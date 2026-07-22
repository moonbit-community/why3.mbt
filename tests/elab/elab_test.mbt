// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn parsed_units(
  source : BytesView,
  filename : BytesView,
) -> Array[@parser.MlwModule] raise {
  guard @parser.parse_mlw_file(source, filename~) is Modules(units) else {
    abort("test input did not parse as named units")
  }
  units
}

///|
fn fresh_environment(
  context : @identity.CompilationContext,
) -> @stdlib.FrozenEnvironment raise {
  @stdlib.minimal_env(context)
}

///|
fn load_fixture(path : String) -> (Bytes, Bytes) raise {
  (@fs.read_file_to_bytes(path), @utf8.encode(path))
}

///|
test "MVP pure theories elaborate against the frozen environment" {
  let (source, filename) = load_fixture("tools/why3_oracle/fixtures/mvp.mlw")
  let context = @identity.CompilationContext::new()
  let frozen = fresh_environment(context)
  let environment = frozen.semantic_environment()
  let units = parsed_units(source[:], filename[:])
  assert_eq(units.length(), 12)
  let theories : Array[@theory.Theory] = []
  for index in 0..<8 {
    let unit = units[index]
    let theory = @why3_elab.elaborate_pure_unit(context, environment, unit) catch {
      _ => fail("pure MVP unit failed at index " + index.to_string())
    }
    environment.register_theory(theory, true, None)
    theories.push(theory)
  }
  assert_eq(theories.length(), 8)
  assert_eq(@theory.split_theory(context, theories[0], None).length(), 3)
  assert_eq(@theory.split_theory(context, theories[2], None).length(), 2)
  assert_eq(@theory.split_theory(context, theories[3], None).length(), 1)
}

///|
fn expect_type_error(
  source : BytesView,
  filename : BytesView,
  expected : @why3_elab.ElabErrorKind,
  start_line : Int64,
  start_column : Int64,
  end_column : Int64,
  expected_actual : Bytes?,
  expected_expected : Bytes?,
) -> Unit raise {
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context).semantic_environment()
  let unit = parsed_units(source, filename)[0]
  try @why3_elab.elaborate_pure_unit(context, environment, unit) catch {
    @why3_elab.ElabError(diagnostic) => {
      assert_eq(diagnostic.kind, expected)
      assert_eq(diagnostic.stage, @why3_elab.PureTyping)
      guard diagnostic.span is Some(span) else {
        fail("typing diagnostic lost its source span")
      }
      let view = span.view()
      assert_eq(view.relative_path, filename.to_owned())
      assert_eq(view.start_line, start_line)
      assert_eq(view.end_line, start_line)
      assert_eq(view.start_column, start_column)
      assert_eq(view.end_column, end_column)
      guard diagnostic.actual_type is Some(actual) &&
        diagnostic.expected_type is Some(expected_type) else {
        fail("typing diagnostic lost its actual/expected types")
      }
      assert_true(!actual.is_empty())
      assert_true(!expected_type.is_empty())
      match expected_actual {
        Some(value) => assert_eq(actual, value)
        None => ()
      }
      match expected_expected {
        Some(value) => assert_eq(expected_type, value)
        None => ()
      }
    }
  } noraise {
    _ => fail("expected a pure typing error")
  }
}

///|
test "pure typing preserves arity mismatch and occurs-check classes" {
  let (arity_source, arity_filename) = load_fixture(
    "tools/why3_oracle/fixtures/typing-arity.mlw",
  )
  expect_type_error(
    arity_source[:],
    arity_filename[:],
    @why3_elab.TypeFailure(ArityMismatch),
    5L,
    15L,
    21L,
    Some(b"int -> int"),
    Some(b"int"),
  )
  let (mismatch_source, mismatch_filename) = load_fixture(
    "tools/why3_oracle/fixtures/typing-mismatch.mlw",
  )
  expect_type_error(
    mismatch_source[:],
    mismatch_filename[:],
    @why3_elab.TypeFailure(TypeMismatch),
    4L,
    18L,
    19L,
    Some(b"int"),
    Some(b"bool"),
  )
  let (occurs_source, occurs_filename) = load_fixture(
    "tools/why3_oracle/fixtures/typing-occurs.mlw",
  )
  expect_type_error(
    occurs_source[:],
    occurs_filename[:],
    @why3_elab.TypeFailure(OccursCheck),
    4L,
    28L,
    29L,
    None,
    None,
  )
}

///|
fn expect_unsupported_before_task(
  source : BytesView,
  filename : BytesView,
  unit_index : Int,
  feature : @why3_elab.UnsupportedFeature,
  start_line : Int64,
  start_column : Int64,
  end_line : Int64,
  end_column : Int64,
) -> Unit raise {
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context).semantic_environment()
  let unit = parsed_units(source, filename)[unit_index]
  try @why3_elab.elaborate_pure_unit(context, environment, unit) catch {
    @why3_elab.ElabError(diagnostic) => {
      assert_eq(diagnostic.kind, @why3_elab.Unsupported(feature))
      assert_eq(diagnostic.stage, @why3_elab.FeatureClassification)
      assert_eq(diagnostic.actual_type, None)
      assert_eq(diagnostic.expected_type, None)
      guard diagnostic.span is Some(span) else {
        fail("unsupported diagnostic lost its source span")
      }
      let view = span.view()
      assert_eq(view.relative_path, filename.to_owned())
      assert_eq(view.start_line, start_line)
      assert_eq(view.start_column, start_column)
      assert_eq(view.end_line, end_line)
      assert_eq(view.end_column, end_column)
    }
  } noraise {
    theory => {
      let task_count = @theory.split_theory(context, theory, None).length()
      fail(
        "unsupported input reached Theory/Task construction (" +
        task_count.to_string() +
        " tasks)",
      )
    }
  }
}

///|
test "unsupported pure features are classified before Task construction" {
  let (lambda_source, lambda_filename) = load_fixture(
    "tools/why3_oracle/fixtures/unsupported/lambda.mlw",
  )
  expect_unsupported_before_task(
    lambda_source[:],
    lambda_filename[:],
    0,
    Lambda,
    4L,
    35L,
    4L,
    53L,
  )
  let (higher_order_source, higher_order_filename) = load_fixture(
    "tools/why3_oracle/fixtures/unsupported/higher-order.mlw",
  )
  expect_unsupported_before_task(
    higher_order_source[:],
    higher_order_filename[:],
    0,
    HigherOrder,
    4L,
    11L,
    4L,
    44L,
  )
  let (datatypes_source, datatypes_filename) = load_fixture(
    "tools/why3_oracle/fixtures/unsupported/datatypes.mlw",
  )
  expect_unsupported_before_task(
    datatypes_source[:],
    datatypes_filename[:],
    0,
    TypeDeclarationShape,
    4L,
    7L,
    4L,
    25L,
  )
  let (control_source, control_filename) = load_fixture(
    "tools/why3_oracle/fixtures/unsupported/control-attribute.mlw",
  )
  expect_unsupported_before_task(
    control_source[:],
    control_filename[:],
    1,
    ControlAttribute,
    8L,
    30L,
    8L,
    48L,
  )
  let (meta_source, meta_filename) = load_fixture(
    "tools/why3_oracle/fixtures/unsupported/meta.mlw",
  )
  expect_unsupported_before_task(
    meta_source[:],
    meta_filename[:],
    0,
    UserMeta,
    7L,
    7L,
    7L,
    15L,
  )
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory RecursiveLogic\n  function loop (x : int) : int = loop x\n  goal unreachable : loop 0 = 0\nend\n",
    b"recursive-logic.mlw",
    0,
    RecursiveOrHigherOrderLogic,
    4L,
    11L,
    4L,
    40L,
  )
}

///|
test "formula and Bool coercions are explicit semantic nodes" {
  let source = b"theory Coercions\n predicate p\n function as_bool : bool = p\n goal as_formula : [@ordinary] as_bool\nend\n"
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context).semantic_environment()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(source, b"coercions.mlw")[0],
  )
  let items = theory.view().items
  guard items[4] is TheoryDecl(logic_declaration) &&
    logic_declaration.view() is Dlogic(definitions) else {
    fail("expected the function definition after the implicit prelude")
  }
  assert_true(definitions[0].view().body.view() is Tif(_, _, _))
  guard items[5] is TheoryDecl(goal) && goal.view() is Dprop(_, _, formula) else {
    fail("expected the coercion goal")
  }
  assert_true(formula.view() is Tapp(_, _, [_, _]))
  assert_true(formula.attributes().any(attribute => attribute == b"ordinary"))
}

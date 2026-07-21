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
test "MVP pure theories elaborate against the frozen environment" {
  let source =
    #|theory LogicCore
    #|  use int.Int
    #|  type u
    #|  constant c : u
    #|  predicate holds (x : u)
    #|  function identity (x : int) : int = x
    #|  predicate nonnegative (x : int) = x >= 0
    #|  axiom c_holds : holds c
    #|  lemma implication_identity : forall x : int. nonnegative x -> nonnegative x
    #|  goal ordinary_attribute : [@ordinary_attribute] true
    #|  goal bool_int_real : let x = identity 1 in if x = 1 then 0 < 1 else false
    #|end
    #|theory LogicReal
    #|  use real.Real
    #|  goal real_order : (0.5 : real) < 1.0
    #|end
    #|theory LogicPolymorphism
    #|  type box 'a
    #|  type wrapped 'a = box 'a
    #|  function identity (x : 'a) : 'a = x
    #|  goal identity_int : identity 0 = 0
    #|  goal identity_bool : identity true = true
    #|end
    #|theory LogicQuantifiers
    #|  use int.Int
    #|  predicate marked (x : int)
    #|  axiom marked_zero : marked 0
    #|  goal quantified_trigger : (forall x : int [marked x]. marked x -> exists y : int. y = x)
    #|end
    #|theory UnitMvp
    #|  constant u : unit
    #|  goal unit_roundtrip : u = ()
    #|end
    #|theory NamespaceMvp
    #|  use int.Int
    #|  scope Inner
    #|    function successor (x : int) : int = x + 1
    #|  end
    #|  goal qualified_lookup : Inner.successor 0 = 1
    #|end
    #|theory MultiFirst
    #|  goal first_goal : true
    #|end
    #|theory MultiSecond
    #|  goal second_goal : true
    #|end
  let context = @identity.CompilationContext::new()
  let frozen = fresh_environment(context)
  let environment = frozen.semantic_environment()
  let units = parsed_units(@utf8.encode(source)[:], b"mvp-pure.mlw")
  assert_eq(units.length(), 8)
  let theories : Array[@theory.Theory] = []
  for index, unit in units {
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
  expect_type_error(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory ArityMismatch\n  function pair (x y : int) : int\n  goal arity : pair 0 = 0\nend\n",
    b"tools/why3_oracle/fixtures/typing-arity.mlw",
    @why3_elab.TypeFailure(ArityMismatch),
    5L,
    15L,
    21L,
    Some(b"int -> int"),
    Some(b"int"),
  )
  expect_type_error(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory TypeMismatch\n  goal mismatch : 0 = true\nend\n",
    b"tools/why3_oracle/fixtures/typing-mismatch.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
    4L,
    18L,
    19L,
    Some(b"int"),
    Some(b"bool"),
  )
  expect_type_error(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory OccursCheck\n  goal occurs : (fun x -> x x) = (fun x -> x x)\nend\n",
    b"tools/why3_oracle/fixtures/typing-occurs.mlw",
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
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory Lambda\n  function identity : int -> int = fun value -> value\n  goal identity_zero : identity 0 = 0\nend\n",
    b"tools/why3_oracle/fixtures/unsupported/lambda.mlw",
    0,
    Lambda,
    4L,
    35L,
    4L,
    53L,
  )
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory HigherOrder\n  constant transformer : (int -> int) -> int\n  constant identity : int -> int\n  goal application : transformer identity = transformer identity\n  goal higher_application : (if true then identity else identity) 0 = 0\nend\n",
    b"tools/why3_oracle/fixtures/unsupported/higher-order.mlw",
    0,
    HigherOrder,
    4L,
    11L,
    4L,
    44L,
  )
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory Datatypes\n  type color = Red | Blue\n  function flip (value : color) : color =\n    match value with\n    | Red -> Blue\n    | Blue -> Red\n    end\n  goal flip_twice : forall value : color. flip (flip value) = value\nend\n",
    b"tools/why3_oracle/fixtures/unsupported/datatypes.mlw",
    0,
    TypeDeclarationShape,
    4L,
    7L,
    4L,
    25L,
  )
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\nmodule ControlAttribute\n  let controlled () : unit = [@vc:sp] ()\nend\n\ntheory UserStopSplit\n  goal rejected_user_origin : [@stop_split] true\nend\n",
    b"tools/why3_oracle/fixtures/unsupported/control-attribute.mlw",
    1,
    ControlAttribute,
    8L,
    30L,
    8L,
    48L,
  )
  expect_unsupported_before_task(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory UserMeta\n  type source\n  type target\n  function convert (x : source) : target\n  meta coercion function convert\nend\n",
    b"tools/why3_oracle/fixtures/unsupported/meta.mlw",
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

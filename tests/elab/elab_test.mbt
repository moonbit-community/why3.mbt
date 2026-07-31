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
) -> @environment.Environment raise {
  @stdlib.embedded_environment_in_context(context)
}

///|
fn load_fixture(path : String) -> (Bytes, Bytes) raise {
  (@fs.read_file_to_bytes(path), @utf8.encode(path))
}

///|
test "MVP pure theories elaborate against the embedded environment" {
  let (source, filename) = load_fixture("tools/why3_reference/fixtures/mvp.mlw")
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
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
  let environment = fresh_environment(context)
  let unit = parsed_units(source, filename)[0]
  try @why3_elab.elaborate_pure_unit(context, environment, unit) catch {
    ElabError(diagnostic) => {
      assert_eq(diagnostic.kind, expected)
      assert_eq(diagnostic.stage, PureTyping)
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
fn expect_plain_type_error(
  source : BytesView,
  filename : BytesView,
  expected : @why3_elab.ElabErrorKind,
  start_line : Int64,
  start_column : Int64,
  end_column : Int64,
) -> Unit raise {
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let unit = parsed_units(source, filename)[0]
  try @why3_elab.elaborate_pure_unit(context, environment, unit) catch {
    @why3_elab.ElabError(diagnostic) => {
      assert_eq(diagnostic.kind, expected)
      assert_eq(diagnostic.stage, @why3_elab.PureTyping)
      assert_eq(diagnostic.actual_type, None)
      assert_eq(diagnostic.expected_type, None)
      guard diagnostic.span is Some(span) else {
        fail("typing diagnostic lost its source span")
      }
      let view = span.view()
      assert_eq(view.relative_path, filename.to_owned())
      assert_eq(view.start_line, start_line)
      assert_eq(view.end_line, start_line)
      assert_eq(view.start_column, start_column)
      assert_eq(view.end_column, end_column)
    }
  } noraise {
    _ => fail("expected a pure typing error")
  }
}

///|
test "pure typing preserves arity mismatch and occurs-check classes" {
  let (arity_source, arity_filename) = load_fixture(
    "tools/why3_reference/fixtures/typing-arity.mlw",
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
    "tools/why3_reference/fixtures/typing-mismatch.mlw",
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
    "tools/why3_reference/fixtures/typing-occurs.mlw",
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
test "whole-file theory diagnostics retain the pure typing stage" {
  let (source, filename) = load_fixture(
    "tools/why3_reference/fixtures/typing-arity.mlw",
  )
  let parsed = @parser.parse_mlw_file(source[:], filename=filename[:])
  let context = @identity.CompilationContext::new()
  try
    @why3_elab.elaborate_file(context, fresh_environment(context), parsed)
  catch {
    @why3_elab.ElabError(diagnostic) => {
      assert_eq(diagnostic.stage, @why3_elab.PureTyping)
      assert_eq(diagnostic.kind, @why3_elab.TypeFailure(ArityMismatch))
    }
    _ => fail("whole-file theory raised another error")
  } noraise {
    _ => fail("expected whole-file pure typing error")
  }
}

///|
test "user control attributes remain semantic task attributes" {
  let (control_source, control_filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/control-attribute.mlw",
  )
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(control_source, control_filename)[1],
  )
  let items = theory.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, formula) else {
    fail("control-attribute fixture lost its goal")
  }
  assert_true(formula.attributes().any(attribute => attribute == b"stop_split"))
  assert_eq(@theory.split_theory(context, theory, None).length(), 1)
}

///|
test "non-terminating pure recursion has a structural type error" {
  expect_plain_type_error(
    b"(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)\n\ntheory RecursiveLogic\n  function loop (x : int) : int = loop x\n  goal unreachable : loop 0 = 0\nend\n",
    b"recursive-logic.mlw",
    TypeFailure(NoTerminationProof),
    4L,
    11L,
    40L,
  )
}

///|
test "formula and Bool coercions are explicit semantic nodes" {
  let source = b"theory Coercions\n predicate p\n function as_bool : bool = p\n goal as_formula : [@ordinary] as_bool\nend\n"
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
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

///|
test "pure case terms elaborate constructor, as, and or-patterns" {
  let source =
    #|theory PureCase
    #|  function invert (value : bool) : bool =
    #|    match value with
    #|    | True -> False
    #|    | False -> True
    #|    end
    #|  function identity (value : bool) : bool =
    #|    match value with
    #|    | (True as found) | (False as found) -> found
    #|    end
    #|  goal invert_true : invert True = False
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"pure-case.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(invert_declaration) &&
    invert_declaration.view() is Dlogic([invert_definition]) &&
    items[4] is TheoryDecl(identity_declaration) &&
    identity_declaration.view() is Dlogic([identity_definition]) else {
    fail("expected the pure case definitions after the implicit prelude")
  }
  guard invert_definition.view().body.view() is Tcase(_, invert_branches) &&
    identity_definition.view().body.view() is Tcase(_, identity_branches) else {
    fail("expected both definitions to retain semantic case nodes")
  }
  assert_eq(invert_branches.length(), 2)
  assert_eq(identity_branches.length(), 1)
  assert_true(identity_branches[0].view().pattern.view() is Por(_, _, _))
  assert_true(identity_branches[0].view().body.view() is Tvar(_))
}

///|
test "pure algebraic datatypes introduce constructors used by case terms" {
  let (source, filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/datatypes.mlw",
  )
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(source[:], filename[:])[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(type_declaration) &&
    type_declaration.view() is Ddata([data]) else {
    fail("expected the source datatype to become a semantic data declaration")
  }
  let data_view = data.view()
  assert_eq(data_view.type_symbol.view().name, b"color")
  assert_eq(data_view.constructors.length(), 2)
  assert_eq(data_view.constructors[0].view().symbol.view().name, b"Red")
  assert_eq(data_view.constructors[1].view().symbol.view().name, b"Blue")
  guard items[4] is TheoryDecl(flip_declaration) &&
    flip_declaration.view() is Dlogic([flip_definition]) &&
    flip_definition.view().body.view() is Tcase(_, branches) else {
    fail("datatype constructors did not remain available to case typing")
  }
  assert_eq(branches.length(), 2)
  assert_true(
    branches[0].view().pattern.view() is Papp(red, [], _) &&
    red == data_view.constructors[0].view().symbol,
  )
}

///|
test "mutually recursive datatypes share one checked declaration group" {
  let source =
    #|theory MutualData
    #|  type even = Zero | EvenSucc odd
    #|  with odd = OddSucc even
    #|  function is_zero (value : even) : bool =
    #|    match value with
    #|    | Zero -> True
    #|    | EvenSucc _ -> False
    #|    end
    #|  goal zero_is_zero : is_zero Zero = True
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"mutual-data.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(type_declaration) &&
    type_declaration.view() is Ddata([even_data, odd_data]) else {
    fail("mutually recursive source types were not kept in one data group")
  }
  let even_view = even_data.view()
  let odd_view = odd_data.view()
  assert_eq(even_view.type_symbol.view().name, b"even")
  assert_eq(odd_view.type_symbol.view().name, b"odd")
  guard even_view.constructors is [_, even_successor] &&
    even_successor.view().symbol.view().argument_types is [odd_argument] &&
    odd_argument.view() is TyApp(odd_symbol, []) else {
    fail("the even constructor lost its reference to odd")
  }
  assert_true(odd_symbol == odd_view.type_symbol)
  guard odd_view.constructors is [odd_successor] &&
    odd_successor.view().symbol.view().argument_types is [even_argument] &&
    even_argument.view() is TyApp(even_symbol, []) else {
    fail("the odd constructor lost its reference to even")
  }
  assert_true(even_symbol == even_view.type_symbol)
  guard items[4] is TheoryDecl(function_declaration) &&
    function_declaration.view() is Dlogic([definition]) &&
    definition.view().body.view() is Tcase(_, branches) else {
    fail("constructors from the recursive group were not exported to typing")
  }
  assert_eq(branches.length(), 2)
}

///|
test "pure inductive declarations type cases against their pending predicates" {
  let source =
    #|theory PureInductive
    #|  inductive reachable (value : bool) =
    #|    | reachable_true : reachable True
    #|    | reachable_false : reachable True -> reachable False
    #|  goal false_is_reachable : reachable False
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"pure-inductive.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(inductive_declaration) &&
    inductive_declaration.view() is Dind(Ind, [reachable]) else {
    fail("source inductive did not become a semantic inductive declaration")
  }
  let reachable_view = reachable.view()
  assert_eq(reachable_view.predicate.view().name, b"reachable")
  assert_eq(reachable_view.cases.length(), 2)
  assert_eq(
    reachable_view.cases[0].view().proposition.view().name,
    b"reachable_true",
  )
  assert_true(
    reachable_view.cases[0].view().formula.view() is Tapp(predicate, _, [_]) &&
    predicate == reachable_view.predicate,
  )
  assert_true(
    reachable_view.cases[1].view().formula.view() is Tbinop(Implies, _, _),
  )
  guard items[4] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, formula) &&
    formula.view() is Tapp(predicate, _, [_]) else {
    fail("the inductive predicate was not exported to following declarations")
  }
  assert_true(predicate == reachable_view.predicate)
}

///|
test "user coercion meta updates the semantic coercion closure" {
  let (source, filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/meta.mlw",
  )
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(source[:], filename[:])[0],
  )
  let exports = theory.export_namespace()
  let source_symbol = exports.find_type([b"source"], None)
  let target_symbol = exports.find_type([b"target"], None)
  let convert = exports.find_logic([b"convert"], None)
  let path = theory
    .coercions()
    .find(
      @logic.Ty::app(source_symbol, [], None),
      @logic.Ty::app(target_symbol, [], None),
      None,
    )
  assert_true(path is [registered] && registered == convert)
  assert_true(
    theory.view().items.any(item => {
      item is TheoryMeta(meta) &&
      meta.view().name == b"coercion" &&
      meta.view().arguments is [MetaLogicSymbol(symbol)] &&
      symbol == convert
    }),
  )
}

///|
test "pure conditional branches use the maximal coercible type" {
  let source =
    #|theory ConditionalCoercion
    #|  type source
    #|  type target
    #|  function convert (value : source) : target
    #|  meta coercion function convert
    #|  function value : source
    #|  function choose (flag : bool) : target =
    #|    if flag then value else convert value
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"conditional-coercion.mlw")[0],
  )
  let convert = theory.export_namespace().find_logic([b"convert"], None)
  let mut saw_coerced_branch = false
  for item in theory.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dlogic([definition]) &&
      definition.view().symbol.view().name == b"choose" &&
      definition.view().body.view() is Tif(_, then_branch, _) &&
      then_branch.view() is Tapp(symbol, _, [_]) {
      saw_coerced_branch = symbol == convert
    }
  }
  assert_true(saw_coerced_branch)
}

///|
test "function application follows coercions into HighOrd arrows" {
  let source =
    #|theory CoercedFunctionApplication
    #|  type box 'a
    #|  function contents (value : box 'a) : int -> 'a
    #|  meta coercion function contents
    #|  function read (value : box int) : int = value 0
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"coerced-function-application.mlw")[0],
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("coerced function application failed")
    }
    _ => fail("coerced function application raised another error")
  }
  assert_true(
    theory.export_namespace().find_logic([b"read"], None).view().result_type
    is Some(_),
  )
}

///|
test "pure clone substitutions retain exact type and logic witnesses" {
  let (source, filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/clone.mlw",
  )
  let units = parsed_units(source[:], filename[:])
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let base = @why3_elab.elaborate_pure_unit(context, environment, units[0])
  environment.register_theory(base, true, None)
  let source_type = base.export_namespace().find_type([b"t"], None)
  let source_function = base.export_namespace().find_logic([b"f"], None)
  let use_theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    units[1],
  )
  let target_type = use_theory.export_namespace().find_type([b"u"], None)
  let target_function = use_theory.export_namespace().find_logic([b"g"], None)
  guard use_theory.view().items.last() is Some(TheoryClone(witness)) else {
    fail("source clone did not append a semantic clone witness")
  }
  let witness_view = witness.view()
  assert_true(
    witness_view.type_instantiations is [CloneTypeSymbol(source, target)] &&
    source == source_type &&
    target == target_type,
  )
  assert_true(
    witness_view.logic_instantiations is [(source, target)] &&
    source == source_function &&
    target == target_function,
  )
}

///|
test "internal epsilon terms finalize with a bound semantic witness" {
  let source = b"theory PureEpsilon\n  goal witness : 0 = 0\nend\n"
  let parsed = parsed_units(source, b"pure-epsilon.mlw")[0]
  guard parsed.declarations
    is [Dprop(kind, goal_name, { desc: Tinfix(zero, equality, _), span })] else {
    fail("epsilon test skeleton did not retain its equality term")
  }
  let witness = @parser.Ident::{ name: b"x", attributes: [], span: zero.span }
  let witness_term = @parser.Term::{
    desc: Tident(Qident(witness)),
    span: zero.span,
  }
  let predicate = @parser.Term::{
    desc: Tinfix(witness_term, equality, witness_term),
    span,
  }
  let int_name = @parser.Ident::{
    name: b"int",
    attributes: [],
    span: zero.span,
  }
  let epsilon = @parser.Term::{
    desc: Teps(witness, PTtyapp(Qident(int_name), []), predicate),
    span,
  }
  let unit = @parser.MlwModule::{
    ..parsed,
    declarations: [
      Dprop(kind, goal_name, @parser.Term::{
        desc: Tinfix(epsilon, equality, zero),
        span,
      }),
    ],
  }
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    unit,
  )
  guard theory.view().items[3] is TheoryDecl(declaration) &&
    declaration.view() is Dprop(_, _, formula) &&
    formula.view() is Tapp(_, _, [left, _]) else {
    fail("expected an equality goal containing epsilon")
  }
  assert_true(left.view() is Teps(_, _))
}

///|
test "source records drive construction, update, and pattern layout" {
  let source =
    #|theory SourceRecords
    #|  type pair = { first : int; second : int }
    #|  function make (x : int) (y : int) : pair =
    #|    { second = y; first = x }
    #|  function replace_first (value : pair) (x : int) : pair =
    #|    { value with first = x }
    #|  function get_first (value : pair) : int =
    #|    match value with
    #|    | { first = x } -> x
    #|    end
    #|  goal layout : get_first (make 1 2) = 1
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"source-records.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(type_declaration) &&
    type_declaration.view() is Ddata([data]) &&
    data.view().constructors is [record_constructor] else {
    fail("source record did not become a single-constructor data declaration")
  }
  let constructor_view = record_constructor.view()
  assert_eq(constructor_view.symbol.view().name, b"pair'mk")
  guard constructor_view.projections is [Some(first), Some(second)] else {
    fail("source record lost its ordered projections")
  }
  assert_eq(first.view().name, b"first")
  assert_eq(second.view().name, b"second")
  guard items[4] is TheoryDecl(make_declaration) &&
    make_declaration.view() is Dlogic([make_definition]) &&
    make_definition.view().body.view()
    is Tapp(make_symbol, _, [first_value, second_value]) else {
    fail("source record construction did not use declaration order")
  }
  assert_true(make_symbol == constructor_view.symbol)
  assert_true(first_value.view() is Tvar(_))
  assert_true(second_value.view() is Tvar(_))
  guard items[5] is TheoryDecl(update_declaration) &&
    update_declaration.view() is Dlogic([update_definition]) &&
    update_definition.view().body.view()
    is Tapp(update_symbol, _, [_, retained]) else {
    fail("source record update did not rebuild its unique constructor")
  }
  assert_true(update_symbol == constructor_view.symbol)
  assert_true(
    retained.view() is Tapp(projection, _, [_]) && projection == second,
  )
  guard items[6] is TheoryDecl(pattern_declaration) &&
    pattern_declaration.view() is Dlogic([pattern_definition]) &&
    pattern_definition.view().body.view() is Tcase(_, [branch]) &&
    branch.view().pattern.view() is Papp(pattern_symbol, [bound, omitted], _) else {
    fail("source record pattern did not lower through its constructor")
  }
  assert_true(pattern_symbol == constructor_view.symbol)
  assert_true(bound.view() is Pvar(_))
  assert_true(omitted.view() is Pwild(_))
}

///|
test "pure range and float declarations type exact annotated literals" {
  let source =
    #|theory ExactLiteralTypes
    #|  type byte = < range -128 127 >
    #|  type binary32 = < float 8 24 >
    #|  function answer : byte = (42 : byte)
    #|  function eighth : binary32 = (0.125 : binary32)
    #|  goal answer_is_exact : answer = (42 : byte)
    #|  goal eighth_is_exact : eighth = (0.125 : binary32)
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"exact-literal-types.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(range_declaration) &&
    range_declaration.view() is Dtype([range_symbol]) &&
    range_symbol.view().definition is Range(lower, upper) else {
    fail("range source declaration lost its exact bounds")
  }
  assert_eq(lower, BigInt::from_int(-128))
  assert_eq(upper, BigInt::from_int(127))
  guard items[9] is TheoryDecl(float_declaration) &&
    float_declaration.view() is Dtype([float_symbol]) else {
    fail("float source declaration did not become a semantic type")
  }
  assert_true(float_symbol.view().definition is Float(8, 24))
  guard items[16] is TheoryDecl(answer_declaration) &&
    answer_declaration.view() is Dlogic([answer_definition]) &&
    answer_definition.view().body.view() is Tconst(_) &&
    answer_definition.view().body.ty() is Some(answer_type) &&
    answer_type.view() is TyApp(answer_symbol, []) else {
    fail("annotated range literal did not retain its target type")
  }
  assert_true(answer_symbol == range_symbol)
  guard items[17] is TheoryDecl(eighth_declaration) &&
    eighth_declaration.view() is Dlogic([eighth_definition]) &&
    eighth_definition.view().body.view() is Tconst(_) &&
    eighth_definition.view().body.ty() is Some(eighth_type) &&
    eighth_type.view() is TyApp(eighth_symbol, []) else {
    fail("annotated float literal did not retain its target type")
  }
  assert_true(eighth_symbol == float_symbol)
}

///|
fn register_record_fixture(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
) -> (@logic.LSymbol, @logic.LSymbol, @logic.LSymbol) raise {
  let origin = fn(name : BytesView) { @identity.Origin::user(name, None, []) }
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"RecordFixture"),
    @theory.SemanticName::new(b"RecordFixture", [], None),
  )
  let builtin = environment.resolve_theory(
    @theory.TheoryKey::new([], b"BuiltIn"),
    None,
  )
  builder.add_use(builtin, true, None)
  let integer = builtin.export_namespace().find_type([b"int"], None)
  let integer_type = @logic.Ty::app(integer, [], None)
  let pair = @logic.TypeSymbol::new_abstract(
    context,
    b"pair",
    origin(b"pair"),
    [],
    None,
  )
  let pair_type = @logic.Ty::app(pair, [], None)
  let make_pair = @logic.LSymbol::new_constructor(
    context,
    b"Pair",
    origin(b"Pair"),
    [integer_type, integer_type],
    pair_type,
    1,
    None,
  )
  let first = @logic.LSymbol::new_projection(
    context,
    b"first",
    origin(b"first"),
    pair_type,
    integer_type,
    None,
  )
  let second = @logic.LSymbol::new_projection(
    context,
    b"second",
    origin(b"second"),
    pair_type,
    integer_type,
    None,
  )
  let data = @logic.DataDeclaration::new(
    pair,
    [@logic.DataConstructor::new(make_pair, [Some(first), Some(second)], None)],
    None,
  )
  builder.add_decl(
    @logic.Decl::data(context, origin(b"pair"), [data], None),
    None,
  )
  environment.register_theory(builder.close(), true, None)
  (make_pair, first, second)
}

///|
test "pure record construction, update, and patterns use declaration layout" {
  let source =
    #|theory PureRecords
    #|  use RecordFixture
    #|  function make (x : int) (y : int) : pair =
    #|    { second = y; first = x }
    #|  function replace_first (value : pair) (x : int) : pair =
    #|    { value with first = x }
    #|  function get_first (value : pair) : int =
    #|    match value with
    #|    | { first = x } -> x
    #|    end
    #|  goal layout : get_first (make 1 2) = 1
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let (make_pair, first, second) = register_record_fixture(context, environment)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"pure-records.mlw")[0],
  )
  let items = theory.view().items
  guard items[4] is TheoryDecl(make_declaration) &&
    make_declaration.view() is Dlogic([make_definition]) &&
    make_definition.view().body.view()
    is Tapp(make_symbol, _, [first_value, second_value]) else {
    fail("record construction did not lower to its unique constructor")
  }
  assert_true(make_symbol == make_pair)
  assert_true(first_value.view() is Tvar(_))
  assert_true(second_value.view() is Tvar(_))
  guard items[5] is TheoryDecl(update_declaration) &&
    update_declaration.view() is Dlogic([update_definition]) &&
    update_definition.view().body.view()
    is Tapp(update_symbol, _, [_, retained]) else {
    fail("record update did not rebuild its unique constructor")
  }
  assert_true(update_symbol == make_pair)
  assert_true(
    retained.view() is Tapp(projection, _, [_]) && projection == second,
  )
  guard items[6] is TheoryDecl(pattern_declaration) &&
    pattern_declaration.view() is Dlogic([pattern_definition]) &&
    pattern_definition.view().body.view() is Tcase(_, [branch]) &&
    branch.view().pattern.view() is Papp(pattern_symbol, [bound, omitted], _) else {
    fail("record pattern did not lower through the record constructor")
  }
  assert_true(pattern_symbol == make_pair)
  assert_true(bound.view() is Pvar(_))
  assert_true(omitted.view() is Pwild(_))
  ignore(first)
}

///|
test "string constants and proof-control connectives retain Why3 semantics" {
  let source =
    #|theory PureControls
    #|  function text : string = "why3"
    #|  goal text_roundtrip : text = "why3"
    #|  goal by_control : true by true
    #|  goal so_control : true so true
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(@utf8.encode(source), b"pure-controls.mlw")[0],
  )
  let items = theory.view().items
  guard items[3] is TheoryDecl(text_declaration) &&
    text_declaration.view() is Dlogic([text_definition]) &&
    text_definition.view().body.view() is Tconst(ConstStr(value)) else {
    fail("string definition did not retain its literal node")
  }
  assert_eq(value, b"why3")
  guard items[5] is TheoryDecl(by_declaration) &&
    by_declaration.view() is Dprop(_, _, by_formula) &&
    by_formula.view() is Tbinop(Implies, by_guard, _) &&
    by_guard.view() is Tbinop(Or, by_evidence, _) else {
    fail("`by` did not lower to the guarded implication")
  }
  assert_true(
    by_evidence.attributes().any(attribute => attribute == b"asym_split"),
  )
  guard items[6] is TheoryDecl(so_declaration) &&
    so_declaration.view() is Dprop(_, _, so_formula) &&
    so_formula.view() is Tbinop(And, _, so_guard) &&
    so_guard.view() is Tbinop(Or, so_evidence, _) else {
    fail("`so` did not lower to the guarded conjunction")
  }
  assert_true(
    so_evidence.attributes().any(attribute => attribute == b"asym_split"),
  )
}

///|
test "tuple syntax loads its builtin family and elaborates types terms and patterns" {
  let source =
    #|theory PureTuples
    #|  function first (value : (int, bool)) : int =
    #|    match value with
    #|    | (selected, _) -> selected
    #|    end
    #|  goal tuple_value : first (1, true) = 1
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"pure-tuples.mlw")[0],
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("pure tuple elaboration failed")
    }
    _ => fail("pure tuple elaboration raised another error")
  }
  let tuple_module = environment.tuple_module(2)
  assert_true(
    tuple_module.key() ==
    @theory.TheoryKey::new([b"why3", b"Tuple2"], b"Tuple2"),
  )
  assert_true(
    theory.view().items.any(item => {
      item is TheoryUse(key) && key == tuple_module.pure_theory().key()
    }),
  )
  let mut saw_pattern = false
  let mut saw_value = false
  for item in theory.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dlogic([definition]) {
      match definition.view().body.view() {
        Tcase(_, [branch]) =>
          if branch.view().pattern.view() is Papp(symbol, [_, _], _) {
            saw_pattern = symbol.view().name == b"Tuple2"
          }
        Tapp(symbol, _, [_, _]) =>
          if symbol.view().name == b"Tuple2" {
            saw_value = true
          }
        _ => ()
      }
    }
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dprop(_, _, formula) &&
      formula.view() is Tapp(_, _, [left, _]) &&
      left.view() is Tapp(_, _, [tuple_value]) &&
      tuple_value.view() is Tapp(symbol, _, [_, _]) {
      saw_value = symbol.view().name == b"Tuple2"
    }
  }
  assert_true(saw_pattern)
  assert_true(saw_value)
}

///|
test "higher-order pure types and applications use the synthesized HighOrd theory" {
  let source =
    #|theory HigherOrderApply
    #|  function apply (f : 'a -> 'b) (x : 'a) : 'b = f x
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"higher-order-apply.mlw")[0],
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("higher-order pure elaboration failed")
    }
    _ => fail("higher-order pure elaboration raised another error")
  }
  let high_order = environment.high_order_module()
  assert_true(
    theory.view().items.any(item => {
      item is TheoryUse(key) && key == high_order.pure_theory().key()
    }),
  )
  let mut saw_application = false
  for item in theory.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dlogic([definition]) &&
      definition.view().body.view() is Tapp(symbol, _, [_, _]) {
      saw_application = symbol.view().name == b"infix @"
    }
  }
  assert_true(saw_application)

  let (fixture_source, fixture_filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/higher-order.mlw",
  )
  ignore(
    @why3_elab.elaborate_pure_unit(
      context,
      environment,
      parsed_units(fixture_source[:], fixture_filename[:])[0],
    ) catch {
      @why3_elab.ElabError(diagnostic) => {
        debug_inspect(diagnostic)
        fail("higher-order fixture elaboration failed")
      }
      _ => fail("higher-order fixture raised another error")
    },
  )
}

///|
test "higher-order overapplication preserves every application-prefix span" {
  let source =
    #|theory HigherOrderApplicationSpans
    #|  function producer (seed : int) : int -> int
    #|  function value : int = producer 0 1
    #|end
  let context = @identity.CompilationContext::new()
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    fresh_environment(context),
    parsed_units(
      @utf8.encode(source),
      b"higher-order-application-spans.mlw",
    )[0],
  )
  let mut checked = false
  for item in theory.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dlogic([definition]) &&
      definition.view().symbol.view().name == b"value" &&
      definition.view().body is body &&
      body.view() is Tapp(application, _, [direct, _]) &&
      application.view().name == b"infix @" &&
      direct.view() is Tapp(producer, _, [_]) &&
      producer.view().name == b"producer" {
      guard body.source_span() is Some(outer_span) &&
        direct.source_span() is Some(direct_span) else {
        fail("higher-order application lost its source spans")
      }
      let outer = outer_span.view()
      let inner = direct_span.view()
      assert_eq(inner.start_byte, outer.start_byte)
      assert_eq(inner.start_column, outer.start_column)
      assert_eq(inner.end_byte + 2, outer.end_byte)
      assert_eq(inner.end_column + 2L, outer.end_column)
      checked = true
    }
  }
  assert_true(checked)
}

///|
test "unapplied function-typed parameters do not export hidden HighOrd names" {
  let source =
    #|theory HiddenHighOrderDependency
    #|  use bool.Bool
    #|  use map.Map as IdMap
    #|  type idmap 'a = IdMap.map int 'a
    #|  function keep (values : idmap bool) (value : bool) : bool =
    #|    notb value
    #|end
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(@utf8.encode(source), b"hidden-high-order.mlw")[0],
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("hidden higher-order dependency failed")
    }
    _ => fail("hidden higher-order dependency raised another error")
  }
  let arrow_exported = try {
    ignore(theory.export_namespace().find_type([b"infix ->"], None))
    true
  } catch {
    _ => false
  }
  let application_exported = try {
    ignore(theory.export_namespace().find_logic([b"infix @"], None))
    true
  } catch {
    _ => false
  }
  assert_false(arrow_exported)
  assert_false(application_exported)
}

///|
test "pure lambdas lower to epsilon-defined HighOrd values" {
  let (source, filename) = load_fixture(
    "tools/why3_reference/fixtures/exact/lambda.mlw",
  )
  let context = @identity.CompilationContext::new()
  let environment = fresh_environment(context)
  let theory = @why3_elab.elaborate_pure_unit(
    context,
    environment,
    parsed_units(source[:], filename[:])[0],
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("pure lambda elaboration failed")
    }
    _ => fail("pure lambda elaboration raised another error")
  }
  let mut saw_lambda = false
  for item in theory.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dlogic([definition]) &&
      definition.view().body.view() is Teps(closure, quantified) &&
      closure.ty().view() is TyApp(function_type, [_, _]) &&
      function_type.view().name == b"infix ->" &&
      quantified.view() is Tquant(ForallQuantifier, [_], _, defining_formula) &&
      defining_formula.view() is Tapp(_, _, [applied, _]) &&
      applied.view() is Tapp(application, _, [_, _]) {
      saw_lambda = application.view().name == b"infix @"
    }
  }
  assert_true(saw_lambda)
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "projection axioms receive independent binder identities" {
  let context = @identity.CompilationContext::new()
  let origin = fn(name : BytesView) { @identity.Origin::user(name, None, []) }
  let integer_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"int",
    origin(b"int"),
    [],
    None,
  )
  let integer_type = @logic.Ty::app(integer_symbol, [], None)
  let pair_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"pair",
    origin(b"pair"),
    [],
    None,
  )
  let pair_type = @logic.Ty::app(pair_symbol, [], None)
  let constructor = @logic.LSymbol::new_constructor(
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
  let data_constructor = @logic.DataConstructor::new(
    constructor,
    [Some(first), Some(second)],
    None,
  )
  let type_variable = @logic.TyVarSymbol::new(context, b"a", origin(b"a"))
  let variable_type = @logic.Ty::variable(type_variable)
  let equality = @logic.LSymbol::new_predicate(
    context,
    b"infix =",
    origin(b"infix ="),
    [variable_type, variable_type],
    None,
  )
  let state : AlgebraicState = {
    context,
    known: @logic.KnownMap::new(context),
    equality,
    integer_type,
    options: {
      keep_enums: false,
      keep_records: false,
      keep_monomorphic: false,
      no_index: false,
      no_inversion: false,
      no_selector: false,
    },
    selectors: Map([]),
    constructors: Map([]),
    constructor_projections: Map([]),
    projections: Map([]),
    kept: Map([]),
    kept_order: [],
    infinite: Map([]),
    material: Map([]),
  }
  state.constructors[constructor] = ordinary_clone(state, constructor)
  let output : Array[@theory.TheoryItem] = []
  add_projections(state, pair_type, [data_constructor], output)
  let binder_groups : Array[Array[@logic.VSymbol]] = []
  for item in output {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dprop(Paxiom, _, formula) &&
      formula.view() is Tquant(ForallQuantifier, binders, _, _) {
      binder_groups.push(binders.to_owned())
    }
  }
  assert_eq(binder_groups.length(), 2)
  assert_eq(binder_groups[0].length(), 2)
  assert_eq(binder_groups[1].length(), 2)
  assert_true(
    binder_groups[0][0].identifier_id() != binder_groups[1][0].identifier_id(),
  )
  assert_true(
    binder_groups[0][1].identifier_id() != binder_groups[1][1].identifier_id(),
  )
}

///|
test "encoded polymorphic projections infer their instantiated result" {
  let context = @identity.CompilationContext::new()
  let origin = fn(name : BytesView) { @identity.Origin::user(name, None, []) }
  let first_parameter = @logic.TyVarSymbol::new(context, b"a", origin(b"a"))
  let second_parameter = @logic.TyVarSymbol::new(context, b"b", origin(b"b"))
  let tuple_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tuple2",
    origin(b"tuple2"),
    [first_parameter, second_parameter],
    None,
  )
  let formal_tuple = @logic.Ty::app(
    tuple_symbol,
    [
      @logic.Ty::variable(first_parameter),
      @logic.Ty::variable(second_parameter),
    ],
    None,
  )
  let projection = @logic.LSymbol::new_projection(
    context,
    b"Tuple2_proj_1",
    origin(b"Tuple2_proj_1"),
    formal_tuple,
    @logic.Ty::variable(first_parameter),
    None,
  )
  let element_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    origin(b"t"),
    [],
    None,
  )
  let element_type = @logic.Ty::app(element_symbol, [], None)
  let outer_parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    origin(b"outer_a"),
  )
  let actual_tuple = @logic.Ty::app(
    tuple_symbol,
    [element_type, @logic.Ty::variable(outer_parameter)],
    None,
  )
  let value = @logic.VSymbol::new(
    context,
    b"value",
    origin(b"value"),
    actual_tuple,
    None,
  )
  let projected = algebraic_projection_term(
    projection,
    @logic.Term::variable(value),
  )
  assert_true(projected.ty() is Some(result) && result == element_type)
}

///|
test "algebraic kept instances follow type allocation order" {
  let context = @identity.CompilationContext::new()
  let origin = fn(name : BytesView) { @identity.Origin::user(name, None, []) }
  let lower_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"lower",
    origin(b"lower"),
    [],
    None,
  )
  let higher_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"higher",
    origin(b"higher"),
    [],
    None,
  )
  let parameter = @logic.TyVarSymbol::new(context, b"a", origin(b"a"))
  let option_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"option",
    origin(b"option"),
    [parameter],
    None,
  )
  let higher = @logic.Ty::app(higher_symbol, [], None)
  let earlier = @logic.Ty::app(option_symbol, [higher], None)
  let lower = @logic.Ty::app(lower_symbol, [], None)
  let later = @logic.Ty::app(option_symbol, [lower], None)
  assert_true(earlier.allocation_order() < later.allocation_order())
  assert_true(compare_algebraic_kept_type(earlier, later) < 0)
}

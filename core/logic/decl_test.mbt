// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn decl_test_span() -> @identity.SourceSpan {
  @identity.SourceSpan::new(b"decl.mlw", 3, 12, 1L, 3L, 1L, 12L)
}

///|
fn decl_user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, Some(decl_test_span()), [])
}

///|
fn decl_snapshot_origin(
  name : BytesView,
  kind : @identity.SnapshotSymbolKind,
  ordinal : UInt,
) -> @identity.Origin {
  @identity.Origin::snapshot(
    name,
    @identity.SnapshotSymbolKey::new(
      b"why3.DeclTest",
      ordinal,
      0U,
      kind,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
fn decl_integer_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @logic.Ty) raise @logic.TypeError {
  let symbol = @logic.TypeSymbol::trusted_builtin(
    context,
    b"int",
    decl_snapshot_origin(b"int", Type, 0U),
    BuiltinInteger,
    Some(decl_test_span()),
  )
  (symbol, @logic.Ty::app(symbol, [], Some(decl_test_span())))
}

///|
test "KnownMap rejects future dependencies and accepts declaration order" {
  let context = @identity.CompilationContext::new()
  let (integer_symbol, integer) = decl_integer_type(context)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"positive",
    decl_user_origin(b"positive"),
    [integer],
    Some(decl_test_span()),
  )
  let parameter_decl = @logic.Decl::parameter(
    context,
    decl_user_origin(b"positive"),
    predicate,
    Some(decl_test_span()),
  )
  let known = @logic.KnownMap::new(context)
  try known.add(parameter_decl, Some(decl_test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, UnknownDependency)
  } noraise {
    _ => fail("expected future dependency rejection")
  }
  let type_decl = @logic.Decl::type_declaration(
    context,
    decl_snapshot_origin(b"int", Type, 0U),
    [integer_symbol],
    Some(decl_test_span()),
  )
  let known = known.add(type_decl, Some(decl_test_span()))
  let known = known.add(parameter_decl, Some(decl_test_span()))
  assert_true(known.contains(LogicDependency(predicate)))
  try known.add(parameter_decl, Some(decl_test_span())) catch {
    TypeError(diagnostic) =>
      assert_eq(diagnostic.kind, DuplicateDeclarationSymbol)
  } noraise {
    _ => fail("expected duplicate declaration rejection")
  }
}

///|
test "logic definitions are closed non-recursive and signature exact" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = decl_integer_type(context)
  let function = @logic.LSymbol::new_function(
    context,
    b"identity",
    decl_user_origin(b"identity"),
    [integer],
    integer,
    Some(decl_test_span()),
  )
  let parameter = @logic.VSymbol::new(
    context,
    b"x",
    decl_user_origin(b"x"),
    integer,
    Some(decl_test_span()),
  )
  let definition = @logic.LogicDefinition::new(
    context,
    function,
    [parameter],
    @logic.Term::variable(parameter),
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::logic(
    context,
    decl_user_origin(b"identity"),
    [definition],
    Some(decl_test_span()),
  )
  assert_true(declaration.view() is Dlogic(_))
  let recursive_body = @logic.Term::apply_function(
    function,
    [@logic.Term::variable(parameter)],
    Some(decl_test_span()),
  )
  try
    @logic.LogicDefinition::new(
      context,
      function,
      [parameter],
      recursive_body,
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, CyclicDefinition)
  } noraise {
    _ => fail("expected recursive definition rejection")
  }
  let unbound = @logic.VSymbol::new(
    context,
    b"y",
    decl_user_origin(b"y"),
    integer,
    Some(decl_test_span()),
  )
  try
    @logic.LogicDefinition::new(
      context,
      function,
      [parameter],
      @logic.Term::variable(unbound),
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, UnboundVariable)
  } noraise {
    _ => fail("expected unbound definition variable")
  }
}

///|
test "user logic declaration rejects mutual recursion" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = decl_integer_type(context)
  let left_symbol = @logic.LSymbol::new_function(
    context,
    b"left",
    decl_user_origin(b"left"),
    [integer],
    integer,
    Some(decl_test_span()),
  )
  let right_symbol = @logic.LSymbol::new_function(
    context,
    b"right",
    decl_user_origin(b"right"),
    [integer],
    integer,
    Some(decl_test_span()),
  )
  let left_parameter = @logic.VSymbol::new(
    context,
    b"x",
    decl_user_origin(b"x"),
    integer,
    Some(decl_test_span()),
  )
  let right_parameter = @logic.VSymbol::new(
    context,
    b"y",
    decl_user_origin(b"y"),
    integer,
    Some(decl_test_span()),
  )
  let left_definition = @logic.LogicDefinition::new(
    context,
    left_symbol,
    [left_parameter],
    @logic.Term::apply_function(
      right_symbol,
      [@logic.Term::variable(left_parameter)],
      Some(decl_test_span()),
    ),
    Some(decl_test_span()),
  )
  let right_definition = @logic.LogicDefinition::new(
    context,
    right_symbol,
    [right_parameter],
    @logic.Term::apply_function(
      left_symbol,
      [@logic.Term::variable(right_parameter)],
      Some(decl_test_span()),
    ),
    Some(decl_test_span()),
  )
  try
    @logic.Decl::logic(
      context,
      decl_user_origin(b"mutual"),
      [left_definition, right_definition],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, CyclicDefinition)
  } noraise {
    _ => fail("expected mutual recursion rejection")
  }
}

///|
test "lemma and goal declarations require closed formulas" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = decl_integer_type(context)
  let proposition = @logic.PrSymbol::new(
    context,
    b"goal",
    decl_user_origin(b"goal"),
  )
  let value_variable = @logic.VSymbol::new(
    context,
    b"x",
    decl_user_origin(b"x"),
    integer,
    Some(decl_test_span()),
  )
  try
    @logic.Decl::proposition(
      context,
      decl_user_origin(b"bad"),
      Plemma,
      proposition,
      @logic.Term::variable(value_variable),
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, FormulaExpected)
  } noraise {
    _ => fail("expected value proposition rejection")
  }
  let nullary_predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    decl_user_origin(b"p"),
    [],
    Some(decl_test_span()),
  )
  let formula = @logic.Term::apply_predicate(
    nullary_predicate,
    [],
    Some(decl_test_span()),
  )
  let goal = @logic.Decl::proposition(
    context,
    decl_user_origin(b"goal"),
    Pgoal,
    proposition,
    formula,
    Some(decl_test_span()),
  )
  assert_true(goal.view() is Dprop(Pgoal, _, _))
  let free_predicate = @logic.LSymbol::new_predicate(
    context,
    b"q",
    decl_user_origin(b"q"),
    [integer],
    Some(decl_test_span()),
  )
  let open_formula = @logic.Term::apply_predicate(
    free_predicate,
    [@logic.Term::variable(value_variable)],
    Some(decl_test_span()),
  )
  try
    @logic.Decl::proposition(
      context,
      decl_user_origin(b"open"),
      Paxiom,
      @logic.PrSymbol::new(context, b"open", decl_user_origin(b"open")),
      open_formula,
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, UnboundVariable)
  } noraise {
    _ => fail("expected open proposition rejection")
  }
}

///|
test "trusted Ddata is validated and user Dtype rejects Range" {
  let context = @identity.CompilationContext::new()
  let unit_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"unit",
    decl_snapshot_origin(b"unit", Type, 0U),
    [],
    Some(decl_test_span()),
  )
  let unit_type = @logic.Ty::app(unit_symbol, [], Some(decl_test_span()))
  let unit_constructor = @logic.LSymbol::trusted_constructor(
    context,
    b"Tuple0",
    decl_snapshot_origin(b"Tuple0", Logic, 0U),
    [],
    unit_type,
    1,
    Some(decl_test_span()),
  )
  let data_constructor = @logic.DataConstructor::trusted_new(
    unit_constructor,
    [],
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::trusted_new(
    unit_symbol,
    [data_constructor],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::trusted_data(
    context,
    decl_snapshot_origin(b"unit", Type, 0U),
    [data],
    Some(decl_test_span()),
  )
  assert_true(declaration.view() is Ddata(_))
  let known = @logic.KnownMap::new(context).add(
    declaration,
    Some(decl_test_span()),
  )
  assert_true(known.contains(TypeDependency(unit_symbol)))
  assert_true(known.contains(LogicDependency(unit_constructor)))
  let range_symbol = @logic.TypeSymbol::trusted_range(
    context,
    b"range",
    decl_snapshot_origin(b"range", Type, 1U),
    BigInt::from_int(0),
    BigInt::from_int(10),
    Some(decl_test_span()),
  )
  try
    @logic.Decl::type_declaration(
      context,
      decl_user_origin(b"range"),
      [range_symbol],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, InvalidDeclaration)
  } noraise {
    _ => fail("expected user Range declaration rejection")
  }
}

///|
test "trusted logic declarations reject user-origin definitions" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = decl_integer_type(context)
  let symbol = @logic.LSymbol::new_function(
    context,
    b"f",
    decl_user_origin(b"f"),
    [integer],
    integer,
    Some(decl_test_span()),
  )
  let parameter = @logic.VSymbol::new(
    context,
    b"x",
    decl_user_origin(b"x"),
    integer,
    Some(decl_test_span()),
  )
  let definition = @logic.LogicDefinition::new(
    context,
    symbol,
    [parameter],
    @logic.Term::variable(parameter),
    Some(decl_test_span()),
  )
  try
    @logic.Decl::trusted_logic(
      context,
      decl_snapshot_origin(b"logic", Logic, 10U),
      [definition],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, SnapshotOriginRequired)
  } noraise {
    _ => fail("expected trusted logic origin rejection")
  }
}

///|
test "trusted Ddata rejects nested recursive occurrences" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    decl_snapshot_origin(b"a", Type, 20U),
  )
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    decl_snapshot_origin(b"tree", Type, 21U),
    [parameter],
    Some(decl_test_span()),
  )
  let tree_a = @logic.Ty::app(
    tree_symbol,
    [@logic.Ty::variable(parameter)],
    Some(decl_test_span()),
  )
  let nested_tree = @logic.Ty::app(
    tree_symbol,
    [tree_a],
    Some(decl_test_span()),
  )
  let constructor_symbol = @logic.LSymbol::trusted_constructor(
    context,
    b"Nested",
    decl_snapshot_origin(b"Nested", Logic, 22U),
    [nested_tree],
    tree_a,
    1,
    Some(decl_test_span()),
  )
  let data_constructor = @logic.DataConstructor::trusted_new(
    constructor_symbol,
    [None],
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::trusted_new(
    tree_symbol,
    [data_constructor],
    Some(decl_test_span()),
  )
  try
    @logic.Decl::trusted_data(
      context,
      decl_snapshot_origin(b"tree", Type, 21U),
      [data],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, InvalidDeclaration)
  } noraise {
    _ => fail("expected nested recursive datatype rejection")
  }
}

///|
test "trusted inductives require matching positive case heads" {
  let context = @identity.CompilationContext::new()
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    decl_snapshot_origin(b"p", Logic, 30U),
    [],
    Some(decl_test_span()),
  )
  let other = @logic.LSymbol::new_predicate(
    context,
    b"q",
    decl_snapshot_origin(b"q", Logic, 31U),
    [],
    Some(decl_test_span()),
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"p_case",
    decl_snapshot_origin(b"p_case", Proposition, 32U),
  )
  let wrong_case = @logic.InductiveCase::trusted_new(
    context,
    proposition,
    @logic.Term::apply_predicate(other, [], Some(decl_test_span())),
    Some(decl_test_span()),
  )
  try
    @logic.InductiveDeclaration::trusted_new(
      predicate,
      [wrong_case],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, InvalidDeclaration)
  } noraise {
    _ => fail("expected mismatched inductive head rejection")
  }

  let recursive_call = @logic.Term::apply_predicate(
    predicate,
    [],
    Some(decl_test_span()),
  )
  let negative_formula = @logic.Term::binary(
    Implies,
    @logic.Term::not(recursive_call, Some(decl_test_span())),
    recursive_call,
    Some(decl_test_span()),
  )
  let negative_case = @logic.InductiveCase::trusted_new(
    context,
    proposition,
    negative_formula,
    Some(decl_test_span()),
  )
  let inductive = @logic.InductiveDeclaration::trusted_new(
    predicate,
    [negative_case],
    Some(decl_test_span()),
  )
  try
    @logic.Decl::trusted_inductive(
      context,
      decl_snapshot_origin(b"p", Logic, 30U),
      [inductive],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, InvalidDeclaration)
  } noraise {
    _ => fail("expected negative inductive occurrence rejection")
  }

  let positive_formula = @logic.Term::binary(
    Implies,
    @logic.Term::apply_predicate(other, [], Some(decl_test_span())),
    recursive_call,
    Some(decl_test_span()),
  )
  let positive_case = @logic.InductiveCase::trusted_new(
    context,
    proposition,
    positive_formula,
    Some(decl_test_span()),
  )
  let positive_inductive = @logic.InductiveDeclaration::trusted_new(
    predicate,
    [positive_case],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::trusted_inductive(
    context,
    decl_snapshot_origin(b"p", Logic, 30U),
    [positive_inductive],
    Some(decl_test_span()),
  )
  assert_true(declaration.view() is Dind(_))
}

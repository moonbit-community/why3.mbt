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
fn decl_catalog_origin(
  name : BytesView,
  _kind : @identity.SourceSymbolKind,
  _ordinal : UInt,
) -> @identity.Origin {
  @identity.Origin::user(name, Some(decl_test_span()), [])
}

///|
fn decl_integer_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @logic.Ty) raise @logic.TypeError {
  let symbol = @logic.TypeSymbol::new_builtin(
    context,
    b"int",
    decl_catalog_origin(b"int", Type, 0U),
    BuiltinInteger,
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
    decl_catalog_origin(b"int", Type, 0U),
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
test "logic definitions are closed and declaration checks termination" {
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
  let recursive_definition = @logic.LogicDefinition::new(
    context,
    function,
    [parameter],
    recursive_body,
    Some(decl_test_span()),
  )
  try
    @logic.Decl::logic(
      context,
      decl_user_origin(b"identity"),
      [recursive_definition],
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, NoTerminationProof)
  } noraise {
    _ => fail("expected non-decreasing recursive definition rejection")
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
    TypeError(diagnostic) => assert_eq(diagnostic.kind, NoTerminationProof)
  } noraise {
    _ => fail("expected mutual recursion rejection")
  }
}

///|
test "public data constructors support structural recursive definitions" {
  let context = @identity.CompilationContext::new()
  let natural_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"natural",
    decl_user_origin(b"natural"),
    [],
    Some(decl_test_span()),
  )
  let natural = @logic.Ty::app(natural_symbol, [], Some(decl_test_span()))
  let zero = @logic.LSymbol::new_constructor(
    context,
    b"Zero",
    decl_user_origin(b"Zero"),
    [],
    natural,
    2,
    Some(decl_test_span()),
  )
  let successor = @logic.LSymbol::new_constructor(
    context,
    b"Succ",
    decl_user_origin(b"Succ"),
    [natural],
    natural,
    2,
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::new(
    natural_symbol,
    [
      @logic.DataConstructor::new(zero, [], Some(decl_test_span())),
      @logic.DataConstructor::new(successor, [None], Some(decl_test_span())),
    ],
    Some(decl_test_span()),
  )
  let data_declaration = @logic.Decl::data(
    context,
    decl_user_origin(b"natural"),
    [data],
    Some(decl_test_span()),
  )
  assert_true(data_declaration.view() is Ddata(_))
  let normalize = @logic.LSymbol::new_function(
    context,
    b"normalize",
    decl_user_origin(b"normalize"),
    [natural],
    natural,
    Some(decl_test_span()),
  )
  let argument = @logic.VSymbol::new(
    context,
    b"n",
    decl_user_origin(b"n"),
    natural,
    Some(decl_test_span()),
  )
  let predecessor = @logic.VSymbol::new(
    context,
    b"predecessor",
    decl_user_origin(b"predecessor"),
    natural,
    Some(decl_test_span()),
  )
  let recursive_argument = @logic.VSymbol::new(
    context,
    b"recursive_argument",
    decl_user_origin(b"recursive_argument"),
    natural,
    Some(decl_test_span()),
  )
  let body = @logic.Term::case(
    @logic.Term::variable(argument),
    [
      (
        @logic.Pattern::app(zero, [], natural, Some(decl_test_span())),
        @logic.Term::apply_function(zero, [], Some(decl_test_span())),
      ),
      (
        @logic.Pattern::app(
          successor,
          [@logic.Pattern::variable(predecessor)],
          natural,
          Some(decl_test_span()),
        ),
        @logic.Term::let_in(
          recursive_argument,
          @logic.Term::variable(predecessor),
          @logic.Term::apply_function(
            normalize,
            [@logic.Term::variable(recursive_argument)],
            Some(decl_test_span()),
          ),
          Some(decl_test_span()),
        ),
      ),
    ],
    Some(decl_test_span()),
  )
  let definition = @logic.LogicDefinition::new(
    context,
    normalize,
    [argument],
    body,
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::logic(
    context,
    decl_user_origin(b"normalize"),
    [definition],
    Some(decl_test_span()),
  )
  guard declaration.view() is Dlogic([checked]) else {
    fail("expected one checked logic definition")
  }
  assert_eq(checked.view().decreasing_parameters, [0])

  let left = @logic.LSymbol::new_function(
    context,
    b"left",
    decl_user_origin(b"left"),
    [natural],
    natural,
    Some(decl_test_span()),
  )
  let right = @logic.LSymbol::new_function(
    context,
    b"right",
    decl_user_origin(b"right"),
    [natural],
    natural,
    Some(decl_test_span()),
  )
  let left_argument = @logic.VSymbol::new(
    context,
    b"left_argument",
    decl_user_origin(b"left_argument"),
    natural,
    Some(decl_test_span()),
  )
  let right_argument = @logic.VSymbol::new(
    context,
    b"right_argument",
    decl_user_origin(b"right_argument"),
    natural,
    Some(decl_test_span()),
  )
  let left_predecessor = @logic.VSymbol::new(
    context,
    b"left_predecessor",
    decl_user_origin(b"left_predecessor"),
    natural,
    Some(decl_test_span()),
  )
  let left_body = @logic.Term::case(
    @logic.Term::variable(left_argument),
    [
      (
        @logic.Pattern::app(zero, [], natural, Some(decl_test_span())),
        @logic.Term::apply_function(zero, [], Some(decl_test_span())),
      ),
      (
        @logic.Pattern::app(
          successor,
          [@logic.Pattern::variable(left_predecessor)],
          natural,
          Some(decl_test_span()),
        ),
        @logic.Term::apply_function(
          right,
          [@logic.Term::variable(left_predecessor)],
          Some(decl_test_span()),
        ),
      ),
    ],
    Some(decl_test_span()),
  )
  let right_body = @logic.Term::apply_function(
    left,
    [@logic.Term::variable(right_argument)],
    Some(decl_test_span()),
  )
  let mutual = @logic.Decl::logic(
    context,
    decl_user_origin(b"mutual"),
    [
      @logic.LogicDefinition::new(
        context,
        left,
        [left_argument],
        left_body,
        Some(decl_test_span()),
      ),
      @logic.LogicDefinition::new(
        context,
        right,
        [right_argument],
        right_body,
        Some(decl_test_span()),
      ),
    ],
    Some(decl_test_span()),
  )
  guard mutual.view() is Dlogic([checked_left, checked_right]) else {
    fail("expected two checked mutual definitions")
  }
  assert_eq(checked_left.view().decreasing_parameters, [0])
  assert_eq(checked_right.view().decreasing_parameters, [0])
}

///|
test "public record declarations validate projection signatures" {
  let context = @identity.CompilationContext::new()
  let (integer_symbol, integer) = decl_integer_type(context)
  let box_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    decl_user_origin(b"box"),
    [],
    Some(decl_test_span()),
  )
  let box_type = @logic.Ty::app(box_symbol, [], Some(decl_test_span()))
  let box_constructor = @logic.LSymbol::new_constructor(
    context,
    b"Box",
    decl_user_origin(b"Box"),
    [integer],
    box_type,
    1,
    Some(decl_test_span()),
  )
  let projection = @logic.LSymbol::new_projection(
    context,
    b"contents",
    decl_user_origin(b"contents"),
    box_type,
    integer,
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::new(
    box_symbol,
    [
      @logic.DataConstructor::new(
        box_constructor,
        [Some(projection)],
        Some(decl_test_span()),
      ),
    ],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::data(
    context,
    decl_user_origin(b"box"),
    [data],
    Some(decl_test_span()),
  )
  let known = @logic.KnownMap::new(context)
    .add(
      @logic.Decl::type_declaration(
        context,
        decl_catalog_origin(b"int", Type, 0U),
        [integer_symbol],
        Some(decl_test_span()),
      ),
      Some(decl_test_span()),
    )
    .add(declaration, Some(decl_test_span()))
  assert_true(known.contains(LogicDependency(projection)))
  let value = @logic.VSymbol::new(
    context,
    b"value",
    decl_user_origin(b"value"),
    integer,
    Some(decl_test_span()),
  )
  let record = known.make_record(
    [(projection, @logic.Term::variable(value))],
    box_type,
    Some(decl_test_span()),
  )
  assert_true(
    record.view() is Tapp(symbol, _, [_]) && symbol == box_constructor,
  )
  let updated = known.make_record_update(
    record,
    [(projection, @logic.Term::variable(value))],
    box_type,
    Some(decl_test_span()),
  )
  assert_true(
    updated.view() is Tapp(symbol, _, [_]) && symbol == box_constructor,
  )
  let pattern = known.make_record_pattern(
    [(projection, @logic.Pattern::variable(value))],
    box_type,
    Some(decl_test_span()),
  )
  assert_true(
    pattern.view() is Papp(symbol, [_], _) && symbol == box_constructor,
  )
  try
    known.make_record(
      [
        (projection, @logic.Term::variable(value)),
        (projection, @logic.Term::variable(value)),
      ],
      box_type,
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, DuplicateRecordField)
  } noraise {
    _ => fail("expected duplicate record field rejection")
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
test "data declarations introduce a projection shared by constructors once" {
  let context = @identity.CompilationContext::new()
  let (integer_symbol, integer) = decl_integer_type(context)
  let choice_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"choice",
    decl_user_origin(b"choice"),
    [],
    Some(decl_test_span()),
  )
  let choice_type = @logic.Ty::app(choice_symbol, [], Some(decl_test_span()))
  let projection = @logic.LSymbol::new_projection(
    context,
    b"value",
    decl_user_origin(b"value"),
    choice_type,
    integer,
    Some(decl_test_span()),
  )
  let constructors = [
    for name in [b"Left", b"Right"] => {
      let symbol = @logic.LSymbol::new_constructor(
        context,
        name,
        decl_user_origin(name),
        [integer],
        choice_type,
        2,
        Some(decl_test_span()),
      )
      @logic.DataConstructor::new(
        symbol,
        [Some(projection)],
        Some(decl_test_span()),
      )
    }
  ]
  let declaration = @logic.Decl::data(
    context,
    decl_user_origin(b"choice"),
    [
      @logic.DataDeclaration::new(
        choice_symbol,
        constructors,
        Some(decl_test_span()),
      ),
    ],
    Some(decl_test_span()),
  )
  let known = @logic.KnownMap::new(context)
    .add(
      @logic.Decl::type_declaration(
        context,
        decl_catalog_origin(b"int", Type, 0U),
        [integer_symbol],
        Some(decl_test_span()),
      ),
      Some(decl_test_span()),
    )
    .add(declaration, Some(decl_test_span()))
  assert_true(known.contains(LogicDependency(projection)))
}

///|
test "Ddata is validated and Dtype accepts Range" {
  let context = @identity.CompilationContext::new()
  let unit_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"unit",
    decl_catalog_origin(b"unit", Type, 0U),
    [],
    Some(decl_test_span()),
  )
  let unit_type = @logic.Ty::app(unit_symbol, [], Some(decl_test_span()))
  let unit_constructor = @logic.LSymbol::new_constructor(
    context,
    b"Tuple0",
    decl_catalog_origin(b"Tuple0", Logic, 0U),
    [],
    unit_type,
    1,
    Some(decl_test_span()),
  )
  let data_constructor = @logic.DataConstructor::new(
    unit_constructor,
    [],
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::new(
    unit_symbol,
    [data_constructor],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::data(
    context,
    decl_catalog_origin(b"unit", Type, 0U),
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
  let range_symbol = @logic.TypeSymbol::new_range(
    context,
    b"range",
    decl_user_origin(b"range"),
    BigInt::from_int(0),
    BigInt::from_int(10),
    Some(decl_test_span()),
  )
  let range_declaration = @logic.Decl::type_declaration(
    context,
    decl_user_origin(b"range"),
    [range_symbol],
    Some(decl_test_span()),
  )
  assert_true(
    range_declaration.view() is Dtype([symbol]) && symbol == range_symbol,
  )
}

///|
test "public coinductive declarations preserve their sign" {
  let context = @identity.CompilationContext::new()
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"stream",
    decl_user_origin(b"stream"),
    [],
    Some(decl_test_span()),
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"stream_case",
    decl_user_origin(b"stream_case"),
  )
  let case_ = @logic.InductiveCase::new(
    context,
    proposition,
    @logic.Term::apply_predicate(predicate, [], Some(decl_test_span())),
    Some(decl_test_span()),
  )
  let inductive = @logic.InductiveDeclaration::new(
    predicate,
    [case_],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::inductive(
    context,
    decl_user_origin(b"stream"),
    Coind,
    [inductive],
    Some(decl_test_span()),
  )
  assert_true(declaration.view() is Dind(Coind, [_]))
}

///|
test "known maps enforce foundness and declaration positivity" {
  let context = @identity.CompilationContext::new()
  let empty_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"empty",
    decl_user_origin(b"empty"),
    [],
    Some(decl_test_span()),
  )
  let empty_type = @logic.Ty::app(empty_symbol, [], Some(decl_test_span()))
  let looping_constructor = @logic.LSymbol::new_constructor(
    context,
    b"Loop",
    decl_user_origin(b"Loop"),
    [empty_type],
    empty_type,
    1,
    Some(decl_test_span()),
  )
  let empty_data = @logic.DataDeclaration::new(
    empty_symbol,
    [
      @logic.DataConstructor::new(
        looping_constructor,
        [None],
        Some(decl_test_span()),
      ),
    ],
    Some(decl_test_span()),
  )
  try
    @logic.KnownMap::new(context).add(
      @logic.Decl::data(
        context,
        decl_user_origin(b"empty"),
        [empty_data],
        Some(decl_test_span()),
      ),
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) =>
      assert_eq(diagnostic.kind, NonFoundedTypeDeclaration)
  } noraise {
    _ => fail("expected a non-founded algebraic type rejection")
  }

  let parameter = @logic.TyVarSymbol::new(context, b"a", decl_user_origin(b"a"))
  let invariant_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"invariant",
    decl_user_origin(b"invariant"),
    [parameter],
    Some(decl_test_span()),
  )
  let known = @logic.KnownMap::new(context).add(
    @logic.Decl::type_declaration(
      context,
      decl_user_origin(b"invariant"),
      [invariant_symbol],
      Some(decl_test_span()),
    ),
    Some(decl_test_span()),
  )
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    decl_user_origin(b"tree"),
    [],
    Some(decl_test_span()),
  )
  let tree_type = @logic.Ty::app(tree_symbol, [], Some(decl_test_span()))
  let nested = @logic.Ty::app(
    invariant_symbol,
    [tree_type],
    Some(decl_test_span()),
  )
  let wrap = @logic.LSymbol::new_constructor(
    context,
    b"Wrap",
    decl_user_origin(b"Wrap"),
    [nested],
    tree_type,
    1,
    Some(decl_test_span()),
  )
  let tree_data = @logic.DataDeclaration::new(
    tree_symbol,
    [@logic.DataConstructor::new(wrap, [None], Some(decl_test_span()))],
    Some(decl_test_span()),
  )
  try
    known.add(
      @logic.Decl::data(
        context,
        decl_user_origin(b"tree"),
        [tree_data],
        Some(decl_test_span()),
      ),
      Some(decl_test_span()),
    )
  catch {
    TypeError(diagnostic) =>
      assert_eq(diagnostic.kind, NonPositiveTypeDeclaration)
  } noraise {
    _ => fail("expected a non-positive algebraic type rejection")
  }
}

///|
test "known maps reject non-exhaustive case expressions" {
  let context = @identity.CompilationContext::new()
  let boolean_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"boolean",
    decl_user_origin(b"boolean"),
    [],
    Some(decl_test_span()),
  )
  let boolean = @logic.Ty::app(boolean_symbol, [], Some(decl_test_span()))
  let true_symbol = @logic.LSymbol::new_constructor(
    context,
    b"True",
    decl_user_origin(b"True"),
    [],
    boolean,
    2,
    Some(decl_test_span()),
  )
  let false_symbol = @logic.LSymbol::new_constructor(
    context,
    b"False",
    decl_user_origin(b"False"),
    [],
    boolean,
    2,
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::new(
    boolean_symbol,
    [
      @logic.DataConstructor::new(true_symbol, [], Some(decl_test_span())),
      @logic.DataConstructor::new(false_symbol, [], Some(decl_test_span())),
    ],
    Some(decl_test_span()),
  )
  let known = @logic.KnownMap::new(context).add(
    @logic.Decl::data(
      context,
      decl_user_origin(b"boolean"),
      [data],
      Some(decl_test_span()),
    ),
    Some(decl_test_span()),
  )
  assert_eq(known.find_constructors(boolean_symbol, None).length(), 2)
  let choose = @logic.LSymbol::new_function(
    context,
    b"choose",
    decl_user_origin(b"choose"),
    [boolean],
    boolean,
    Some(decl_test_span()),
  )
  let argument = @logic.VSymbol::new(
    context,
    b"argument",
    decl_user_origin(b"argument"),
    boolean,
    Some(decl_test_span()),
  )
  let body = @logic.Term::case(
    @logic.Term::variable(argument),
    [
      (
        @logic.Pattern::app(true_symbol, [], boolean, Some(decl_test_span())),
        @logic.Term::apply_function(true_symbol, [], Some(decl_test_span())),
      ),
    ],
    Some(decl_test_span()),
  )
  let definition = @logic.LogicDefinition::new(
    context,
    choose,
    [argument],
    body,
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::logic(
    context,
    decl_user_origin(b"choose"),
    [definition],
    Some(decl_test_span()),
  )
  try known.add(declaration, Some(decl_test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, NonExhaustivePattern)
  } noraise {
    _ => fail("expected a non-exhaustive case rejection")
  }
}

///|
test "Ddata rejects nested recursive occurrences" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    decl_catalog_origin(b"a", Type, 20U),
  )
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    decl_catalog_origin(b"tree", Type, 21U),
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
  let constructor_symbol = @logic.LSymbol::new_constructor(
    context,
    b"Nested",
    decl_catalog_origin(b"Nested", Logic, 22U),
    [nested_tree],
    tree_a,
    1,
    Some(decl_test_span()),
  )
  let data_constructor = @logic.DataConstructor::new(
    constructor_symbol,
    [None],
    Some(decl_test_span()),
  )
  let data = @logic.DataDeclaration::new(
    tree_symbol,
    [data_constructor],
    Some(decl_test_span()),
  )
  try
    @logic.Decl::data(
      context,
      decl_catalog_origin(b"tree", Type, 21U),
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
test "inductives require matching positive case heads" {
  let context = @identity.CompilationContext::new()
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    decl_catalog_origin(b"p", Logic, 30U),
    [],
    Some(decl_test_span()),
  )
  let other = @logic.LSymbol::new_predicate(
    context,
    b"q",
    decl_catalog_origin(b"q", Logic, 31U),
    [],
    Some(decl_test_span()),
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"p_case",
    decl_catalog_origin(b"p_case", Proposition, 32U),
  )
  let wrong_case = @logic.InductiveCase::new(
    context,
    proposition,
    @logic.Term::apply_predicate(other, [], Some(decl_test_span())),
    Some(decl_test_span()),
  )
  try
    @logic.InductiveDeclaration::new(
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
  let negative_case = @logic.InductiveCase::new(
    context,
    proposition,
    negative_formula,
    Some(decl_test_span()),
  )
  let inductive = @logic.InductiveDeclaration::new(
    predicate,
    [negative_case],
    Some(decl_test_span()),
  )
  try
    @logic.Decl::inductive(
      context,
      decl_catalog_origin(b"p", Logic, 30U),
      Ind,
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
  let positive_case = @logic.InductiveCase::new(
    context,
    proposition,
    positive_formula,
    Some(decl_test_span()),
  )
  let positive_inductive = @logic.InductiveDeclaration::new(
    predicate,
    [positive_case],
    Some(decl_test_span()),
  )
  let declaration = @logic.Decl::inductive(
    context,
    decl_catalog_origin(b"p", Logic, 30U),
    Ind,
    [positive_inductive],
    Some(decl_test_span()),
  )
  assert_true(declaration.view() is Dind(Ind, _))
}

///|
test "abstract case exhaustiveness sees wildcard alternatives under as/or" {
  let context = @identity.CompilationContext::new()
  let abstract_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"abstract",
    decl_user_origin(b"abstract"),
    [],
    None,
  )
  let abstract_ty = @logic.Ty::app(abstract_symbol, [], None)
  let type_declaration = @logic.Decl::type_declaration(
    context,
    decl_user_origin(b"abstract"),
    [abstract_symbol],
    None,
  )
  let scrutinee = @logic.VSymbol::new(
    context,
    b"value",
    decl_user_origin(b"value"),
    abstract_ty,
    None,
  )
  let whole_variable = @logic.VSymbol::new(
    context,
    b"whole",
    decl_user_origin(b"whole"),
    abstract_ty,
    None,
  )
  let alternative = @logic.Pattern::or(
    @logic.Pattern::wild(abstract_ty),
    @logic.Pattern::wild(abstract_ty),
    None,
  )
  let pattern = @logic.Pattern::as_pattern(alternative, whole_variable, None)
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [scrutinee],
    [],
    @logic.Term::case(
      @logic.Term::variable(scrutinee),
      [(pattern, @logic.Term::true_formula())],
      None,
    ),
    None,
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"exhaustive",
    decl_user_origin(b"exhaustive"),
  )
  let declaration = @logic.Decl::proposition(
    context,
    decl_user_origin(b"exhaustive"),
    Paxiom,
    proposition,
    formula,
    None,
  )
  let known = @logic.KnownMap::new(context).add(type_declaration, None)
  assert_true(
    known.add(declaration, None).contains(PropositionDependency(proposition)),
  )
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn term_test_span() -> @identity.SourceSpan {
  @identity.SourceSpan::new(b"term.mlw", 1, 8, 1L, 1L, 1L, 8L)
}

///|
fn term_user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, Some(term_test_span()), [])
}

///|
fn term_snapshot_origin(
  name : BytesView,
  kind : @identity.SnapshotSymbolKind,
  ordinal : UInt,
) -> @identity.Origin {
  @identity.Origin::snapshot(
    name,
    @identity.SnapshotSymbolKey::new(
      b"why3.TermTest",
      ordinal,
      0U,
      kind,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
fn term_builtin(
  context : @identity.CompilationContext,
  name : BytesView,
  kind : @logic.BuiltinTypeKind,
  ordinal : UInt,
) -> (@logic.TypeSymbol, @logic.Ty) raise @logic.TypeError {
  let symbol = @logic.TypeSymbol::trusted_builtin(
    context,
    name,
    term_snapshot_origin(name, Type, ordinal),
    kind,
    Some(term_test_span()),
  )
  (symbol, @logic.Ty::app(symbol, [], Some(term_test_span())))
}

///|
test "function and predicate APIs reject kind confusion" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let x = @logic.VSymbol::new(
    context,
    b"x",
    term_user_origin(b"x"),
    integer,
    Some(term_test_span()),
  )
  let function = @logic.LSymbol::new_function(
    context,
    b"f",
    term_user_origin(b"f"),
    [integer],
    integer,
    Some(term_test_span()),
  )
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    term_user_origin(b"p"),
    [integer],
    Some(term_test_span()),
  )
  try
    @logic.Term::apply_predicate(
      function,
      [@logic.Term::variable(x)],
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, PredicateExpected)
  } noraise {
    _ => fail("expected function/predicate confusion")
  }
  try
    @logic.Term::apply_function(
      predicate,
      [@logic.Term::variable(x)],
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, FunctionExpected)
  } noraise {
    _ => fail("expected predicate/function confusion")
  }
}

///|
test "polymorphic applications reject inconsistent equality arguments" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let (_, boolean) = term_builtin(context, b"bool", BuiltinBoolean, 1U)
  let a = @logic.TyVarSymbol::new(context, b"a", term_user_origin(b"a"))
  let equality = @logic.LSymbol::new_predicate(
    context,
    b"=",
    term_user_origin(b"="),
    [@logic.Ty::variable(a), @logic.Ty::variable(a)],
    Some(term_test_span()),
  )
  let x = @logic.VSymbol::new(
    context,
    b"x",
    term_user_origin(b"x"),
    integer,
    Some(term_test_span()),
  )
  let b = @logic.VSymbol::new(
    context,
    b"b",
    term_user_origin(b"b"),
    boolean,
    Some(term_test_span()),
  )
  try
    @logic.Term::apply_predicate(
      equality,
      [@logic.Term::variable(x), @logic.Term::variable(b)],
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, TypeMismatch)
  } noraise {
    _ => fail("expected equality type mismatch")
  }
}

///|
test "formula and boolean values never mix implicitly" {
  let context = @identity.CompilationContext::new()
  let (_, boolean) = term_builtin(context, b"bool", BuiltinBoolean, 0U)
  let value = @logic.Term::variable(
    @logic.VSymbol::new(
      context,
      b"b",
      term_user_origin(b"b"),
      boolean,
      Some(term_test_span()),
    ),
  )
  try
    @logic.Term::if_then_else(
      @logic.Term::true_formula(),
      value,
      @logic.Term::false_formula(),
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, TypeMismatch)
  } noraise {
    _ => fail("expected formula/value branch mismatch")
  }
  try @logic.Term::not(value, Some(term_test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, FormulaExpected)
  } noraise {
    _ => fail("expected explicit boolean-to-formula coercion requirement")
  }
}

///|
test "alpha equivalence and capture-safe substitution respect shadowing" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let a = @logic.TyVarSymbol::new(context, b"a", term_user_origin(b"a"))
  let equality = @logic.LSymbol::new_predicate(
    context,
    b"=",
    term_user_origin(b"="),
    [@logic.Ty::variable(a), @logic.Ty::variable(a)],
    Some(term_test_span()),
  )
  let x = @logic.VSymbol::new(
    context,
    b"x",
    term_user_origin(b"x"),
    integer,
    Some(term_test_span()),
  )
  let y = @logic.VSymbol::new(
    context,
    b"y",
    term_user_origin(b"y"),
    integer,
    Some(term_test_span()),
  )
  let reflexive_x = @logic.Term::apply_predicate(
    equality,
    [@logic.Term::variable(x), @logic.Term::variable(x)],
    Some(term_test_span()),
  )
  let reflexive_y = @logic.Term::apply_predicate(
    equality,
    [@logic.Term::variable(y), @logic.Term::variable(y)],
    Some(term_test_span()),
  )
  let quantified_x = @logic.Term::quantify(
    ForallQuantifier,
    [x],
    [[@logic.Term::variable(x)]],
    reflexive_x,
    Some(term_test_span()),
  )
  let quantified_y = @logic.Term::quantify(
    ForallQuantifier,
    [y],
    [[@logic.Term::variable(y)]],
    reflexive_y,
    Some(term_test_span()),
  )
  assert_true(quantified_x.alpha_equivalent(quantified_y))
  let body = @logic.Term::apply_predicate(
    equality,
    [@logic.Term::variable(y), @logic.Term::variable(x)],
    Some(term_test_span()),
  )
  let quantified = @logic.Term::quantify(
    ForallQuantifier,
    [x],
    [],
    body,
    Some(term_test_span()),
  )
  let substituted = @logic.TermSubstitution::new()
    .bind(y, @logic.Term::variable(x), Some(term_test_span()))
    .apply(context, quantified, Some(term_test_span()))
  let free = substituted.free_variables()
  assert_eq(free.length(), 1)
  assert_true(free[0] == x)
}

///|
test "triggers reject variables outside the quantified body" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let x = @logic.VSymbol::new(
    context,
    b"x",
    term_user_origin(b"x"),
    integer,
    Some(term_test_span()),
  )
  let outside = @logic.VSymbol::new(
    context,
    b"outside",
    term_user_origin(b"outside"),
    integer,
    Some(term_test_span()),
  )
  try
    @logic.Term::quantify(
      ForallQuantifier,
      [x],
      [[@logic.Term::variable(outside)]],
      @logic.Term::true_formula(),
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, InvalidTrigger)
  } noraise {
    _ => fail("expected invalid trigger")
  }
}

///|
test "one polymorphic symbol records distinct type instances" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let (_, boolean) = term_builtin(context, b"bool", BuiltinBoolean, 1U)
  let a = @logic.TyVarSymbol::new(context, b"a", term_user_origin(b"a"))
  let identity = @logic.LSymbol::new_function(
    context,
    b"id",
    term_user_origin(b"id"),
    [@logic.Ty::variable(a)],
    @logic.Ty::variable(a),
    Some(term_test_span()),
  )
  let integer_variable = @logic.VSymbol::new(
    context,
    b"i",
    term_user_origin(b"i"),
    integer,
    Some(term_test_span()),
  )
  let boolean_variable = @logic.VSymbol::new(
    context,
    b"b",
    term_user_origin(b"b"),
    boolean,
    Some(term_test_span()),
  )
  let integer_instance = @logic.Term::apply_function(
    identity,
    [@logic.Term::variable(integer_variable)],
    Some(term_test_span()),
  )
  let boolean_instance = @logic.Term::apply_function(
    identity,
    [@logic.Term::variable(boolean_variable)],
    Some(term_test_span()),
  )
  assert_true(integer_instance.ty() == Some(integer))
  assert_true(boolean_instance.ty() == Some(boolean))
}

///|
test "exact constants enforce Range Float and string types" {
  let context = @identity.CompilationContext::new()
  let (_, string_type) = term_builtin(context, b"string", BuiltinString, 0U)
  let range_symbol = @logic.TypeSymbol::trusted_range(
    context,
    b"range8",
    term_snapshot_origin(b"range8", Type, 1U),
    BigInt::from_int(-128),
    BigInt::from_int(127),
    Some(term_test_span()),
  )
  let range_type = @logic.Ty::app(range_symbol, [], Some(term_test_span()))
  ignore(
    @logic.Term::constant(
      @logic.Constant::integer(IntegerDecimal, BigInt::from_int(127)),
      range_type,
      Some(term_test_span()),
    ),
  )
  try
    @logic.Term::constant(
      @logic.Constant::integer(IntegerDecimal, BigInt::from_int(128)),
      range_type,
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, ConstantOutOfRange)
  } noraise {
    _ => fail("expected Range rejection")
  }
  let string_term = @logic.Term::constant(
    @logic.Constant::string(b"a\x00\xff"),
    string_type,
    Some(term_test_span()),
  )
  guard string_term.view() is Tconst(string_constant) &&
    string_constant.view() is StringConstant(bytes) else {
    fail("expected string constant")
  }
  assert_eq(bytes, b"a\x00\xff")
  let float_symbol = @logic.TypeSymbol::trusted_float(
    context,
    b"float32",
    term_snapshot_origin(b"float32", Type, 2U),
    8,
    24,
    Some(term_test_span()),
  )
  let float_type = @logic.Ty::app(float_symbol, [], Some(term_test_span()))
  ignore(
    @logic.Term::constant(
      @logic.Constant::real(
        RealDecimal(0L),
        @parser.RealValue::normalized(
          BigInt::from_int(1),
          BigInt::from_int(0),
          BigInt::from_int(0),
        ),
      ),
      float_type,
      Some(term_test_span()),
    ),
  )
  try
    @logic.Term::constant(
      @logic.Constant::real(
        RealDecimal(0L),
        @parser.RealValue::normalized(
          BigInt::from_int(1),
          BigInt::from_int(0),
          BigInt::from_int(-1),
        ),
      ),
      float_type,
      Some(term_test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, NonRepresentableFloat)
  } noraise {
    _ => fail("expected non-representable Float rejection")
  }
}

///|
test "instantiated applications expose actual rather than scheme type variables" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let formal = @logic.TyVarSymbol::new(
    context,
    b"formal",
    term_user_origin(b"formal"),
  )
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    term_user_origin(b"p"),
    [@logic.Ty::variable(formal)],
    Some(term_test_span()),
  )
  let value = @logic.VSymbol::new(
    context,
    b"value",
    term_user_origin(b"value"),
    integer,
    Some(term_test_span()),
  )
  let application = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(value)],
    Some(term_test_span()),
  )
  assert_true(application.free_type_variables().is_empty())
}

///|
test "substitution merges decoration and validates replacement context" {
  let context = @identity.CompilationContext::new()
  let (_, integer) = term_builtin(context, b"int", BuiltinInteger, 0U)
  let source = @logic.VSymbol::new(
    context,
    b"source",
    term_user_origin(b"source"),
    integer,
    Some(term_test_span()),
  )
  let replacement_variable = @logic.VSymbol::new(
    context,
    b"replacement",
    term_user_origin(b"replacement"),
    integer,
    Some(term_test_span()),
  )
  let source_origin = term_user_origin(b"source-term")
  let replacement_origin = term_user_origin(b"replacement-term")
  let source_term = @logic.Term::variable(source).decorate(source_origin, [
    b"source-attribute",
  ])
  let replacement = @logic.Term::variable(replacement_variable).decorate(
    replacement_origin,
    [b"replacement-attribute"],
  )
  let result = @logic.TermSubstitution::new()
    .bind(source, replacement, Some(term_test_span()))
    .apply(context, source_term, Some(term_test_span()))
  assert_true(result.origin() == Some(replacement_origin))
  assert_eq(result.attributes(), [b"replacement-attribute", b"source-attribute"])

  let foreign_context = @identity.CompilationContext::new()
  let foreign_predicate = @logic.LSymbol::new_predicate(
    foreign_context,
    b"foreign",
    term_user_origin(b"foreign"),
    [],
    Some(term_test_span()),
  )
  let mixed = @logic.Term::if_then_else(
    @logic.Term::apply_predicate(foreign_predicate, [], Some(term_test_span())),
    @logic.Term::variable(replacement_variable),
    @logic.Term::variable(replacement_variable),
    Some(term_test_span()),
  )
  let substitution = @logic.TermSubstitution::new().bind(
    source,
    mixed,
    Some(term_test_span()),
  )
  try substitution.apply(context, @logic.Term::variable(source), None) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, ContextMismatch)
  } noraise {
    _ => fail("expected foreign replacement context rejection")
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_span() -> @identity.SourceSpan {
  @identity.SourceSpan::new(b"types.mlw", 4, 9, 1L, 4L, 1L, 9L)
}

///|
fn user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, Some(test_span()), [])
}

///|
fn snapshot_type_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::snapshot(
    name,
    @identity.SnapshotSymbolKey::new(
      b"why3.Test",
      0U,
      0U,
      Type,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
test "aliases expand and semantic applications enforce arity" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(context, b"a", user_origin(b"a"))
  let list = @logic.TypeSymbol::new_abstract(
    context,
    b"list",
    user_origin(b"list"),
    [parameter],
    Some(test_span()),
  )
  let integer = @logic.TypeSymbol::new_abstract(
    context,
    b"int",
    user_origin(b"int"),
    [],
    Some(test_span()),
  )
  let alias_target = @logic.Ty::app(
    list,
    [@logic.Ty::variable(parameter)],
    Some(test_span()),
  )
  let sequence_alias = @logic.TypeSymbol::new_alias(
    context,
    b"sequence",
    user_origin(b"sequence"),
    [parameter],
    alias_target,
    Some(test_span()),
  )
  let int_type = @logic.Ty::app(integer, [], Some(test_span()))
  let expanded = @logic.Ty::app(sequence_alias, [int_type], Some(test_span()))
  guard expanded.view() is TyApp(expanded_symbol, arguments) else {
    fail("expected expanded type application")
  }
  assert_true(expanded_symbol == list)
  assert_eq(arguments.length(), 1)
  assert_true(arguments[0] == int_type)
  try @logic.Ty::app(list, [], Some(test_span())) catch {
    TypeError(diagnostic) => {
      assert_eq(diagnostic.kind, ArityMismatch)
      assert_eq(diagnostic.span, Some(test_span()))
    }
  } noraise {
    _ => fail("expected arity mismatch")
  }
}

///|
test "alias parameters are unique and bind every free variable" {
  let context = @identity.CompilationContext::new()
  let a = @logic.TyVarSymbol::new(context, b"a", user_origin(b"a"))
  let b = @logic.TyVarSymbol::new(context, b"b", user_origin(b"b"))
  try
    @logic.TypeSymbol::new_abstract(
      context,
      b"bad",
      user_origin(b"bad"),
      [a, a],
      Some(test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, DuplicateTypeParameter)
  } noraise {
    _ => fail("expected duplicate parameter error")
  }
  try
    @logic.TypeSymbol::new_alias(
      context,
      b"bad_alias",
      user_origin(b"bad_alias"),
      [a],
      @logic.Ty::variable(b),
      Some(test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, UnboundTypeVariable)
  } noraise {
    _ => fail("expected unbound variable error")
  }
}

///|
test "substitution composition is left-to-right and immutable" {
  let context = @identity.CompilationContext::new()
  let a = @logic.TyVarSymbol::new(context, b"a", user_origin(b"a"))
  let b = @logic.TyVarSymbol::new(context, b"b", user_origin(b"b"))
  let integer = @logic.TypeSymbol::new_abstract(
    context,
    b"int",
    user_origin(b"int"),
    [],
    Some(test_span()),
  )
  let int_type = @logic.Ty::app(integer, [], Some(test_span()))
  let first = @logic.TySubstitution::new().bind(
    a,
    @logic.Ty::variable(b),
    Some(test_span()),
  )
  let second = @logic.TySubstitution::new().bind(b, int_type, Some(test_span()))
  let composed = first.then(second, Some(test_span()))
  assert_true(
    composed.apply(@logic.Ty::variable(a), Some(test_span())) == int_type,
  )
  assert_true(
    first.apply(@logic.Ty::variable(a), Some(test_span())) ==
    @logic.Ty::variable(b),
  )
}

///|
test "type matching binds variables and rejects inconsistent repetition" {
  let context = @identity.CompilationContext::new()
  let a = @logic.TyVarSymbol::new(context, b"a", user_origin(b"a"))
  let pair = @logic.TypeSymbol::new_abstract(
    context,
    b"pair",
    user_origin(b"pair"),
    [a, @logic.TyVarSymbol::new(context, b"b", user_origin(b"b"))],
    Some(test_span()),
  )
  let integer = @logic.TypeSymbol::new_abstract(
    context,
    b"int",
    user_origin(b"int"),
    [],
    Some(test_span()),
  )
  let boolean = @logic.TypeSymbol::new_abstract(
    context,
    b"bool",
    user_origin(b"bool"),
    [],
    Some(test_span()),
  )
  let int_type = @logic.Ty::app(integer, [], Some(test_span()))
  let bool_type = @logic.Ty::app(boolean, [], Some(test_span()))
  let repeated = @logic.Ty::app(
    pair,
    [@logic.Ty::variable(a), @logic.Ty::variable(a)],
    Some(test_span()),
  )
  let same = @logic.Ty::app(pair, [int_type, int_type], Some(test_span()))
  let substitution = @logic.type_match(repeated, same, Some(test_span()))
  assert_true(
    substitution.apply(@logic.Ty::variable(a), Some(test_span())) == int_type,
  )
  let different = @logic.Ty::app(pair, [int_type, bool_type], Some(test_span()))
  try @logic.type_match(repeated, different, Some(test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, TypeMismatch)
  } noraise {
    _ => fail("expected inconsistent type match")
  }
}

///|
test "snapshot-only Range and Float reject user origins" {
  let context = @identity.CompilationContext::new()
  try
    @logic.TypeSymbol::trusted_range(
      context,
      b"range",
      user_origin(b"range"),
      BigInt::from_int(0),
      BigInt::from_int(10),
      Some(test_span()),
    )
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, SnapshotOriginRequired)
  } noraise {
    _ => fail("expected snapshot-only rejection")
  }
  try
    @logic.TypeSymbol::trusted_range(
      context,
      b"empty",
      snapshot_type_origin(b"empty"),
      BigInt::from_int(1),
      BigInt::from_int(0),
      Some(test_span()),
    )
  catch {
    TypeError(diagnostic) => {
      assert_eq(diagnostic.kind, InvalidRange)
      assert_eq(diagnostic.span, Some(test_span()))
    }
  } noraise {
    _ => fail("expected invalid Range rejection")
  }
  try
    @logic.TypeSymbol::trusted_float(
      context,
      b"float",
      snapshot_type_origin(b"float"),
      0,
      24,
      Some(test_span()),
    )
  catch {
    TypeError(diagnostic) => {
      assert_eq(diagnostic.kind, InvalidFloat)
      assert_eq(diagnostic.span, Some(test_span()))
    }
  } noraise {
    _ => fail("expected invalid Float rejection")
  }
}

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
test "type matching is directional and substitutions remain one-layer" {
  let context = @identity.CompilationContext::new()
  let a = @logic.TyVarSymbol::new(context, b"a", user_origin(b"a"))
  let b = @logic.TyVarSymbol::new(context, b"b", user_origin(b"b"))
  let c = @logic.TyVarSymbol::new(context, b"c", user_origin(b"c"))
  let integer = @logic.TypeSymbol::new_abstract(
    context,
    b"int",
    user_origin(b"int"),
    [],
    Some(test_span()),
  )
  let int_type = @logic.Ty::app(integer, [], Some(test_span()))
  let a_type = @logic.Ty::variable(a)
  let b_type = @logic.Ty::variable(b)
  let c_type = @logic.Ty::variable(c)
  let substitution = @logic.TySubstitution::new().match_type(
    a_type,
    b_type,
    Some(test_span()),
  )
  assert_true(substitution.apply(a_type, Some(test_span())) == b_type)
  try substitution.match_type(a_type, c_type, Some(test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, TypeMismatch)
  } noraise {
    _ => fail("a matched type variable accepted a different subject")
  }
  let layered = substitution.bind(b, int_type, Some(test_span()))
  assert_true(
    layered.apply(a_type, Some(test_span())) == b_type &&
    layered.apply(b_type, Some(test_span())) == int_type,
  )
  let cyclic = @logic.TySubstitution::new()
    .bind(a, b_type, Some(test_span()))
    .bind(b, a_type, Some(test_span()))
  assert_true(
    cyclic.apply(a_type, Some(test_span())) == b_type &&
    cyclic.apply(b_type, Some(test_span())) == a_type,
  )
  let inference = @logic.TyVarSymbol::new(
    context,
    b"xi",
    @identity.Origin::user(b"xi", Some(test_span()), [
      b"mlw:inference_type_variable",
    ]),
  )
  let wrapper = @logic.TypeSymbol::new_abstract(
    context,
    b"wrapper",
    user_origin(b"wrapper"),
    [a],
    Some(test_span()),
  )
  let inferred = @logic.Ty::app(
    wrapper,
    [@logic.Ty::variable(inference)],
    Some(test_span()),
  )
  let concrete = @logic.Ty::app(wrapper, [int_type], Some(test_span()))
  let resolved = @logic.TySubstitution::new()
    .match_type(a_type, inferred, Some(test_span()))
    .match_type(a_type, concrete, Some(test_span()))
  assert_true(resolved.apply(a_type, Some(test_span())) == concrete)
}

///|
test "Range and Float are ordinary exact type definitions" {
  let context = @identity.CompilationContext::new()
  let range = @logic.TypeSymbol::new_range(
    context,
    b"range",
    user_origin(b"range"),
    BigInt::from_int(0),
    BigInt::from_int(10),
    Some(test_span()),
  )
  assert_true(
    range.view().definition is Range(lower, upper) &&
    lower == BigInt::from_int(0) &&
    upper == BigInt::from_int(10),
  )
  let float = @logic.TypeSymbol::new_float(
    context,
    b"float32",
    user_origin(b"float32"),
    8,
    24,
    Some(test_span()),
  )
  assert_true(float.view().definition is Float(8, 24))
  try
    @logic.TypeSymbol::new_range(
      context,
      b"empty",
      user_origin(b"empty"),
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
    @logic.TypeSymbol::new_float(
      context,
      b"float",
      user_origin(b"float"),
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

///|
test "type hash-consing exposes stable first-allocation order" {
  let context = @identity.CompilationContext::new()
  let first_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"first",
    user_origin(b"first"),
    [],
    Some(test_span()),
  )
  let second_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"second",
    user_origin(b"second"),
    [],
    Some(test_span()),
  )
  let first = @logic.Ty::app(first_symbol, [], Some(test_span()))
  let second = @logic.Ty::app(second_symbol, [], Some(test_span()))
  let first_again = @logic.Ty::app(first_symbol, [], Some(test_span()))
  assert_true(first.allocation_order() < second.allocation_order())
  assert_true(first == first_again)
  assert_eq(first.allocation_order(), first_again.allocation_order())
}

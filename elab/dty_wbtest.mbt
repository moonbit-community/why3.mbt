// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn dty_test_span() -> @identity.SourceSpan {
  @identity.SourceSpan::new(b"elab.mlw", 2, 7, 1L, 2L, 1L, 7L)
}

///|
fn dty_user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, Some(dty_test_span()), [])
}

///|
fn nullary_type(
  context : @identity.CompilationContext,
  name : BytesView,
) -> (@logic.TypeSymbol, @logic.Ty) raise @logic.TypeError {
  let symbol = @logic.TypeSymbol::new_abstract(
    context,
    name,
    dty_user_origin(name),
    [],
    Some(dty_test_span()),
  )
  (symbol, @logic.Ty::app(symbol, [], Some(dty_test_span())))
}

///|
test "delayed unification resolves fresh variables and compresses links" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let (_, integer) = nullary_type(semantic_context, b"int")
  let fresh = delayed_context.fresh()
  let known = delayed_context.known(integer, Some(dty_test_span()))
  delayed_context.unify(fresh, known, Some(dty_test_span()))
  assert_true(
    delayed_context.finalize_strict(fresh, Some(dty_test_span())) == integer,
  )
}

///|
test "delayed unification rejects constructor mismatch with stable position" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let (_, integer) = nullary_type(semantic_context, b"int")
  let (_, boolean) = nullary_type(semantic_context, b"bool")
  let left = delayed_context.known(integer, Some(dty_test_span()))
  let right = delayed_context.known(boolean, Some(dty_test_span()))
  try delayed_context.unify(left, right, Some(dty_test_span())) catch {
    TypeError(diagnostic) => {
      assert_eq(diagnostic.kind, TypeMismatch)
      assert_eq(diagnostic.span, Some(dty_test_span()))
    }
  } noraise {
    _ => fail("expected delayed type mismatch")
  }
}

///|
test "occurs check rejects an infinite delayed type" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let parameter = @logic.TyVarSymbol::new(
    semantic_context,
    b"a",
    dty_user_origin(b"a"),
  )
  let list = @logic.TypeSymbol::new_abstract(
    semantic_context,
    b"list",
    dty_user_origin(b"list"),
    [parameter],
    Some(dty_test_span()),
  )
  let fresh = delayed_context.fresh()
  let recursive = delayed_context.app(list, [fresh], Some(dty_test_span()))
  try delayed_context.unify(fresh, recursive, Some(dty_test_span())) catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, OccursCheck)
  } noraise {
    _ => fail("expected occurs-check failure")
  }
}

///|
test "higher-order delayed application reports an occurs check" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let variable = delayed_context.fresh()
  let result = delayed_context.fresh()
  let self_application = delayed_context.arrow(variable, result, None)
  try
    delayed_context.unify(variable, self_application, Some(dty_test_span()))
  catch {
    TypeError(diagnostic) => assert_eq(diagnostic.kind, OccursCheck)
  } noraise {
    _ => fail("expected an occurs-check failure for x x")
  }
}

///|
test "pure finalization accepts semantic polymorphism" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let variable = @logic.TyVarSymbol::new(
    semantic_context,
    b"a",
    dty_user_origin(b"a"),
  )
  let semantic = @logic.Ty::variable(variable)
  assert_true(
    delayed_context.finalize_pure(delayed_context.known(semantic, None), None) ==
    semantic,
  )
}

///|
test "program strict finalize rejects unresolved variables" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  try
    delayed_context.finalize_strict(
      delayed_context.fresh(),
      Some(dty_test_span()),
    )
  catch {
    TypeError(diagnostic) => {
      assert_eq(diagnostic.kind, UnresolvedTypeVariable)
      assert_eq(diagnostic.span, Some(dty_test_span()))
    }
  } noraise {
    _ => fail("expected strict-finalize failure")
  }
}

///|
test "program strict finalize rejects known polymorphic types" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let variable = @logic.TyVarSymbol::new(
    semantic_context,
    b"a",
    dty_user_origin(b"a"),
  )
  let polymorphic = delayed_context.known(
    @logic.Ty::variable(variable),
    Some(dty_test_span()),
  )
  try
    delayed_context.finalize_strict(polymorphic, Some(dty_test_span()))
  catch {
    TypeError(diagnostic) =>
      assert_eq(diagnostic.kind, PolymorphicProgramRoutine)
  } noraise {
    _ => fail("expected polymorphic-program rejection")
  }
}

///|
test "pure-logic generalization is deterministic and shares variables" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let left_parameter = @logic.TyVarSymbol::new(
    semantic_context,
    b"a",
    dty_user_origin(b"a"),
  )
  let right_parameter = @logic.TyVarSymbol::new(
    semantic_context,
    b"b",
    dty_user_origin(b"b"),
  )
  let pair = @logic.TypeSymbol::new_abstract(
    semantic_context,
    b"pair",
    dty_user_origin(b"pair"),
    [left_parameter, right_parameter],
    Some(dty_test_span()),
  )
  let fresh = delayed_context.fresh()
  let delayed_pair = delayed_context.app(
    pair,
    [fresh, fresh],
    Some(dty_test_span()),
  )
  let (generalized, variables) = delayed_context.generalize(
    delayed_pair,
    Some(dty_test_span()),
  )
  assert_eq(variables.length(), 1)
  guard generalized.view() is TyApp(_, arguments) else {
    fail("expected generalized application")
  }
  assert_eq(arguments.length(), 2)
  assert_true(arguments[0] == arguments[1])
  assert_true(arguments[0] == @logic.Ty::variable(variables[0]))
}

///|
test "delayed alias expansion preserves unresolved arguments" {
  let semantic_context = @identity.CompilationContext::new()
  let delayed_context = DtyContext::new(semantic_context)
  let parameter = @logic.TyVarSymbol::new(
    semantic_context,
    b"a",
    dty_user_origin(b"a"),
  )
  let box_symbol = @logic.TypeSymbol::new_abstract(
    semantic_context,
    b"box",
    dty_user_origin(b"box"),
    [parameter],
    Some(dty_test_span()),
  )
  let box_alias = @logic.TypeSymbol::new_alias(
    semantic_context,
    b"box_alias",
    dty_user_origin(b"box_alias"),
    [parameter],
    @logic.Ty::app(
      box_symbol,
      [@logic.Ty::variable(parameter)],
      Some(dty_test_span()),
    ),
    Some(dty_test_span()),
  )
  let delayed_alias = delayed_context.app(
    box_alias,
    [delayed_context.fresh()],
    Some(dty_test_span()),
  )
  let (generalized, variables) = delayed_context.generalize(
    delayed_alias,
    Some(dty_test_span()),
  )
  assert_eq(variables.length(), 1)
  guard generalized.view() is TyApp(symbol, arguments) else {
    fail("expected expanded delayed alias")
  }
  assert_true(symbol == box_symbol)
  assert_true(arguments[0] == @logic.Ty::variable(variables[0]))
}

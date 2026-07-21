// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn env_name(name : BytesView) -> @theory.SemanticName {
  @theory.SemanticName::new(name, [], None)
}

///|
fn empty_theory(
  context : @identity.CompilationContext,
  path : ArrayView[Bytes],
  name : BytesView,
) -> @theory.Theory raise {
  @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new(path, name),
    env_name(name),
  ).close()
}

///|
test "environment separates visible aliases from driver-only theories" {
  let context = @identity.CompilationContext::new()
  let environment = @environment.Environment::new(context)
  let builtin = empty_theory(context, [b"why3", b"BuiltIn"], b"BuiltIn")
  let hidden = empty_theory(context, [b"bv"], b"BV64")
  environment.register_theory(builtin, false, None)
  environment.register_theory(hidden, false, None)
  environment.add_theory_alias(
    @theory.TheoryKey::new([], b"BuiltIn"),
    builtin.key(),
    None,
  )
  assert_true(
    environment
    .resolve_theory(@theory.TheoryKey::new([], b"BuiltIn"), None)
    .key() ==
    builtin.key(),
  )
  try environment.resolve_theory(hidden.key(), None) catch {
    EnvironmentError(diagnostic) => assert_eq(diagnostic.kind, DriverOnlyTheory)
  } noraise {
    _ => fail("expected driver-only rejection")
  }
  try
    environment.resolve_theory(@theory.TheoryKey::new([], b"Missing"), None)
  catch {
    _ => ()
  } noraise {
    _ => fail("expected resolve error")
  }
}

///|
test "environment rejects cross-context registration" {
  let context = @identity.CompilationContext::new()
  let other = @identity.CompilationContext::new()
  let environment = @environment.Environment::new(context)
  let foreign = empty_theory(other, [], b"Foreign")
  try environment.register_theory(foreign, true, None) catch {
    EnvironmentError(diagnostic) =>
      assert_eq(diagnostic.kind, EnvironmentContextMismatch)
  } noraise {
    _ => fail("expected context mismatch")
  }
}

///|
test "environment interns type-variable spellings across frozen and user symbols" {
  let context = @identity.CompilationContext::new()
  let environment = @environment.Environment::new(context)
  let origin = @identity.Origin::user(b"a", None, [])
  let snapshot_variable = @logic.TyVarSymbol::new(context, b"a", origin)
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    @identity.Origin::user(b"box", None, []),
    [snapshot_variable],
    None,
  )
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Types"),
    env_name(b"Types"),
  )
  builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      @identity.Origin::user(b"box", None, []),
      [type_symbol],
      None,
    ),
    None,
  )
  environment.register_theory(builder.close(), true, None)
  let reused = environment.intern_type_variable(
    context,
    b"a",
    @identity.Origin::user(b"different source occurrence", None, []),
    None,
  )
  assert_true(reused == snapshot_variable)
  let fresh = environment.intern_type_variable(context, b"b", origin, None)
  assert_true(
    environment.intern_type_variable(context, b"b", origin, None) == fresh,
  )
}

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
test "environment interns source type variables without capturing builtins" {
  let context = @identity.CompilationContext::new()
  let environment = @environment.Environment::new(context)
  let builtin_origin = @identity.Origin::user(b"a", None, [])
  let builtin_variable = @logic.TyVarSymbol::new(context, b"a", builtin_origin)
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    @identity.Origin::user(b"box", None, []),
    [builtin_variable],
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
  let span = @identity.SourceSpan::new(b"source.mlw", 0, 1, 1L, 0L, 1L, 1L)
  let source_origin = @identity.Origin::user(b"a", Some(span), [])
  let source_variable = environment.intern_type_variable(
    context,
    b"a",
    source_origin,
    Some(span),
  )
  assert_true(source_variable != builtin_variable)
  assert_true(
    environment.intern_type_variable(
      context,
      b"a",
      @identity.Origin::user(b"different source occurrence", Some(span), []),
      Some(span),
    ) ==
    source_variable,
  )
}

///|
test "typed environment owns its context and memoizes successful source loads" {
  let path = @env.LibraryPath::new([b"demo"])
  let provider = @env.SourceProvider::memory(b"embedded", [
    @env.MemorySource::new(path, b"mlw", b"module Demo end"),
  ])
  let environment = @environment.Environment::with_source(provider)
  let other = @environment.Environment::with_source(provider)
  let own_id = environment.compilation_context().fresh_id()
  let other_id = other.compilation_context().fresh_id()
  assert_false(own_id.same_context(other_id))
  let loads = Ref(0)
  let first = environment.read_library(path, (_, _, candidate) => {
    loads.val = loads.val + 1
    assert_eq(candidate.view().contents, b"module Demo end")
    @environment.TypedLibrary::new([], [])
  })
  let second = environment.read_library(path, (_, _, _) => {
    loads.val = loads.val + 1
    @environment.TypedLibrary::new([], [])
  })
  assert_eq(loads.val, 1)
  assert_eq(first.view().theories.length(), second.view().theories.length())
  assert_eq(environment.cached_library_paths().length(), 1)
}

///|
fn cyclic_library_loader(
  _context : @identity.CompilationContext,
  environment : @environment.Environment,
  candidate : @env.SourceCandidate,
) -> @environment.TypedLibrary raise {
  let next = if candidate.view().path.view().segments == [b"a"] {
    @env.LibraryPath::new([b"b"])
  } else {
    @env.LibraryPath::new([b"a"])
  }
  environment.read_library(next, cyclic_library_loader)
}

///|
test "typed environment propagates recursive library cycle diagnostics" {
  let a = @env.LibraryPath::new([b"a"])
  let b = @env.LibraryPath::new([b"b"])
  let environment = @environment.Environment::with_source(
    @env.SourceProvider::memory(b"embedded", [
      @env.MemorySource::new(a, b"mlw", b"use b"),
      @env.MemorySource::new(b, b"mlw", b"use a"),
    ]),
  )
  try environment.read_library(a, cyclic_library_loader) catch {
    @env.SourceError(diagnostic) => {
      assert_eq(diagnostic.kind, CircularDependency)
      assert_eq(diagnostic.dependency_chain, [[b"a"], [b"b"], [b"a"]])
    }
    _ => fail("expected a source error")
  } noraise {
    _ => fail("expected a circular dependency")
  }
  assert_true(environment.cached_library_paths().is_empty())
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn source_environment_with_prelude(
  context : @identity.CompilationContext,
  provider : @env.SourceProvider,
) -> @environment.Environment raise {
  @environment.Environment::with_source_in_context(context, provider)
}

///|
test "lazy MLW loader preserves library path and reuses typed file cache" {
  let context = @identity.CompilationContext::new()
  let path = @env.LibraryPath::new([b"demo"])
  let provider = @env.SourceProvider::memory(b"embedded", [
    @env.MemorySource::new(
      path, b"mlw", b"theory Example\n  lemma truth: true\nend\n",
    ),
  ])
  let environment = source_environment_with_prelude(context, provider)
  let library = environment.read_library(path, @why3_elab.load_mlw_library)
  guard library.find_theory(b"Example") is Some(theory) else {
    fail("typed source library has no Example theory")
  }
  assert_eq(theory.key().view().path, [b"demo"])
  assert_true(
    environment
    .resolve_theory(@theory.TheoryKey::new([b"demo"], b"Example"), None)
    .context_anchor() ==
    theory.context_anchor(),
  )
  let cached = environment.read_library(path, (_, _, _) => {
    fail("cached library unexpectedly invoked its loader")
  })
  assert_true(
    cached.find_theory(b"Example") is Some(found) &&
    found.context_anchor() == theory.context_anchor(),
  )
}

///|
test "lazy MLW loader resolves same-file units and recursive libraries" {
  let context = @identity.CompilationContext::new()
  let dependency_path = @env.LibraryPath::new([b"dep"])
  let root_path = @env.LibraryPath::new([b"root"])
  let provider = @env.SourceProvider::memory(b"embedded", [
    @env.MemorySource::new(
      dependency_path, b"mlw", b"theory Dependency\n  predicate p\n  axiom hp: p\nend\n",
    ),
    @env.MemorySource::new(
      root_path,
      b"mlw",
      b"theory First\n" +
      b"  predicate local\n" +
      b"end\n" +
      b"theory Second\n" +
      b"  use First\n" +
      b"  use dep.Dependency\n" +
      b"  lemma imported: local -> p -> p\n" +
      b"end\n",
    ),
  ])
  let environment = source_environment_with_prelude(context, provider)
  let root = environment.read_library(root_path, @why3_elab.load_mlw_library)
  guard root.find_theory(b"Second") is Some(second) else {
    fail("root library has no Second theory")
  }
  assert_eq(second.key().view().path, [b"root"])
  assert_true(
    environment
    .resolve_theory(@theory.TheoryKey::new([b"dep"], b"Dependency"), None)
    .key() ==
    @theory.TheoryKey::new([b"dep"], b"Dependency"),
  )
  let cached = environment.cached_library_paths()
  assert_eq(cached.length(), 2)
  assert_eq(cached[0].view().segments, [b"dep"])
  assert_eq(cached[1].view().segments, [b"root"])
}

///|
test "recursive MLW imports report a source cycle without partial publication" {
  let context = @identity.CompilationContext::new()
  let a = @env.LibraryPath::new([b"a"])
  let b = @env.LibraryPath::new([b"b"])
  let environment = source_environment_with_prelude(
    context,
    @env.SourceProvider::memory(b"embedded", [
      @env.MemorySource::new(a, b"mlw", b"theory A\n  use b.B\nend\n"),
      @env.MemorySource::new(b, b"mlw", b"theory B\n  use a.A\nend\n"),
    ]),
  )
  try environment.read_library(a, @why3_elab.load_mlw_library) catch {
    @why3_elab.ElabError(diagnostic) =>
      assert_true(
        diagnostic.kind is @why3_elab.SourceFailure(@env.CircularDependency),
      )
    _ => fail("expected an elaboration source error")
  } noraise {
    _ => fail("expected a circular dependency")
  }
  assert_true(environment.cached_library_paths().is_empty())
  try
    ignore(
      environment.resolve_theory(@theory.TheoryKey::new([b"a"], b"A"), None),
    )
  catch {
    @environment.EnvironmentError(diagnostic) =>
      assert_eq(diagnostic.kind, ResolveError)
    _ => fail("expected an environment resolution error")
  } noraise {
    _ => fail("failed library leaked a partially registered theory")
  }
}

///|
test "lazy loader elaborates the polymorphic reference library from source" {
  let context = @identity.CompilationContext::new()
  let path = @env.LibraryPath::new([b"ref"])
  let provider = @env.SourceProvider::memory(b"embedded", [
    @env.MemorySource::new(
      path,
      b"mlw",
      b"module Ref\n" +
      b"  use export why3.Ref.Ref\n" +
      b"  let function (!) (r : ref 'a) = r.contents\n" +
      b"  let (:=) (ref r : 'a) (v : 'a)\n" +
      b"    ensures { r = v }\n" +
      b"  = r <- v\n" +
      b"end\n",
    ),
  ])
  let environment = source_environment_with_prelude(context, provider)
  let library = environment.read_library(path, @why3_elab.load_mlw_library) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("reference library elaboration failed: \{diagnostic.message}")
    _ => fail("reference library raised an unexpected error family")
  }
  guard library.find_module(b"Ref") is Some(reference_module) else {
    fail("typed source library has no Ref module")
  }
  let declarations : Array[@mlw.ProgramDeclaration] = []
  for item in reference_module.view().items {
    if item is Udecl(declaration) {
      declarations.push(declaration)
    }
  }
  guard declarations
    is [
      PDlet(dereference, Cfun(dereference_cty, Some(_)), [_], _),
      PDlet(assignment, Cfun(assignment_cty, Some(_)), [], _),
    ] else {
    fail("source Ref routines did not elaborate")
  }
  assert_eq(dereference.view().name, b"prefix !")
  assert_true(dereference.kind() is @mlw.RKfunc)
  assert_true(
    dereference_cty.view().arguments[0].view().ity.view() is ItyReg(_),
  )
  assert_true(dereference_cty.view().result.view() is ItyVar(_))
  assert_eq(assignment.view().name, b"infix :=")
  assert_true(
    assignment_cty.view().arguments is [reference, value] &&
    reference.view().ity.view() is ItyReg(region) &&
    region.view().symbol.view().logic_type.name() == b"ref" &&
    region.view().arguments is [content] &&
    value.view().ity == content,
  )
  assert_true(
    assignment_cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"tuple0",
  )
}

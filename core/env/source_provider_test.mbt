// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn library_path(parts : ArrayView[Bytes]) -> @env.LibraryPath raise {
  @env.LibraryPath::new(parts)
}

///|
test "source provider returns every candidate in loadpath and extension order" {
  let path = library_path([b"int"])
  let first = @env.SourceProvider::memory(b"/first", [
    @env.MemorySource::new(path, b"why", b"first why"),
    @env.MemorySource::new(path, b"mlw", b"first mlw"),
  ])
  let second = @env.SourceProvider::memory(b"/second", [
    @env.MemorySource::new(path, b"mlw", b"second mlw"),
  ])
  let candidates = @env.SourceProvider::combine([first, second]).candidates(
    path,
    [b"mlw", b"why"],
  )
  assert_eq(candidates.length(), 3)
  assert_eq(candidates[0].view().location, b"/first/int.mlw")
  assert_eq(candidates[1].view().location, b"/first/int.why")
  assert_eq(candidates[2].view().location, b"/second/int.mlw")
}

///|
test "source provider distinguishes missing and ambiguous libraries" {
  let path = library_path([b"list"])
  let provider = @env.SourceProvider::combine([
    @env.SourceProvider::memory(b"/one", [
      @env.MemorySource::new(path, b"mlw", b"one"),
    ]),
    @env.SourceProvider::memory(b"/two", [
      @env.MemorySource::new(path, b"mlw", b"two"),
    ]),
  ])
  try provider.locate(path, [b"mlw"]) catch {
    @env.SourceError(diagnostic) => {
      assert_eq(diagnostic.kind, AmbiguousPath)
      assert_eq(diagnostic.candidates, [b"/one/list.mlw", b"/two/list.mlw"])
    }
  } noraise {
    _ => fail("expected an ambiguous path")
  }
  try provider.locate(library_path([b"missing"]), [b"mlw"]) catch {
    @env.SourceError(diagnostic) => assert_eq(diagnostic.kind, LibraryNotFound)
    _ => fail("expected a source error")
  } noraise {
    _ => fail("expected a missing library")
  }
}

///|
test "library cache detects cycles and clears loading state after errors" {
  let cache : @env.LibraryCache[Int] = @env.LibraryCache::new()
  let a = library_path([b"a"])
  let b = library_path([b"b"])
  try cache.read(a, () => cache.read(b, () => cache.read(a, () => 0))) catch {
    @env.SourceError(diagnostic) => {
      assert_eq(diagnostic.kind, CircularDependency)
      assert_eq(diagnostic.dependency_chain, [[b"a"], [b"b"], [b"a"]])
    }
    _ => fail("expected a source error")
  } noraise {
    _ => fail("expected a circular dependency")
  }
  assert_true(cache.loading_paths().is_empty())
  assert_eq(cache.read(a, () => 7), 7)
  assert_eq(cache.read(a, () => 9), 7)
}

///|
test "builtin registry normalizes empty requests and detects conflicts" {
  let registry : @env.BuiltinRegistry[Int] = @env.BuiltinRegistry::new()
  registry.add(path => if path.view().segments == [] { Some(1) } else { None })
  assert_eq(
    registry.resolve(library_path([]), (left, right) => left == right),
    Some(1),
  )
  registry.add(path => if path.view().segments == [] { Some(2) } else { None })
  try
    ignore(registry.resolve(library_path([]), (left, right) => left == right))
  catch {
    @env.SourceError(diagnostic) => assert_eq(diagnostic.kind, LibraryConflict)
    _ => fail("expected a source error")
  } noraise {
    _ => fail("expected a builtin conflict")
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// Per-language memo table plus an exception-safe loading stack. Values are
/// stored only after the loader succeeds, matching Why3's `read_library`.
struct LibraryCache[T] {
  values : Map[LibraryPath, T]
  loading : Array[LibraryPath]
}

///|
pub fn[T] LibraryCache::new() -> LibraryCache[T] {
  { values: Map([]), loading: [] }
}

///|
pub fn[T] LibraryCache::get(self : LibraryCache[T], path : LibraryPath) -> T? {
  self.values.get(path.normalized_request())
}

///|
pub fn[T] LibraryCache::contains(
  self : LibraryCache[T],
  path : LibraryPath,
) -> Bool {
  self.values.contains(path.normalized_request())
}

///|
pub fn[T] LibraryCache::loading_paths(
  self : LibraryCache[T],
) -> Array[LibraryPath] {
  self.loading.copy()
}

///|
fn[T] LibraryCache::enter(
  self : LibraryCache[T],
  path : LibraryPath,
) -> Unit raise SourceError {
  let path = path.normalized_request()
  let mut cycle_start = -1
  for index, loading in self.loading {
    if loading == path {
      cycle_start = index
      break
    }
  }
  if cycle_start >= 0 {
    let chain : Array[Array[Bytes]] = []
    for index = cycle_start; index < self.loading.length(); index = index + 1 {
      chain.push(self.loading[index].view().segments.to_owned())
    }
    chain.push(path.view().segments.to_owned())
    fail_source(
      CircularDependency,
      path.view().segments,
      [],
      chain,
      "circular library dependency",
    )
  }
  self.loading.push(path)
}

///|
fn[T] LibraryCache::leave(self : LibraryCache[T], path : LibraryPath) -> Unit {
  let normalized = path.normalized_request()
  if self.loading.last() is Some(last) && last == normalized {
    ignore(self.loading.pop())
    return
  }
  for index = self.loading.length() - 1; index >= 0; index = index - 1 {
    if self.loading[index] == normalized {
      ignore(self.loading.remove(index))
      return
    }
  }
}

///|
/// Reads a cached value or computes it once. Recursive reads of the same
/// normalized path fail before invoking the loader.
pub fn[T] LibraryCache::read(
  self : LibraryCache[T],
  path : LibraryPath,
  loader : () -> T raise,
) -> T raise {
  let path = path.normalized_request()
  match self.values.get(path) {
    Some(value) => value
    None => {
      self.enter(path)
      let value = loader() catch {
        error => {
          self.leave(path)
          raise error
        }
      }
      self.leave(path)
      self.values[path] = value
      value
    }
  }
}

///|
pub fn[T] LibraryCache::store(
  self : LibraryCache[T],
  path : LibraryPath,
  value : T,
) -> Unit raise SourceError {
  let path = path.normalized_request()
  if self.values.contains(path) {
    fail_source(
      CacheProtocolError,
      path.view().segments,
      [],
      [],
      "library cache entry is already present",
    )
  }
  self.values[path] = value
}

///|
pub fn[T] LibraryCache::cached_paths(
  self : LibraryCache[T],
) -> Array[LibraryPath] {
  let result = self.values.keys().to_array()
  result.sort_by((left, right) => left.lexical_compare(right))
  result
}

///|
struct BuiltinRegistry[T] {
  providers : Array[(LibraryPath) -> T? raise]
}

///|
pub fn[T] BuiltinRegistry::new() -> BuiltinRegistry[T] {
  { providers: [] }
}

///|
pub fn[T] BuiltinRegistry::add(
  self : BuiltinRegistry[T],
  provider : (LibraryPath) -> T? raise,
) -> Unit {
  self.providers.push(provider)
}

///|
/// Invokes all builtin providers and accepts repeated definitions only when
/// the language layer's identity predicate says they are the same object.
pub fn[T] BuiltinRegistry::resolve(
  self : BuiltinRegistry[T],
  path : LibraryPath,
  equivalent : (T, T) -> Bool,
) -> T? raise {
  let path = path.normalized_request()
  guard path.without_builtin_prefix() is Some(relative) else { return None }
  let mut resolved : T? = None
  for provider in self.providers {
    match provider(relative) {
      None => ()
      Some(value) =>
        match resolved {
          None => resolved = Some(value)
          Some(existing) =>
            if !equivalent(existing, value) {
              fail_source(
                LibraryConflict,
                path.view().segments,
                [],
                [],
                "conflicting definitions for builtin library",
              )
            }
        }
    }
  }
  resolved
}

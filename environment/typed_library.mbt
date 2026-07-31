// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct TypedLibrary {
  theories : Array[(Bytes, @theory.Theory)]
  modules : Array[(Bytes, @mlw.Pmodule)]
}

///|
pub(all) struct TypedLibraryView {
  theories : ArrayView[(Bytes, @theory.Theory)]
  modules : ArrayView[(Bytes, @mlw.Pmodule)]
}

///|
fn[T] duplicate_typed_name(entries : ArrayView[(Bytes, T)]) -> Bytes? {
  for index = 0; index < entries.length(); index = index + 1 {
    for other = index + 1; other < entries.length(); other = other + 1 {
      if entries[index].0 == entries[other].0 {
        return Some(entries[index].0)
      }
    }
  }
  None
}

///|
pub fn TypedLibrary::new(
  theories : ArrayView[(Bytes, @theory.Theory)],
  modules : ArrayView[(Bytes, @mlw.Pmodule)],
) -> TypedLibrary raise EnvironmentError {
  if duplicate_typed_name(theories) is Some(_) {
    fail_environment(
      DuplicateTheory,
      None,
      "typed library defines one theory name twice",
    )
  }
  if duplicate_typed_name(modules) is Some(_) {
    fail_environment(
      DuplicateModule,
      None,
      "typed library defines one module name twice",
    )
  }
  { theories: theories.to_owned(), modules: modules.to_owned() }
}

///|
pub fn TypedLibrary::view(self : TypedLibrary) -> TypedLibraryView {
  { theories: self.theories[:], modules: self.modules[:] }
}

///|
pub fn TypedLibrary::find_theory(
  self : TypedLibrary,
  name : BytesView,
) -> @theory.Theory? {
  for entry in self.theories {
    if entry.0[:] == name {
      return Some(entry.1)
    }
  }
  None
}

///|
pub fn TypedLibrary::find_module(
  self : TypedLibrary,
  name : BytesView,
) -> @mlw.Pmodule? {
  for entry in self.modules {
    if entry.0[:] == name {
      return Some(entry.1)
    }
  }
  None
}

///|
/// Atomically publishes every theory/module in one successfully elaborated
/// file. All conflicts are checked before any environment map is mutated.
pub fn Environment::register_typed_library(
  self : Environment,
  library : TypedLibrary,
  user_visible : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  let view = library.view()
  for entry in view.theories {
    let theory = entry.1
    self.require_context(theory.context_anchor(), span)
    let key = theory.key()
    if self.theories.contains(key) ||
      (user_visible && self.theory_aliases.contains(key)) {
      fail_environment(
        DuplicateTheory,
        span,
        "theory key is already registered",
      )
    }
  }
  for entry in view.modules {
    let pmodule = entry.1
    self.require_context(pmodule.context_anchor(), span)
    let key = pmodule.key()
    if self.modules.contains(key) ||
      (user_visible && self.module_aliases.contains(key)) {
      fail_environment(
        DuplicateModule,
        span,
        "module key is already registered",
      )
    }
  }
  for entry in view.theories {
    self.register_theory(entry.1, user_visible, span)
  }
  for entry in view.modules {
    self.register_module(entry.1, user_visible, span)
  }
}

///|
fn TypedLibrary::equivalent(self : TypedLibrary, other : TypedLibrary) -> Bool {
  if self.theories.length() != other.theories.length() ||
    self.modules.length() != other.modules.length() {
    return false
  }
  for entry in self.theories {
    guard other.find_theory(entry.0) is Some(candidate) else { return false }
    if candidate.context_anchor() != entry.1.context_anchor() ||
      candidate.key() != entry.1.key() {
      return false
    }
  }
  for entry in self.modules {
    guard other.find_module(entry.0) is Some(candidate) else { return false }
    if candidate.context_anchor() != entry.1.context_anchor() ||
      candidate.key() != entry.1.key() {
      return false
    }
  }
  true
}

///|
/// Adds one lazy builtin source. The path passed to `provider` has the leading
/// `why3` component removed, as in Why3's `Env.add_builtin`.
pub fn Environment::add_builtin(
  self : Environment,
  provider : (@env.LibraryPath) -> TypedLibrary? raise,
) -> Unit {
  self.builtins.add(provider)
}

///|
/// Loads and memoizes one typed library. Non-builtin sources are selected by
/// the core provider before `loader` parses and elaborates them. The cache
/// entry is committed only after successful elaboration.
pub fn Environment::read_library(
  self : Environment,
  path : @env.LibraryPath,
  loader : (@identity.CompilationContext, Environment, @env.SourceCandidate) -> TypedLibrary raise,
) -> TypedLibrary raise {
  self.typed_libraries.read(path, () => {
    let normalized = path.normalized_request()
    if normalized.is_builtin() {
      match self.language_builtin_library(normalized) {
        Some(library) => library
        None =>
          match
            self.builtins.resolve(normalized, (left, right) => {
              left.equivalent(right)
            }) {
            Some(library) => library
            None =>
              match self.tuple_builtin_library(normalized) {
                Some(library) => library
                None =>
                  match self.reference_builtin_library(normalized) {
                    Some(library) => library
                    None =>
                      match self.high_order_builtin_library(normalized) {
                        Some(library) => library
                        None =>
                          match self.well_founded_builtin_library(normalized) {
                            Some(library) => library
                            None =>
                              raise @env.SourceError({
                                kind: @env.LibraryNotFound,
                                path: normalized.view().segments.to_owned(),
                                candidates: [],
                                dependency_chain: [],
                                message: "library file not found",
                              })
                          }
                      }
                  }
              }
          }
      }
    } else {
      let candidate = self.source_environment.locate_library(normalized)
      loader(self.context, self, candidate)
    }
  })
}

///|
pub fn Environment::cached_library_paths(
  self : Environment,
) -> Array[@env.LibraryPath] {
  self.typed_libraries.cached_paths()
}

///|
pub fn Environment::read_theory(
  self : Environment,
  path : @env.LibraryPath,
  name : BytesView,
  loader : (@identity.CompilationContext, Environment, @env.SourceCandidate) -> TypedLibrary raise,
  span : @identity.SourceSpan?,
) -> @theory.Theory raise {
  let effective_path = if path.is_empty() {
    let segments = [b"why3", name.to_owned()]
    @env.LibraryPath::new(segments)
  } else {
    path
  }
  guard self.read_library(effective_path, loader).find_theory(name)
    is Some(theory) else {
    fail_environment(ResolveError, span, "theory not found in library")
  }
  theory
}

///|
pub fn Environment::read_module(
  self : Environment,
  path : @env.LibraryPath,
  name : BytesView,
  loader : (@identity.CompilationContext, Environment, @env.SourceCandidate) -> TypedLibrary raise,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule raise {
  let effective_path = if path.is_empty() {
    let segments = [b"why3", name.to_owned()]
    @env.LibraryPath::new(segments)
  } else {
    path
  }
  guard self.read_library(effective_path, loader).find_module(name)
    is Some(pmodule) else {
    fail_environment(ResolveError, span, "module not found in library")
  }
  pmodule
}

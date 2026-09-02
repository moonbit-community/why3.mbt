// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// The MLW-independent half of an environment. Every instance owns a fresh
/// compilation context; semantic language layers keep their typed caches
/// separately and share this context.
struct CoreEnvironment {
  context : @identity.CompilationContext
  provider : SourceProvider
  extensions : Array[Bytes]
}

///|
pub fn CoreEnvironment::empty(
  context : @identity.CompilationContext,
) -> CoreEnvironment {
  { context, provider: SourceProvider::empty(), extensions: [b"mlw", b"why"] }
}

///|
pub fn CoreEnvironment::new(
  provider : SourceProvider,
  extensions? : ArrayView[Bytes] = [b"mlw", b"why"],
) -> CoreEnvironment raise SourceError {
  CoreEnvironment::with_context(
    @identity.CompilationContext::new(),
    provider,
    extensions~,
  )
}

///|
/// Compatibility constructor for language layers that already own a context.
/// New typed environments should normally use `CoreEnvironment::new`.
pub fn CoreEnvironment::with_context(
  context : @identity.CompilationContext,
  provider : SourceProvider,
  extensions? : ArrayView[Bytes] = [b"mlw", b"why"],
) -> CoreEnvironment raise SourceError {
  let copied = extensions.to_owned()
  for extension in copied {
    validate_extension(extension, [])
  }
  { context, provider, extensions: copied }
}

///|
pub fn CoreEnvironment::compilation_context(
  self : CoreEnvironment,
) -> @identity.CompilationContext {
  self.context
}

///|
pub fn CoreEnvironment::source_provider(
  self : CoreEnvironment,
) -> SourceProvider {
  self.provider
}

///|
pub fn CoreEnvironment::extensions(self : CoreEnvironment) -> ArrayView[Bytes] {
  self.extensions[:]
}

///|
pub fn CoreEnvironment::locate_library(
  self : CoreEnvironment,
  path : LibraryPath,
) -> SourceCandidate raise SourceError {
  self.provider.locate(path, self.extensions)
}

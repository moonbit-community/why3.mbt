// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum SourceErrorKind {
  InvalidLibraryPath
  LibraryNotFound
  AmbiguousPath
  CircularDependency
  LibraryConflict
  InvalidExtension
  CacheProtocolError
} derive(Eq, Debug)

///|
pub(all) struct SourceDiagnostic {
  kind : SourceErrorKind
  path : Array[Bytes]
  candidates : Array[Bytes]
  dependency_chain : Array[Array[Bytes]]
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror SourceError {
  SourceError(SourceDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_source(
  kind : SourceErrorKind,
  path : ArrayView[Bytes],
  candidates : ArrayView[Bytes],
  dependency_chain : ArrayView[Array[Bytes]],
  message : String,
) -> A raise SourceError {
  raise SourceError({
    kind,
    path: path.to_owned(),
    candidates: candidates.to_owned(),
    dependency_chain: dependency_chain.to_owned(),
    message,
  })
}

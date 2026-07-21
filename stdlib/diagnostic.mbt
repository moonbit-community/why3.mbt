// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum SnapshotErrorKind {
  PayloadLengthMismatch
  PayloadDigestMismatch
  InvalidUtf8
  InvalidJson
  SchemaMismatch
  MalformedSnapshot
  UnknownReference
  DuplicateCatalogEntry
  UnsupportedSnapshotVariant
  SemanticInvariantFailure
} derive(Eq, Debug)

///|
pub(all) struct SnapshotDiagnostic {
  kind : SnapshotErrorKind
  path : String
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror SnapshotError {
  SnapshotError(SnapshotDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_snapshot(
  kind : SnapshotErrorKind,
  path : String,
  message : String,
) -> A raise SnapshotError {
  raise SnapshotError({ kind, path, message })
}

///|
pub(all) enum BindErrorKind {
  MissingSymbol
  SymbolDigestMismatch
  SymbolKindMismatch
  CatalogContextMismatch
} derive(Eq, Debug)

///|
pub(all) struct BindDiagnostic {
  kind : BindErrorKind
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror BindError {
  BindError(BindDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_bind(kind : BindErrorKind, message : String) -> A raise BindError {
  raise BindError({ kind, message })
}

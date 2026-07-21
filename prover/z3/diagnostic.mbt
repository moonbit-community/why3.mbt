// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum BindErrorKind {
  InvalidProfile
  MissingSymbol
  SymbolDigestMismatch
  SymbolKindMismatch
  ContextMismatch
  InvalidTask
  UnsupportedTransformInput
  ResidualTypeVariable
  ResidualEpsilon
  UnsupportedDatatype
} derive(Eq, Debug)

///|
pub(all) struct BindDiagnostic {
  kind : BindErrorKind
  path : String
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror BindError {
  BindError(BindDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_bind(
  kind : BindErrorKind,
  path : String,
  message : String,
) -> A raise BindError {
  raise BindError({ kind, path, message })
}

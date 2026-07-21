// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum PrinterErrorKind {
  ContextMismatch
  InvalidTask
  InvalidSyntaxMeta
  InvalidSyntaxTemplate
  ResidualTypeVariable
  UnsupportedType
  UnsupportedTerm
  UnsupportedDeclaration
  UnsupportedDatatype
  MissingBuiltinSyntax
  InvalidIdentifierOccurrence
  InvalidSmtToken
} derive(Eq, Debug)

///|
pub(all) struct PrinterDiagnostic {
  kind : PrinterErrorKind
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror PrinterError {
  PrinterError(PrinterDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_printer(
  kind : PrinterErrorKind,
  message : String,
) -> A raise PrinterError {
  raise PrinterError({ kind, message })
}

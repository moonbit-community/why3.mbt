// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum VcErrorKind {
  ContextMismatch
  UnsupportedControlAttribute
  UnsupportedComputation
  InvariantFailure
} derive(Eq, Debug)

///|
pub(all) struct VcDiagnostic {
  kind : VcErrorKind
  span : @identity.SourceSpan?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror VcError {
  VcError(VcDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_vc(
  kind : VcErrorKind,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise VcError {
  raise VcError({ kind, span, message })
}

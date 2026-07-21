// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum EnvironmentErrorKind {
  DuplicateTheory
  DuplicateModule
  EnvironmentContextMismatch
  ResolveError
  DriverOnlyTheory
} derive(Eq, Debug)

///|
pub(all) struct EnvironmentDiagnostic {
  kind : EnvironmentErrorKind
  span : @identity.SourceSpan?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror EnvironmentError {
  EnvironmentError(EnvironmentDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_environment(
  kind : EnvironmentErrorKind,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise EnvironmentError {
  raise EnvironmentError({ kind, span, message })
}

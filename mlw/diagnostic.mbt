// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum MlwErrorKind {
  MlwContextMismatch
  SnapshotProgramOriginRequired
  UnsupportedProgramType
  UnsupportedEffect
  InvalidComputationType
  DuplicateProgramName
  AmbiguousProgramName
  UnboundProgramName
  InvalidProgramDeclaration
  ProgramModuleBuilderSealed
} derive(Eq, Debug)

///|
pub(all) struct MlwDiagnostic {
  kind : MlwErrorKind
  span : @identity.SourceSpan?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror MlwError {
  MlwError(MlwDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_mlw(
  kind : MlwErrorKind,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise MlwError {
  raise MlwError({ kind, span, message })
}

///|
fn require_mlw_context(
  anchor : @identity.SemanticId,
  id : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if !anchor.same_context(id) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "program objects belong to different contexts",
    )
  }
}

///|
fn require_snapshot_program_origin(
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if !(origin.kind().view() is SnapshotKind) {
    fail_mlw(
      SnapshotProgramOriginRequired,
      span,
      "program symbol requires trusted snapshot provenance",
    )
  }
}

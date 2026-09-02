// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum MlwErrorKind {
  MlwContextMismatch
  UnsupportedProgramType
  BadProgramTypeArity
  BadRegionArity
  InvalidRegion
  InvalidProgramTypeInvariant
  ProgramTypeMismatch
  UnboundProgramTypeVariable
  UnboundRegion
  InvalidExceptionType
  InvalidProgramMask
  InvalidOldSnapshot
  UnboundSpecificationVariable
  InvalidEffect
  DuplicateEffectField
  AssignSnapshot
  AssignPrivate
  WriteImmutable
  IllegalAssignment
  IllegalUpdate
  IllegalSnapshot
  IllegalAlias
  ImpureVariable
  StaleVariable
  BadGhostWrite
  GhostDivergence
  UnsupportedEffect
  InvalidComputationType
  DuplicateProgramName
  AmbiguousProgramName
  UnboundProgramName
  InvalidProgramDeclaration
  ProgramModuleBuilderSealed
  NoOpenedProgramNamespace
  UnsupportedProgramInterfaceUnit
  ProgramInterfaceSymbolNotFound
  ProgramInterfaceMismatch
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

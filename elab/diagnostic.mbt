// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ElabStage {
  DeclarationElaboration
  PureTyping
  ProgramTyping
  FileRegistration
} derive(Eq, Debug)

///|
pub(all) enum ElabInputErrorKind {
  InvalidBinder
  InvalidDeclaration
  InvalidPattern
  InvalidSpecification
  InvalidTypeDeclaration
  InvalidUnit
} derive(Eq, Debug)

///|
pub(all) enum ElabErrorKind {
  InvalidInput(ElabInputErrorKind)
  TypeFailure(@logic.TypeErrorKind)
  TheoryFailure(@theory.TheoryErrorKind)
  EnvironmentFailure(@environment.EnvironmentErrorKind)
  SourceFailure(@env.SourceErrorKind)
  ProgramFailure(@mlw.MlwErrorKind)
} derive(Eq, Debug)

///|
pub(all) struct ElabDiagnostic {
  kind : ElabErrorKind
  stage : ElabStage
  span : @identity.SourceSpan?
  actual_type : Bytes?
  expected_type : Bytes?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror ElabError {
  ElabError(ElabDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_invalid_input(
  kind : ElabInputErrorKind,
  stage : ElabStage,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise ElabError {
  raise ElabError({
    kind: InvalidInput(kind),
    stage,
    span,
    actual_type: None,
    expected_type: None,
    message,
  })
}

///|
fn type_failure_diagnostic(
  diagnostic : @logic.TypeDiagnostic,
) -> ElabDiagnostic {
  {
    kind: TypeFailure(diagnostic.kind),
    stage: PureTyping,
    span: diagnostic.span,
    actual_type: diagnostic.actual_type,
    expected_type: diagnostic.expected_type,
    message: diagnostic.message,
  }
}

///|
fn theory_failure_diagnostic(
  diagnostic : @theory.TheoryDiagnostic,
) -> ElabDiagnostic {
  {
    kind: TheoryFailure(diagnostic.kind),
    stage: DeclarationElaboration,
    span: diagnostic.span,
    actual_type: None,
    expected_type: None,
    message: diagnostic.message,
  }
}

///|
fn environment_failure_diagnostic(
  diagnostic : @environment.EnvironmentDiagnostic,
  stage : ElabStage,
) -> ElabDiagnostic {
  {
    kind: EnvironmentFailure(diagnostic.kind),
    stage,
    span: diagnostic.span,
    actual_type: None,
    expected_type: None,
    message: diagnostic.message,
  }
}

///|
fn program_failure_diagnostic(
  diagnostic : @mlw.MlwDiagnostic,
) -> ElabDiagnostic {
  {
    kind: ProgramFailure(diagnostic.kind),
    stage: ProgramTyping,
    span: diagnostic.span,
    actual_type: None,
    expected_type: None,
    message: diagnostic.message,
  }
}

///|
fn source_failure_diagnostic(
  diagnostic : @env.SourceDiagnostic,
  stage : ElabStage,
) -> ElabDiagnostic {
  {
    kind: SourceFailure(diagnostic.kind),
    stage,
    span: None,
    actual_type: None,
    expected_type: None,
    message: diagnostic.message,
  }
}

///|
fn[A] normalize_elaboration_errors(
  action : () -> A raise,
  environment_stage : ElabStage,
) -> A raise ElabError {
  action() catch {
    @logic.TypeError(diagnostic) =>
      raise ElabError(type_failure_diagnostic(diagnostic))
    @theory.TheoryError(diagnostic) =>
      raise ElabError(theory_failure_diagnostic(diagnostic))
    @environment.EnvironmentError(diagnostic) =>
      raise ElabError(
        environment_failure_diagnostic(diagnostic, environment_stage),
      )
    @env.SourceError(diagnostic) =>
      raise ElabError(source_failure_diagnostic(diagnostic, environment_stage))
    @mlw.MlwError(diagnostic) =>
      raise ElabError(program_failure_diagnostic(diagnostic))
    ElabError(diagnostic) => raise ElabError(diagnostic)
    _ => abort("unexpected elaboration error escaped a typed boundary")
  }
}

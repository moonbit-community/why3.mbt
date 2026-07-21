// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ElabStage {
  FeatureClassification
  DeclarationElaboration
  PureTyping
  ProgramTyping
  FileRegistration
} derive(Eq, Debug)

///|
pub(all) enum UnsupportedFeature {
  AbstractRoutineShape
  AlgebraicData
  CheckAssertion
  Clone
  ControlAttribute
  Datatype
  DestructuringPattern
  DriverOnlyTheory
  DriverOnlyType
  Epsilon
  Exception
  ExternalOrDriverOnlyImport
  Ghost
  HigherOrder
  HigherOrderApplication
  Inductive
  Lambda
  LocalRoutine
  Loop
  NestedUnsupportedExpression
  NestedUnsupportedTerm
  OldAt
  PrivateType
  ProgramExpression
  ProgramRoutineShape
  ProofControlConnective
  RecordOrInvariant
  Recursion
  RecursiveOrHigherOrderLogic
  Reference
  RoutineKind
  StringLiteral
  TupleExpression
  TupleTerm
  TupleType
  TypeDeclarationShape
  TypePurification
  TypeVisibilityShape
  UserMeta
} derive(Eq, Debug)

///|
pub(all) enum ElabErrorKind {
  Unsupported(UnsupportedFeature)
  TypeFailure(@logic.TypeErrorKind)
  TheoryFailure(@theory.TheoryErrorKind)
  EnvironmentFailure(@environment.EnvironmentErrorKind)
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
fn[A] fail_unsupported(
  feature : UnsupportedFeature,
  stage : ElabStage,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise ElabError {
  raise ElabError({
    kind: Unsupported(feature),
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
    @mlw.MlwError(diagnostic) =>
      raise ElabError(program_failure_diagnostic(diagnostic))
    ElabError(diagnostic) => raise ElabError(diagnostic)
    _ => abort("unexpected elaboration error escaped a typed boundary")
  }
}

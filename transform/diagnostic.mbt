// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum TransformErrorKind {
  ContextMismatch
  InvalidTask
  UnsupportedStructure
  InvariantFailure
} derive(Eq, Debug)

///|
pub(all) struct TransformDiagnostic {
  kind : TransformErrorKind
  stage : @identity.GeneratedStage
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror TransformError {
  TransformError(TransformDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_transform(
  kind : TransformErrorKind,
  stage : @identity.GeneratedStage,
  message : String,
) -> A raise TransformError {
  raise TransformError({ kind, stage, message })
}

///|
fn require_task_context(
  context : @identity.CompilationContext,
  task : @theory.Task,
  stage : @identity.GeneratedStage,
) -> Unit raise TransformError {
  if !context.contains(task.context_anchor()) {
    fail_transform(
      ContextMismatch,
      stage,
      "transform and task belong to different compilation contexts",
    )
  }
}

///|
fn checked_task(
  anchor : @identity.SemanticId,
  items : ArrayView[@theory.TheoryItem],
  stage : @identity.GeneratedStage,
) -> @theory.Task raise TransformError {
  @theory.Task::trusted_new(anchor, items, None) catch {
    _ =>
      fail_transform(InvalidTask, stage, "transform violated Task invariants")
  }
}

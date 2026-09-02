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
  original : @theory.Task,
  items : ArrayView[@theory.TheoryItem],
  stage : @identity.GeneratedStage,
) -> @theory.Task raise TransformError {
  // Why3's Task.add_decl silently ignores a declaration when one of its
  // introduced identifiers is already known.  This matters for transforms
  // such as eliminate_epsilon: two occurrences of the same cached canonical
  // closure can yield the same parameter/axiom pair more than once.
  let normalized : Array[@theory.TheoryItem] = []
  let introduced : Map[@identity.SemanticId, Unit] = Map([])
  for item in items {
    if item is TheoryDecl(declaration) {
      let symbols = declaration.introduced_symbols()
      if symbols.any(symbol => introduced.contains(symbol.semantic_id())) {
        continue
      }
      for symbol in symbols {
        introduced[symbol.semantic_id()] = ()
      }
    }
    normalized.push(item)
  }
  propagate_persistent_declarations(original, normalized)
  @theory.Task::trusted_new_with_dependencies(
    original.context_anchor(),
    normalized,
    original.dependency_theories(),
    None,
  ) catch {
    _ =>
      fail_transform(InvalidTask, stage, "transform violated Task invariants")
  }
}

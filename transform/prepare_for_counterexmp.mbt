// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub fn prepare_for_counterexmp(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  require_task_context(context, task, stage)
  if task_has_meta(task, b"get_counterexmp") {
    fail_transform(
      UnsupportedStructure,
      stage,
      "counterexample preparation is outside the no-counterexample profile",
    )
  }
  task
}

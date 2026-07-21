// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn task_uses_theory(
  items : ArrayView[@theory.TheoryItem],
  key : @theory.TheoryKey,
) -> Bool {
  for item in items {
    match item {
      TheoryUse(used) => if used == key { return true }
      TheoryClone(witness) => if witness.view().source == key { return true }
      TheoryDecl(_) | TheoryMeta(_) => ()
    }
  }
  false
}

///|
fn Z3Profile::printer_preludes(
  self : Z3Profile,
  task : @theory.Task,
) -> Array[Bytes] {
  let result = self.preludes.copy()
  let seen : Map[@theory.TheoryKey, Unit] = Map([])
  for item in task.view().items {
    let key = match item {
      TheoryUse(key) => Some(key)
      TheoryClone(witness) => Some(witness.view().source)
      TheoryDecl(_) | TheoryMeta(_) => None
    }
    guard key is Some(key) && !seen.contains(key) else { continue }
    seen[key] = ()
    for group in self.theory_preludes {
      if group.theory_key == key {
        for value in group.values {
          result.push(value)
        }
        break
      }
    }
  }
  result
}

///|
pub fn Z3Profile::printer_query(
  self : Z3Profile,
  task : @theory.Task,
) -> @smtv2.SmtV26Query raise BindError {
  if !self.anchor.same_context(task.context_anchor()) {
    fail_bind(
      ContextMismatch,
      "$.task",
      "profile and task belong to different contexts",
    )
  }
  @smtv2.SmtV26Query::new(self.anchor, self.printer_preludes(task))
}

///|
pub fn Z3Profile::driver_update(
  self : Z3Profile,
  task : @theory.Task,
) -> @theory.Task raise BindError {
  if !self.anchor.same_context(task.context_anchor()) {
    fail_bind(
      ContextMismatch,
      "$.task",
      "profile and task belong to different contexts",
    )
  }
  let original = task.view().items
  if original.is_empty() {
    fail_bind(InvalidTask, "$.task", "task is empty")
  }
  let result : Array[@theory.TheoryItem] = []
  for index = 0; index + 1 < original.length(); index = index + 1 {
    result.push(original[index])
  }
  for group in self.meta_groups {
    if task_uses_theory(original, group.theory_key) {
      for entry in group.entries {
        result.push(TheoryMeta(entry.meta))
      }
    }
  }
  result.push(original[original.length() - 1])
  @theory.Task::trusted_new(self.anchor, result, None) catch {
    _ =>
      fail_bind(InvalidTask, "$.task", "driver update violated task invariants")
  }
}

///|
pub fn Z3Profile::command(self : Z3Profile) -> Z3CommandTemplate {
  self.command
}

///|
pub fn Z3Profile::checkpoint_sequence(
  self : Z3Profile,
  polymorphic : Bool,
) -> ArrayView[Bytes] {
  if polymorphic {
    self.polymorphic_checkpoints[:]
  } else {
    self.monomorphic_checkpoints[:]
  }
}

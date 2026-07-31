// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

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
  let applicable : Array[(TypedMetaGroup, @theory.Theory)] = []
  for group in self.meta_groups {
    match task.referenced_theory(group.theory_key) {
      Some(source) => applicable.push((group, source))
      None => ()
    }
  }
  applicable.sort_by((left, right) => {
    left.1
    .context_anchor()
    .local_id()
    .compare(right.1.context_anchor().local_id())
  })
  for entry in applicable {
    let group = entry.0
    let source = entry.1
    for declaration in task.clone_history(source).view().tds_set {
      match declaration {
        TheoryUse(_) =>
          for entry in group.entries {
            result.push(TheoryMeta(entry.meta))
          }
        TheoryClone(witness) =>
          for entry in group.entries {
            let cloned = entry.meta.clone_through(source, witness, None) catch {
              _ =>
                fail_bind(InvalidTask, "$.task", "driver meta cloning failed")
            }
            match cloned {
              Some(meta) => result.push(TheoryMeta(meta))
              None => ()
            }
          }
        TheoryDecl(_) | TheoryMeta(_) => ()
      }
    }
  }
  result.push(original[original.length() - 1])
  @theory.Task::trusted_new_with_dependencies(
    self.anchor,
    result,
    task.dependency_theories(),
    None,
  ) catch {
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

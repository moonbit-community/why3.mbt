// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct Task {
  anchor : @identity.SemanticId
  items : Array[TheoryItem]
}

///|
pub(all) struct TaskView {
  items : ArrayView[TheoryItem]
}

///|
pub fn Task::context_anchor(self : Task) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn Task::view(self : Task) -> TaskView {
  { items: self.items[:] }
}

///|
fn declaration_is_goal(declaration : @logic.Decl) -> Bool {
  declaration.view() is Dprop(Pgoal, _, _)
}

///|
priv struct TaskAccumulator {
  context : @identity.CompilationContext
  items : Array[TheoryItem]
  seen_symbols : Map[@identity.SemanticId, Unit]
  seen_uses : Map[TheoryKey, Unit]
}

///|
fn TaskAccumulator::new(
  context : @identity.CompilationContext,
) -> TaskAccumulator {
  { context, items: [], seen_symbols: Map([]), seen_uses: Map([]) }
}

///|
fn TaskAccumulator::add_declaration(
  self : TaskAccumulator,
  declaration : @logic.Decl,
) -> Unit {
  let introduced = declaration.introduced_symbols()
  if introduced.any(symbol => self.seen_symbols.contains(symbol.semantic_id())) {
    return
  }
  for symbol in introduced {
    self.seen_symbols[symbol.semantic_id()] = ()
  }
  self.items.push(TheoryDecl(declaration))
}

///|
fn TaskAccumulator::add_imported_declaration(
  self : TaskAccumulator,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  match declaration.view() {
    Dprop(Plemma, _, _) =>
      self.add_declaration(
        declaration.reclassify_proposition(self.context, Paxiom, span),
      )
    Dprop(Pgoal, _, _) => ()
    _ => self.add_declaration(declaration)
  }
}

///|
fn TaskAccumulator::flatten_use(
  self : TaskAccumulator,
  theory : Theory,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let key = theory.key
  if self.seen_uses.contains(key) {
    return
  }
  self.seen_uses[key] = ()
  for item in theory.items {
    match item {
      TheoryDecl(declaration) =>
        self.add_imported_declaration(declaration, span)
      TheoryUse(used_key) =>
        self.flatten_use(theory.used_theory(used_key), span)
      TheoryClone(witness) => self.items.push(TheoryClone(witness))
      TheoryMeta(meta) => self.items.push(TheoryMeta(meta))
    }
  }
  self.items.push(TheoryUse(key))
}

///|
pub fn Task::trusted_new(
  anchor : @identity.SemanticId,
  items : ArrayView[TheoryItem],
  span : @identity.SourceSpan?,
) -> Task raise TheoryError {
  let mut goals = 0
  for index, item in items {
    if item is TheoryDecl(declaration) && declaration_is_goal(declaration) {
      goals = goals + 1
      if index + 1 != items.length() {
        fail_theory(GoalNotLast, span, "task goal must be the final item")
      }
    }
  }
  if goals == 0 {
    fail_theory(MissingGoal, span, "task has no goal")
  }
  if goals > 1 {
    fail_theory(MultipleGoals, span, "task contains multiple goals")
  }
  { anchor, items: items.to_owned() }
}

///|
pub fn split_theory(
  context : @identity.CompilationContext,
  theory : Theory,
  span : @identity.SourceSpan?,
) -> Array[Task] raise {
  if !context.contains(theory.anchor) {
    fail_theory(ContextMismatch, span, "theory belongs to another context")
  }
  let prefix = TaskAccumulator::new(context)
  let tasks : Array[Task] = []
  for item in theory.items {
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dprop(Plemma, _, _) => {
            let task_items = prefix.items.copy()
            task_items.push(
              TheoryDecl(
                declaration.reclassify_proposition(context, Pgoal, span),
              ),
            )
            tasks.push(Task::trusted_new(theory.anchor, task_items, span))
            prefix.add_declaration(
              declaration.reclassify_proposition(context, Paxiom, span),
            )
          }
          Dprop(Pgoal, _, _) => {
            let task_items = prefix.items.copy()
            task_items.push(item)
            tasks.push(Task::trusted_new(theory.anchor, task_items, span))
          }
          _ => prefix.add_declaration(declaration)
        }
      TheoryUse(key) => prefix.flatten_use(theory.used_theory(key), span)
      TheoryClone(witness) => prefix.items.push(TheoryClone(witness))
      TheoryMeta(meta) => prefix.items.push(TheoryMeta(meta))
    }
  }
  tasks
}

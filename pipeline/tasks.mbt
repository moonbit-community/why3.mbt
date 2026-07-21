// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn final_goal(task : @theory.Task) -> @logic.PrSymbol {
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(declaration) &&
    declaration.view() is Dprop(Pgoal, proposition, _) else {
    abort("validated raw task has no final goal")
  }
  proposition
}

///|
pub fn tasks(checked : CheckedFile) -> CheckedFile raise {
  if !checked.raw_goal_entries.is_empty() {
    return checked
  }
  let entries : Array[RawGoal] = []
  let raw : Array[@theory.Task] = []
  for unit in checked.typed_units {
    let (kind, name, theory) = match unit {
      Theory(theory) => (@z3.TheoryUnit, theory.view().name.view().name, theory)
      Module(pmodule) => {
        let generated = @vc.generate_module(checked.context, pmodule)
        (
          @z3.ModuleUnit,
          generated.pure_theory().view().name.view().name,
          generated.pure_theory(),
        )
      }
    }
    for ordinal, task in @theory.split_theory(checked.context, theory, None) {
      let info = @z3.GoalInfo::new(kind, name, final_goal(task), ordinal)
      entries.push({ task, info })
      raw.push(task)
    }
  }
  {
    context: checked.context,
    environment: checked.environment,
    typed_units: checked.typed_units.copy(),
    raw_goal_entries: entries,
    raw_goals: raw,
  }
}

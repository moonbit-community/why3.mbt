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
pub fn generate_vc_module(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  pmodule : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  generate_vc_module_with_options(
    context,
    environment,
    pmodule,
    @vc.VcOptions::classical(),
  )
}

///|
pub fn generate_vc_module_with_options(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  pmodule : @mlw.Pmodule,
  options : @vc.VcOptions,
) -> @mlw.Pmodule raise {
  let mut integer_theory : @theory.Theory? = None
  for theory in pmodule.pure_theory().used_theories() {
    let key = theory.key().view()
    if key.path == [b"int"] && key.name == b"Int" {
      integer_theory = Some(theory)
      break
    }
  }
  let integer_theory = match integer_theory {
    Some(theory) => theory
    None =>
      environment.resolve_theory(@theory.TheoryKey::new([b"int"], b"Int"), None) catch {
        _ =>
          environment.read_theory(
            @env.LibraryPath::new([b"int"]),
            b"Int",
            @elab.load_mlw_library,
            None,
          )
      }
  }
  let well_founded_theory = environment.well_founded_module().pure_theory()
  @vc.generate_routine_module_with_support_and_options(
    context, pmodule, integer_theory, well_founded_theory, options,
  )
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
        let generated = generate_vc_module(
          checked.context,
          checked.environment,
          pmodule,
        )
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

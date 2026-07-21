// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum TypedUnitView {
  Theory(@theory.Theory)
  Module(@mlw.Pmodule)
}

///|
priv struct RawGoal {
  task : @theory.Task
  info : @z3.GoalInfo
}

///|
struct CheckedFile {
  context : @identity.CompilationContext
  environment : @stdlib.FrozenEnvironment
  typed_units : Array[TypedUnitView]
  raw_goal_entries : Array[RawGoal]
  raw_goals : Array[@theory.Task]
}

///|
fn CheckedFile::new(
  context : @identity.CompilationContext,
  environment : @stdlib.FrozenEnvironment,
  typed_units : Array[TypedUnitView],
) -> CheckedFile {
  { context, environment, typed_units, raw_goal_entries: [], raw_goals: [] }
}

///|
pub fn CheckedFile::typed_units(self : CheckedFile) -> ArrayView[TypedUnitView] {
  self.typed_units[:]
}

///|
pub fn CheckedFile::raw_goals(self : CheckedFile) -> ArrayView[@theory.Task] {
  self.raw_goals[:]
}

///|
pub fn CheckedFile::goal_infos(self : CheckedFile) -> Array[@z3.GoalInfo] {
  self.raw_goal_entries.map(entry => entry.info)
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum GoalUnitKind {
  TheoryUnit
  ModuleUnit
} derive(Eq, Debug)

///|
struct GoalInfo {
  unit_kind : GoalUnitKind
  unit_name : Bytes
  goal : @logic.PrSymbol
  display_name : Bytes
  ordinal : Int
  origin : @identity.Origin
  expl_attributes : Array[Bytes]
}

///|
pub(all) struct GoalInfoView {
  unit_kind : GoalUnitKind
  unit_name : Bytes
  goal : @logic.PrSymbol
  display_name : Bytes
  ordinal : Int
  origin : @identity.Origin
  expl_attributes : ArrayView[Bytes]
}

///|
fn goal_attribute_starts_with(value : BytesView, prefix : BytesView) -> Bool {
  if value.length() < prefix.length() {
    return false
  }
  for index = 0; index < prefix.length(); index = index + 1 {
    if value[index] != prefix[index] {
      return false
    }
  }
  true
}

///|
pub fn GoalInfo::new(
  unit_kind : GoalUnitKind,
  unit_name : BytesView,
  goal : @logic.PrSymbol,
  ordinal : Int,
) -> GoalInfo {
  if ordinal < 0 {
    abort("goal ordinal cannot be negative")
  }
  let view = goal.view()
  let explanation_attributes : Array[Bytes] = []
  for attribute in view.origin.attributes() {
    if goal_attribute_starts_with(attribute, b"expl:") {
      explanation_attributes.push(attribute)
    }
  }
  {
    unit_kind,
    unit_name: unit_name.to_owned(),
    goal,
    display_name: view.origin.display_name().to_owned(),
    ordinal,
    origin: view.origin,
    expl_attributes: explanation_attributes,
  }
}

///|
pub fn GoalInfo::view(self : GoalInfo) -> GoalInfoView {
  {
    unit_kind: self.unit_kind,
    unit_name: self.unit_name,
    goal: self.goal,
    display_name: self.display_name,
    ordinal: self.ordinal,
    origin: self.origin,
    expl_attributes: self.expl_attributes[:],
  }
}

///|
struct PreparedCall {
  raw_task : @theory.Task
  prepared_task : @theory.Task
  query : @smtv2.SmtQuery
  command : @prover.CommandSpec
  goal_info : GoalInfo
}

///|
pub fn PreparedCall::new(
  raw_task : @theory.Task,
  prepared_task : @theory.Task,
  query : @smtv2.SmtQuery,
  command : @prover.CommandSpec,
  goal_info : GoalInfo,
) -> PreparedCall raise BindError {
  let anchor = raw_task.context_anchor()
  if !anchor.same_context(prepared_task.context_anchor()) ||
    !anchor.same_context(goal_info.goal.semantic_id()) {
    raise BindError({
      kind: ContextMismatch,
      path: "$.preparedCall",
      message: "prepared call combines different compilation contexts",
    })
  }
  { raw_task, prepared_task, query, command, goal_info }
}

///|
pub fn PreparedCall::raw_task(self : PreparedCall) -> @theory.Task {
  self.raw_task
}

///|
pub fn PreparedCall::prepared_task(self : PreparedCall) -> @theory.Task {
  self.prepared_task
}

///|
pub fn PreparedCall::query(self : PreparedCall) -> @smtv2.SmtQuery {
  self.query
}

///|
pub fn PreparedCall::command(self : PreparedCall) -> @prover.CommandSpec {
  self.command
}

///|
pub fn PreparedCall::goal_info(self : PreparedCall) -> GoalInfo {
  self.goal_info
}

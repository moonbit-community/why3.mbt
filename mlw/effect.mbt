// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ProgramTermination {
  Total
} derive(Eq, Debug)

///|
pub(all) enum ProgramMask {
  Visible
  Ghost
} derive(Eq, Debug)

///|
struct Effect {
  reads : Array[PVariable]
  ghost : Bool
}

///|
pub(all) struct EffectView {
  reads : ArrayView[PVariable]
  termination : ProgramTermination
  ghost : Bool
}

///|
pub fn Effect::pure(ghost : Bool) -> Effect {
  { reads: [], ghost }
}

///|
pub fn Effect::from_reads(reads : ArrayView[PVariable], ghost : Bool) -> Effect {
  let unique : Array[PVariable] = []
  for variable in reads {
    if !unique.any(existing => existing == variable) {
      unique.push(variable)
    }
  }
  { reads: unique, ghost }
}

///|
fn Effect::union(self : Effect, other : Effect) -> Effect {
  let reads = self.reads.copy()
  for variable in other.reads {
    if !reads.any(existing => existing == variable) {
      reads.push(variable)
    }
  }
  { reads, ghost: self.ghost || other.ghost }
}

///|
fn Effect::without(self : Effect, binder : PVariable) -> Effect {
  {
    reads: [
      for variable in self.reads if variable != binder => variable
    ],
    ghost: self.ghost,
  }
}

///|
pub fn Effect::view(self : Effect) -> EffectView {
  { reads: self.reads[:], termination: Total, ghost: self.ghost }
}

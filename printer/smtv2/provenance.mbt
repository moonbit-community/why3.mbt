// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-28.

///|
priv enum TrackedIdentifierOrigin {
  TrackedUser
  TrackedGenerated(@identity.GeneratedStage)
}

///|
/// Binder provenance follows Why3 identifier clones independently of semantic
/// identity. Non-binder identifiers already carry exact origins and therefore
/// fall back to their immutable `Origin` during token normalization.
struct SmtProvenance {
  context : @identity.CompilationContext
  mut identifier_watermark : @identity.IdentifierWatermark
  origins : Map[@identity.IdentifierId, TrackedIdentifierOrigin]
  seen : Map[@identity.IdentifierId, Unit]
  clone_sources : Map[@identity.IdentifierId, @identity.IdentifierId]
  identifier_types : Map[@identity.IdentifierId, @logic.Ty]
}

///|
pub fn SmtProvenance::new(
  context : @identity.CompilationContext,
) -> SmtProvenance {
  {
    context,
    identifier_watermark: context.identifier_watermark(),
    origins: Map([]),
    seen: Map([]),
    clone_sources: Map([]),
    identifier_types: Map([]),
  }
}

///|
fn SmtProvenance::observe_identifier_clones(self : SmtProvenance) -> Unit {
  for
    event in self.context.identifier_clone_events_since(
      self.identifier_watermark,
    ) {
    self.clone_sources[event.clone()] = event.original()
  }
  self.identifier_watermark = self.context.identifier_watermark()
}

///|
fn SmtProvenance::root_identifier(
  self : SmtProvenance,
  identifier : @identity.IdentifierId,
) -> @identity.IdentifierId {
  match self.clone_sources.get(identifier) {
    None => identifier
    Some(source) => self.root_identifier(source)
  }
}

///|
fn SmtProvenance::nearest_ancestor_type(
  self : SmtProvenance,
  identifier : @identity.IdentifierId,
) -> @logic.Ty? {
  match self.clone_sources.get(identifier) {
    None => None
    Some(source) =>
      match self.identifier_types.get(source) {
        Some(ty) => Some(ty)
        None => self.nearest_ancestor_type(source)
      }
  }
}

///|
fn SmtProvenance::tracked_origin(
  self : SmtProvenance,
  identifier : @identity.IdentifierId,
) -> TrackedIdentifierOrigin? {
  match self.origins.get(identifier) {
    Some(origin) => Some(origin)
    None =>
      match self.clone_sources.get(identifier) {
        Some(source) => self.tracked_origin(source)
        None => None
      }
  }
}

///|
fn SmtProvenance::observe_binder(
  self : SmtProvenance,
  variable : @logic.VSymbol,
  stage : @identity.GeneratedStage?,
  ty : @logic.Ty?,
) -> Unit {
  let identifier = variable.identifier_id()
  // A declaration transformer may reuse a memoized declaration whose clone
  // event predates this per-goal observer.  VSymbol retains the immediate
  // clone edge. Replay it only when its source is itself unobservable in this
  // goal. If the source was already observed, the missing event denotes a
  // cached clone and Why3 deliberately treats the surviving identifier as a
  // new root in the current checkpoint.
  if variable.clone_source_identifier_id() is Some(source) &&
    !self.clone_sources.contains(identifier) &&
    !self.seen.contains(source) {
    self.clone_sources[identifier] = source
    if !self.seen.contains(source) &&
      !self.origins.contains(source) &&
      !self.clone_sources.contains(source) {
      // Persistent declaration caches can retain a clone whose creation event
      // predates this goal. Seed that otherwise-unobservable source from the
      // immutable presentation origin carried by the surviving VSymbol.
      self.origins[source] = match variable.view().origin.kind().view() {
        UserKind => TrackedUser
        GeneratedKind(stage) => TrackedGenerated(stage)
      }
    }
  }
  // MoonBit materializes opened closures eagerly. The same semantic variable
  // can therefore carry one identifier through a pattern binding and a later
  // typed binding where Why3 keeps distinct closure-local identifier clones.
  // Preserve the later type observation so Guards can compare the clone
  // lineage exactly as Why3 does.
  if ty is Some(ty) && !self.identifier_types.contains(identifier) {
    self.identifier_types[identifier] = ty
  }
  if self.seen.contains(identifier) {
    return
  }
  self.seen[identifier] = ()
  if stage == Some(@identity.Guards) {
    let preserves_type = match self.nearest_ancestor_type(identifier) {
      Some(source_type) =>
        match ty {
          Some(ty) => source_type == ty
          None => false
        }
      None => false
    }
    if !preserves_type {
      self.origins[identifier] = TrackedGenerated(@identity.Guards)
    }
    return
  }
  let root = self.root_identifier(identifier)
  if self.origins.contains(root) {
    return
  }
  self.origins[root] = match stage {
    None => TrackedUser
    Some(stage) => TrackedGenerated(stage)
  }
}

///|
fn observe_pattern_binders(
  provenance : SmtProvenance,
  pattern : @logic.Pattern,
  stage : @identity.GeneratedStage?,
) -> Unit {
  match pattern.view() {
    Pwild(_) => ()
    Pvar(variable) => provenance.observe_binder(variable, stage, None)
    Papp(_, arguments, _) =>
      for argument in arguments {
        observe_pattern_binders(provenance, argument, stage)
      }
    Por(left, right, _) => {
      observe_pattern_binders(provenance, left, stage)
      observe_pattern_binders(provenance, right, stage)
    }
    Pas(inner, variable, _) => {
      observe_pattern_binders(provenance, inner, stage)
      provenance.observe_binder(variable, stage, None)
    }
  }
}

///|
fn observe_term_binders(
  provenance : SmtProvenance,
  term : @logic.Term,
  stage : @identity.GeneratedStage?,
) -> Unit {
  let visit = fn(child) { observe_term_binders(provenance, child, stage) }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
    Tapp(_, _, arguments) =>
      for argument in arguments {
        visit(argument)
      }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(variable, value, body) => {
      provenance.observe_binder(variable, stage, Some(variable.ty()))
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        let view = branch.view()
        observe_pattern_binders(provenance, view.pattern, stage)
        visit(view.body)
      }
    }
    Teps(variable, body) => {
      provenance.observe_binder(variable, stage, Some(variable.ty()))
      visit(body)
    }
    Tquant(_, binders, triggers, body) => {
      for binder in binders {
        provenance.observe_binder(binder, stage, Some(binder.ty()))
      }
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
  }
}

///|
fn observe_declaration_binders(
  provenance : SmtProvenance,
  declaration : @logic.Decl,
  stage : @identity.GeneratedStage?,
) -> Unit {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        let view = definition.view()
        for parameter in view.parameters {
          provenance.observe_binder(parameter, stage, Some(parameter.ty()))
        }
        observe_term_binders(provenance, view.body, stage)
      }
    Dind(_, declarations) =>
      for inductive in declarations {
        for case_ in inductive.view().cases {
          observe_term_binders(provenance, case_.view().formula, stage)
        }
      }
    Dprop(_, _, formula) => observe_term_binders(provenance, formula, stage)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

///|
/// Observes the raw task with `stage = None`, then each preparation
/// checkpoint with the stage that produced it.
pub fn SmtProvenance::observe_task(
  self : SmtProvenance,
  task : @theory.Task,
  stage : @identity.GeneratedStage?,
) -> Unit {
  self.observe_identifier_clones()
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      observe_declaration_binders(self, declaration, stage)
    }
  }
}

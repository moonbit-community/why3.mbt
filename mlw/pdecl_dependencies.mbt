// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum ProgramDependency {
  CoreDependency(@logic.DeclDependency)
  ProgramTypeDependency(ProgramTypeSymbol)
  RoutineDependency(RoutineSymbol)
  ProgramVariableDependency(PVariable)
  ExceptionDependency(XSymbol)
}

///|
fn ProgramDependency::kind_tag(self : ProgramDependency) -> Int {
  match self {
    CoreDependency(_) => 0
    ProgramTypeDependency(_) => 1
    RoutineDependency(_) => 2
    ProgramVariableDependency(_) => 3
    ExceptionDependency(_) => 4
  }
}

///|
pub fn ProgramDependency::semantic_id(
  self : ProgramDependency,
) -> @identity.SemanticId {
  match self {
    CoreDependency(dependency) => dependency.semantic_id()
    ProgramTypeDependency(symbol) => symbol.semantic_id()
    RoutineDependency(symbol) => symbol.semantic_id()
    ProgramVariableDependency(variable) => variable.semantic_id()
    ExceptionDependency(exception) => exception.semantic_id()
  }
}

///|
pub impl Eq for ProgramDependency with fn equal(self, other) {
  self.kind_tag() == other.kind_tag() &&
  self.semantic_id() == other.semantic_id()
}

///|
priv struct ProgramDependencyCollector {
  values : Array[ProgramDependency]
}

///|
fn ProgramDependencyCollector::new() -> ProgramDependencyCollector {
  { values: [] }
}

///|
fn ProgramDependencyCollector::add(
  self : ProgramDependencyCollector,
  dependency : ProgramDependency,
) -> Unit {
  if !self.values.any(existing => existing == dependency) {
    self.values.push(dependency)
  }
}

///|
fn ProgramDependencyCollector::add_program_variable(
  self : ProgramDependencyCollector,
  variable : PVariable,
) -> Unit {
  self.add(ProgramVariableDependency(variable))
  self.add_ity(variable.view().ity)
}

///|
fn ProgramDependencyCollector::add_ty(
  self : ProgramDependencyCollector,
  ty : @logic.Ty,
) -> Unit {
  match ty.view() {
    TyVar(_) => ()
    TyApp(symbol, arguments) => {
      self.add(CoreDependency(TypeDependency(symbol)))
      for argument in arguments {
        self.add_ty(argument)
      }
    }
  }
}

///|
fn ProgramDependencyCollector::add_ity(
  self : ProgramDependencyCollector,
  ity : Ity,
) -> Unit {
  match ity.view() {
    ItyVar(_) => ()
    ItyApp(symbol, arguments, regions) => {
      self.add(ProgramTypeDependency(symbol))
      self.add(CoreDependency(TypeDependency(symbol.view().logic_type)))
      for argument in arguments {
        self.add_ity(argument)
      }
      for region in regions {
        self.add_ity(region)
      }
    }
    ItyReg(region) => {
      let view = region.view()
      self.add(ProgramTypeDependency(view.symbol))
      self.add(CoreDependency(TypeDependency(view.symbol.view().logic_type)))
      for argument in view.arguments {
        self.add_ity(argument)
      }
      for nested in view.regions {
        self.add_ity(nested)
      }
    }
  }
}

///|
fn ProgramDependencyCollector::add_pattern(
  self : ProgramDependencyCollector,
  pattern : @logic.Pattern,
) -> Unit {
  self.add_ty(pattern.ty())
  match pattern.view() {
    Pwild(_) | Pvar(_) => ()
    Papp(symbol, arguments, _) => {
      self.add(CoreDependency(LogicDependency(symbol)))
      for argument in arguments {
        self.add_pattern(argument)
      }
    }
    Por(left, right, _) => {
      self.add_pattern(left)
      self.add_pattern(right)
    }
    Pas(inner, _, _) => self.add_pattern(inner)
  }
}

///|
fn ProgramDependencyCollector::add_term(
  self : ProgramDependencyCollector,
  term : @logic.Term,
) -> Unit {
  if term.ty() is Some(ty) {
    self.add_ty(ty)
  }
  match term.view() {
    Tvar(variable) => self.add_ty(variable.ty())
    Tconst(_) | Ttrue | Tfalse => ()
    Tapp(symbol, instantiation, arguments) => {
      self.add(CoreDependency(LogicDependency(symbol)))
      for entry in instantiation {
        self.add_ty(entry.1)
      }
      for argument in arguments {
        self.add_term(argument)
      }
    }
    Tif(condition, consequent, alternative) => {
      self.add_term(condition)
      self.add_term(consequent)
      self.add_term(alternative)
    }
    Tlet(variable, value, body) => {
      self.add_ty(variable.ty())
      self.add_term(value)
      self.add_term(body)
    }
    Tcase(scrutinee, branches) => {
      self.add_term(scrutinee)
      for branch in branches {
        let view = branch.view()
        self.add_pattern(view.pattern)
        self.add_term(view.body)
      }
    }
    Teps(variable, body) => {
      self.add_ty(variable.ty())
      self.add_term(body)
    }
    Tquant(_, binders, triggers, body) => {
      for binder in binders {
        self.add_ty(binder.ty())
      }
      for group in triggers {
        for trigger in group {
          self.add_term(trigger)
        }
      }
      self.add_term(body)
    }
    Tbinop(_, left, right) => {
      self.add_term(left)
      self.add_term(right)
    }
    Tnot(inner) => self.add_term(inner)
  }
}

///|
fn ProgramDependencyCollector::add_effect(
  self : ProgramDependencyCollector,
  effect : Effect,
) -> Unit {
  let view = effect.view()
  for variable in view.reads {
    self.add_program_variable(variable)
  }
  for write in view.writes {
    let write_view = write.view()
    self.add_ity(Ity::region(write_view.region))
    for field in write_view.fields {
      self.add_program_variable(field)
    }
  }
  for exception in view.raises {
    self.add(ExceptionDependency(exception))
    self.add_ity(exception.view().ity)
  }
}

///|
fn ProgramDependencyCollector::add_cty(
  self : ProgramDependencyCollector,
  cty : Cty,
) -> Unit {
  let view = cty.view()
  for variable in view.arguments {
    self.add_program_variable(variable)
  }
  for precondition in view.preconditions {
    self.add_term(precondition)
  }
  for postcondition in view.postconditions {
    let post = postcondition.view()
    self.add_ty(post.result.ty())
    self.add_term(post.formula)
  }
  for exceptional in view.exceptional_postconditions {
    let exceptional_view = exceptional.view()
    self.add(ExceptionDependency(exceptional_view.exception))
    for postcondition in exceptional_view.postconditions {
      let post = postcondition.view()
      self.add_ty(post.result.ty())
      self.add_term(post.formula)
    }
  }
  for oldie in view.oldies {
    let oldie_view = oldie.view()
    self.add_program_variable(oldie_view.snapshot)
    self.add_program_variable(oldie_view.original)
  }
  self.add_effect(view.effect)
  self.add_ity(view.result)
}

///|
fn ProgramDependencyCollector::add_cexp(
  self : ProgramDependencyCollector,
  computation : Cexp,
) -> Unit {
  self.add_cty(computation.cty())
  match computation.view() {
    Capp(symbol, arguments) => {
      self.add(RoutineDependency(symbol))
      for argument in arguments {
        self.add_program_variable(argument)
      }
    }
    Cpur(symbol, arguments) => {
      self.add(CoreDependency(LogicDependency(symbol)))
      for argument in arguments {
        self.add_program_variable(argument)
      }
    }
    Cfun(body) => self.add_expr(body)
    Cany => ()
  }
}

///|
fn ProgramDependencyCollector::add_let_definition(
  self : ProgramDependencyCollector,
  definition : LetDefinition,
) -> Unit {
  match definition.view() {
    LDvar(variable, value) => {
      self.add_program_variable(variable)
      self.add_expr(value)
    }
    LDsym(symbol, computation) => {
      self.add(RoutineDependency(symbol))
      self.add_cexp(computation)
    }
    LDrec(definitions) =>
      for definition in definitions {
        let view = definition.view()
        self.add(RoutineDependency(view.symbol))
        self.add(RoutineDependency(view.internal_symbol))
        self.add_cexp(view.function_)
        for variant in view.variants {
          let variant_view = variant.view()
          self.add_term(variant_view.term)
          if variant_view.relation is Some(relation) {
            self.add(CoreDependency(LogicDependency(relation)))
          }
        }
      }
  }
}

///|
fn ProgramDependencyCollector::add_expr(
  self : ProgramDependencyCollector,
  expression : Expr,
) -> Unit {
  self.add_ity(expression.ity())
  self.add_effect(expression.effect())
  match expression.view() {
    Evar(variable) => self.add_program_variable(variable)
    Econst(_) | Eabsurd => ()
    Eexec(computation, cty) => {
      self.add_cexp(computation)
      self.add_cty(cty)
    }
    Eassign(assignments) =>
      for assignment in assignments {
        let view = assignment.view()
        self.add_program_variable(view.region)
        self.add(RoutineDependency(view.field))
        self.add_program_variable(view.value)
      }
    Elet(definition, body) => {
      self.add_let_definition(definition)
      self.add_expr(body)
    }
    Eif(condition, consequent, alternative) => {
      self.add_expr(condition)
      self.add_expr(consequent)
      self.add_expr(alternative)
    }
    Ematch(scrutinee, regular, exceptional) => {
      self.add_expr(scrutinee)
      for branch in regular {
        let view = branch.view()
        self.add_pattern(view.pattern.view().pattern)
        self.add_expr(view.body)
      }
      for branch in exceptional {
        let view = branch.view()
        self.add(ExceptionDependency(view.exception))
        self.add_expr(view.body)
      }
    }
    Ewhile(condition, invariants, variants, body) => {
      self.add_expr(condition)
      for invariant in invariants {
        self.add_term(invariant)
      }
      for variant in variants {
        let view = variant.view()
        self.add_term(view.term)
        if view.relation is Some(relation) {
          self.add(CoreDependency(LogicDependency(relation)))
        }
      }
      self.add_expr(body)
    }
    Efor(variable, bounds, internal, invariants, body) => {
      self.add_program_variable(variable)
      let bounds_view = bounds.view()
      self.add_program_variable(bounds_view.first)
      self.add_program_variable(bounds_view.last)
      self.add_program_variable(internal)
      for invariant in invariants {
        self.add_term(invariant)
      }
      self.add_expr(body)
    }
    Eraise(exception, payload) => {
      self.add(ExceptionDependency(exception))
      self.add_expr(payload)
    }
    Eexn(exception, body) => {
      self.add(ExceptionDependency(exception))
      self.add_expr(body)
    }
    Eassert(_, formula) | Epure(formula) => self.add_term(formula)
    Eghost(body) => self.add_expr(body)
  }
}

///|
fn ProgramDependencyCollector::add_meta(
  self : ProgramDependencyCollector,
  meta : @theory.Meta,
) -> Unit {
  for argument in meta.view().arguments {
    match argument {
      MetaType(ty) => self.add_ty(ty)
      MetaTypeSymbol(symbol) => self.add(CoreDependency(TypeDependency(symbol)))
      MetaLogicSymbol(symbol) =>
        self.add(CoreDependency(LogicDependency(symbol)))
      MetaPropositionSymbol(symbol) =>
        self.add(CoreDependency(PropositionDependency(symbol)))
      MetaString(_) | MetaInteger(_) | MetaIdentifier(_) => ()
    }
  }
}

///|
pub fn ProgramDeclaration::introduced_symbols(
  self : ProgramDeclaration,
) -> Array[ProgramDependency] {
  let collector = ProgramDependencyCollector::new()
  for declaration in self.pure_declarations() {
    for dependency in declaration.introduced_symbols() {
      collector.add(CoreDependency(dependency))
    }
  }
  match self {
    PDtype(declarations, _, _) =>
      for declaration in declarations {
        let view = declaration.view()
        collector.add(ProgramTypeDependency(view.symbol))
        for field in view.fields {
          collector.add(RoutineDependency(field))
        }
        for constructor_symbol in view.constructors {
          collector.add(RoutineDependency(constructor_symbol))
        }
      }
    PDlet(symbol, _, _, _) => collector.add(RoutineDependency(symbol))
    PDvar(variable, _, _, _) =>
      collector.add(ProgramVariableDependency(variable))
    PDrec(definitions, _, _) =>
      for definition in definitions {
        collector.add(RoutineDependency(definition.view().symbol))
      }
    PDexn(exception, _, _) => collector.add(ExceptionDependency(exception))
    PDpure(_, _) => ()
  }
  collector.values
}

///|
pub fn ProgramDeclaration::dependencies(
  self : ProgramDeclaration,
) -> Array[ProgramDependency] {
  let collector = ProgramDependencyCollector::new()
  for declaration in self.pure_declarations() {
    for dependency in declaration.dependencies() {
      collector.add(CoreDependency(dependency))
    }
  }
  for meta in self.metas() {
    collector.add_meta(meta)
  }
  match self {
    PDtype(declarations, _, _) =>
      for declaration in declarations {
        let view = declaration.view()
        collector.add(ProgramTypeDependency(view.symbol))
        collector.add(
          CoreDependency(TypeDependency(view.symbol.view().logic_type)),
        )
        if view.symbol.view().definition is ProgramAlias(target) {
          collector.add_ity(target)
        }
        for field in view.fields {
          collector.add(RoutineDependency(field))
          collector.add_cty(field.view().cty)
        }
        for constructor_symbol in view.constructors {
          collector.add(RoutineDependency(constructor_symbol))
          collector.add_cty(constructor_symbol.view().cty)
        }
        for invariant in view.invariants {
          collector.add_term(invariant)
        }
        if view.witness is Some(witness) {
          collector.add_expr(witness)
        }
      }
    PDlet(symbol, computation, _, _) => {
      collector.add_cty(symbol.view().cty)
      match computation {
        Cany(cty) => collector.add_cty(cty)
        Cfun(cty, body) => {
          collector.add_cty(cty)
          if body is Some(body) {
            collector.add_expr(body)
          }
        }
        Cexpression(expression) => collector.add_cexp(expression)
      }
      for read in computation.cty().reads() {
        collector.add_program_variable(read)
      }
    }
    PDvar(variable, value, _, _) => {
      collector.add_ity(variable.view().ity)
      collector.add_expr(value)
    }
    PDrec(definitions, _, _) =>
      for definition in definitions {
        let view = definition.view()
        collector.add_cty(view.symbol.view().cty)
        collector.add_cty(view.internal_symbol.view().cty)
        collector.add_cexp(view.function_)
        for variant in view.variants {
          collector.add_term(variant.view().term)
        }
        for read in view.internal_symbol.view().cty.reads() {
          collector.add_program_variable(read)
        }
      }
    PDexn(exception, _, _) => collector.add_ity(exception.view().ity)
    PDpure(_, _) => ()
  }
  collector.values
}

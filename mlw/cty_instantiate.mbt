// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
priv struct CtyTermInstantiation {
  context : @identity.CompilationContext
  types : @logic.TySubstitution
  target_types : @logic.TySubstitution
  variables : Map[@logic.VSymbol, @logic.VSymbol]
}

///|
fn CtyTermInstantiation::new(
  context : @identity.CompilationContext,
  types : @logic.TySubstitution,
  target_types : @logic.TySubstitution,
) -> CtyTermInstantiation {
  { context, types, target_types, variables: Map([]) }
}

///|
fn diagnostic_logic_type(ty : @logic.Ty) -> String {
  match ty.view() {
    TyVar(variable) =>
      "'\{variable.name()}#\{variable.semantic_id().local_id()}"
    TyApp(symbol, arguments) => {
      let arguments = arguments.map(diagnostic_logic_type)
      if arguments.is_empty() {
        "\{symbol.name()}"
      } else {
        "\{symbol.name()}<\{arguments.join(",")}>"
      }
    }
  }
}

///|
fn cty_inference_type_variable(variable : @logic.TyVarSymbol) -> Bool {
  variable
  .origin()
  .attributes()
  .any(attribute => attribute == b"mlw:inference_type_variable")
}

///|
fn ItySubstitution::inference_logic_substitution(
  self : ItySubstitution,
  span : @identity.SourceSpan?,
) -> @logic.TySubstitution raise {
  let mut normalizing_types = @logic.TySubstitution::new()
  for entry in self.type_variables {
    let target = self.resolve_inference_variables(entry.1, span)
    if !target.free_type_variables().any(variable => variable == entry.0) {
      normalizing_types = normalizing_types.bind(
        entry.0,
        target.to_ty(span),
        span,
      )
    }
  }
  let mut result = @logic.TySubstitution::new()
  for entry in self.type_variables {
    if cty_inference_type_variable(entry.0) {
      let target = self.resolve_inference_variables(entry.1, span)
      let normalized = normalizing_types.apply(target.to_ty(span), span)
      result = result.bind(entry.0, normalized, span)
    }
  }
  result
}

///|
fn CtyTermInstantiation::bind(
  self : CtyTermInstantiation,
  source : @logic.VSymbol,
  source_ity : Ity,
  target : @logic.VSymbol,
  target_ity : Ity,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let instantiated = self.types.apply(source.ty(), span)
  let target_instantiated = self.target_types.apply(target.ty(), span)
  if instantiated != target_instantiated {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "program-variable substitution for '\{source.view().name}' has the wrong type: pure \{diagnostic_logic_type(instantiated)}, program \{diagnostic_logic_type(self.types.apply(source_ity.to_ty(span), span))}, target program \{diagnostic_logic_type(target_ity.to_ty(span))}, target pure \{diagnostic_logic_type(target_instantiated)}",
    )
  }
  self.variables[source] = target
}

///|
fn CtyTermInstantiation::clone_variable(
  self : CtyTermInstantiation,
  variable : @logic.VSymbol,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  let view = variable.view()
  let instantiated_type = self.types.apply(view.ty, span)
  if instantiated_type == view.ty {
    variable
  } else {
    @logic.VSymbol::new(
      self.context,
      view.name,
      view.origin,
      instantiated_type,
      span,
    )
  }
}

///|
fn cty_pattern_bound_variables(
  pattern : @logic.Pattern,
) -> Array[@logic.VSymbol] {
  let variables = pattern.bound_variables().to_owned()
  variables.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  variables
}

///|
fn CtyTermInstantiation::pattern(
  self : CtyTermInstantiation,
  pattern : @logic.Pattern,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  match pattern.view() {
    Pwild(ty) => @logic.Pattern::wild(self.types.apply(ty, span))
    Pvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Pattern::variable(replacement)
        None =>
          fail_mlw(
            UnboundSpecificationVariable,
            span,
            "pattern variable has no instantiated correspondence",
          )
      }
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        symbol,
        arguments.map(argument => self.pattern(argument, variables, span)),
        self.types.apply(ty, span),
        span,
      )
    Por(left, right, _) =>
      @logic.Pattern::or(
        self.pattern(left, variables, span),
        self.pattern(right, variables, span),
        span,
      )
    Pas(inner, variable, _) =>
      match variables.get(variable) {
        Some(replacement) =>
          @logic.Pattern::as_pattern(
            self.pattern(inner, variables, span),
            replacement,
            span,
          )
        None =>
          fail_mlw(
            UnboundSpecificationVariable,
            span,
            "as-pattern variable has no instantiated correspondence",
          )
      }
  }
}

///|
fn copy_instantiated_term_decoration(
  source : @logic.Term,
  replacement : @logic.Term,
) -> @logic.Term {
  let replacement = match source.origin() {
    Some(origin) => replacement.decorate(origin, [])
    None => replacement
  }
  replacement.source_decorate(source.source_span(), source.attributes())
}

///|
fn CtyTermInstantiation::term_with(
  self : CtyTermInstantiation,
  term : @logic.Term,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let instantiated = match term.view() {
    Tvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Term::variable(replacement)
        None => {
          let replacement = self.clone_variable(variable, span)
          variables[variable] = replacement
          @logic.Term::variable(replacement)
        }
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) else {
        abort("validated constant term lost its value type")
      }
      @logic.Term::constant(constant, self.types.apply(ty, span), span)
    }
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        arguments.map(argument => self.term_with(argument, variables, span)),
        match term.ty() {
          Some(ty) => Some(self.types.apply(ty, span))
          None => None
        },
        span,
      )
    Tif(condition, consequent, alternative) =>
      @logic.Term::if_then_else(
        self.term_with(condition, variables, span),
        self.term_with(consequent, variables, span),
        self.term_with(alternative, variables, span),
        span,
      )
    Tlet(variable, value, body) => {
      let replacement = self.clone_variable(variable, span)
      let body_variables = variables.copy()
      body_variables[variable] = replacement
      @logic.Term::let_in(
        replacement,
        self.term_with(value, variables, span),
        self.term_with(body, body_variables, span),
        span,
      )
    }
    Tcase(scrutinee, branches) => {
      let instantiated_branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        let branch_variables = variables.copy()
        for variable in cty_pattern_bound_variables(view.pattern) {
          branch_variables[variable] = self.clone_variable(variable, span)
        }
        instantiated_branches.push(
          (
            self.pattern(view.pattern, branch_variables, span),
            self.term_with(view.body, branch_variables, span),
          ),
        )
      }
      @logic.Term::case(
        self.term_with(scrutinee, variables, span),
        instantiated_branches,
        span,
      )
    }
    Teps(variable, body) => {
      let replacement = self.clone_variable(variable, span)
      let body_variables = variables.copy()
      body_variables[variable] = replacement
      @logic.Term::epsilon(
        replacement,
        self.term_with(body, body_variables, span),
        span,
      )
    }
    Tquant(quantifier, binders, triggers, body) => {
      let body_variables = variables.copy()
      let replacements : Array[@logic.VSymbol] = []
      for binder in binders {
        let replacement = self.clone_variable(binder, span)
        replacements.push(replacement)
        body_variables[binder] = replacement
      }
      @logic.Term::quantify(
        quantifier,
        replacements,
        triggers.map(group => {
          group.map(trigger => self.term_with(trigger, body_variables, span))
        }),
        self.term_with(body, body_variables, span),
        span,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(
        operator,
        self.term_with(left, variables, span),
        self.term_with(right, variables, span),
        span,
      )
    Tnot(inner) =>
      @logic.Term::not(self.term_with(inner, variables, span), span)
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_instantiated_term_decoration(term, instantiated)
}

///|
fn CtyTermInstantiation::term(
  self : CtyTermInstantiation,
  term : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  self.term_with(term, self.variables.copy(), span)
}

///|
fn ItySubstitution::logic_substitution(
  self : ItySubstitution,
  span : @identity.SourceSpan?,
) -> @logic.TySubstitution raise {
  let mut result = @logic.TySubstitution::new()
  for entry in self.type_variables {
    let normalized = self.resolve_inference_variables(entry.1, span)
    result = result.bind(entry.0, normalized.to_ty(span), span)
  }
  result
}

///|
fn remapped_program_variable(
  substitutions : ArrayView[(PVariable, PVariable)],
  variable : PVariable,
) -> PVariable {
  for entry in substitutions {
    if entry.0 == variable {
      return entry.1
    }
  }
  variable
}

///|
fn add_program_substitution(
  substitutions : Array[(PVariable, PVariable)],
  source : PVariable,
  target : PVariable,
) -> Unit {
  for index = 0; index < substitutions.length(); index = index + 1 {
    if substitutions[index].0 == source {
      substitutions[index] = (source, target)
      return
    }
  }
  substitutions.push((source, target))
}

///|
fn instantiate_postconditions(
  instantiation : CtyTermInstantiation,
  posts : ArrayView[Postcondition],
  span : @identity.SourceSpan?,
) -> Array[Postcondition] raise {
  let result : Array[Postcondition] = []
  for postcondition in posts {
    let post = postcondition.view()
    let replacement = instantiation.clone_variable(post.result, span)
    let variables = instantiation.variables.copy()
    variables[post.result] = replacement
    result.push(
      Postcondition::trusted_new(
        replacement,
        instantiation.term_with(post.formula, variables, span),
        span,
      ),
    )
  }
  result
}

///|
pub fn Cty::apply(
  self : Cty,
  context : @identity.CompilationContext,
  applied : ArrayView[PVariable],
  remaining_types : ArrayView[Ity],
  result : Ity,
  span : @identity.SourceSpan?,
) -> Cty raise {
  if applied.length() > self.arguments.length() ||
    remaining_types.length() != self.arguments.length() - applied.length() {
    fail_mlw(
      InvalidComputationType,
      span,
      "computation type application has the wrong arity",
    )
  }
  if !context.contains(result.context_anchor()) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "computation type application belongs to another context",
    )
  }
  let mut substitution = self.freeze
  let mut ghost = self.effect.view().ghost
  for index = 0; index < applied.length(); index = index + 1 {
    let formal = self.arguments[index]
    let actual = applied[index]
    require_mlw_context(result.context_anchor(), actual.semantic_id(), span)
    substitution = substitution.match_ity(
      formal.view().ity,
      actual.view().ity,
      span,
    )
    ghost = ghost || (actual.view().ghost && !formal.view().ghost)
  }
  for index = 0; index < remaining_types.length(); index = index + 1 {
    substitution = substitution.match_ity(
      self.arguments[index + applied.length()].view().ity,
      remaining_types[index],
      span,
    )
  }
  substitution = substitution.match_ity(self.result, result, span)
  let logic_substitution = substitution.logic_substitution(span)
  let target_logic_substitution = substitution.inference_logic_substitution(
    span,
  )
  let term_instantiation = CtyTermInstantiation::new(
    context, logic_substitution, target_logic_substitution,
  )
  let program_substitutions : Array[(PVariable, PVariable)] = []
  for index = 0; index < applied.length(); index = index + 1 {
    let formal = self.arguments[index]
    let actual = applied[index]
    add_program_substitution(program_substitutions, formal, actual)
    term_instantiation.bind(
      formal.view().pure_symbol,
      formal.view().ity,
      actual.view().pure_symbol,
      actual.view().ity,
      span,
    )
  }
  let remaining_arguments : Array[PVariable] = []
  for index = 0; index < remaining_types.length(); index = index + 1 {
    let formal = self.arguments[index + applied.length()]
    let replacement = PVariable::trusted_new(
      context,
      formal.view().name,
      remaining_types[index],
      formal.view().ghost,
      span,
    )
    remaining_arguments.push(replacement)
    add_program_substitution(program_substitutions, formal, replacement)
    term_instantiation.bind(
      formal.view().pure_symbol,
      formal.view().ity,
      replacement.view().pure_symbol,
      replacement.view().ity,
      span,
    )
  }
  for variable in self.program_variables {
    if program_substitutions.any(entry => entry.0 == variable) {
      continue
    }
    let instantiated_ity = substitution.instantiate(variable.view().ity, span)
    let replacement = if instantiated_ity == variable.view().ity {
      variable
    } else {
      PVariable::trusted_new(
        context,
        variable.view().name,
        instantiated_ity,
        variable.view().ghost,
        span,
      )
    }
    add_program_substitution(program_substitutions, variable, replacement)
    term_instantiation.bind(
      variable.view().pure_symbol,
      variable.view().ity,
      replacement.view().pure_symbol,
      replacement.view().ity,
      span,
    )
  }
  let oldies : Array[OldSnapshot] = []
  for oldie in self.oldies {
    let source = oldie.view()
    let original = remapped_program_variable(
      program_substitutions,
      source.original,
    )
    let preliminary = remapped_program_variable(
      program_substitutions,
      source.snapshot,
    )
    let snapshot_ity = original.view().ity.purify()
    let snapshot = if preliminary.view().ghost &&
      preliminary.view().ity == snapshot_ity {
      preliminary
    } else {
      let corrected = PVariable::trusted_new(
        context,
        source.snapshot.view().name,
        snapshot_ity,
        true,
        span,
      )
      add_program_substitution(
        program_substitutions,
        source.snapshot,
        corrected,
      )
      term_instantiation.variables[source.snapshot.view().pure_symbol] = corrected.view().pure_symbol
      corrected
    }
    oldies.push(OldSnapshot::new(snapshot, original, span))
  }
  let effect = self.effect
    .instantiate(substitution, span)
    .remap_variables(program_substitutions)
    .ghostify(ghost, span)
    .read_pre(applied, span)
  let exceptional : Array[ExceptionalPostconditions] = []
  for entry in self.exceptional_postconditions {
    exceptional.push(
      ExceptionalPostconditions::new(
        entry.exception,
        instantiate_postconditions(
          term_instantiation,
          entry.postconditions,
          span,
        ),
        span,
      ),
    )
  }
  let mut freeze = self.freeze
  for variable in applied {
    freeze = freeze.freeze(variable.view().ity, span)
  }
  let variables = collect_cty_variables(remaining_arguments, effect, oldies)
  Cty::trusted_new_full(
    result.context_anchor(),
    variables,
    remaining_arguments,
    self.preconditions.map(precondition => {
      term_instantiation.term(precondition, span)
    }),
    instantiate_postconditions(term_instantiation, self.postconditions, span),
    exceptional,
    oldies,
    effect,
    result,
    self.mask,
    freeze,
    span,
  )
}

///|
/// Why3 rebuilds a fully applied tuple constructor with `cty_tuple`, so the
/// result mask records each actual component instead of ghostifying the whole
/// tuple when only some arguments are ghost.
fn Cty::tuple_application(
  self : Cty,
  arguments : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  let mask = ProgramMask::Tuple(arguments.map(ProgramMask::of_variable))
    .reduce()
    .validate_for_ity(self.result, span)
  { ..self, effect: Effect::from_reads(arguments, mask is Ghost), mask }
}

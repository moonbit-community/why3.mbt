// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct Postcondition {
  result : @logic.VSymbol
  formula : @logic.Term
}

///|
pub(all) struct PostconditionView {
  result : @logic.VSymbol
  formula : @logic.Term
}

///|
struct Cty {
  program_variables : Array[PVariable]
  arguments : Array[PVariable]
  preconditions : Array[@logic.Term]
  postconditions : Array[Postcondition]
  effect : Effect
  result : Ity
  mask : ProgramMask
}

///|
pub(all) struct CtyView {
  program_variables : ArrayView[PVariable]
  arguments : ArrayView[PVariable]
  preconditions : ArrayView[@logic.Term]
  postconditions : ArrayView[Postcondition]
  effect : Effect
  result : Ity
  mask : ProgramMask
}

///|
pub fn Postcondition::trusted_new(
  result : @logic.VSymbol,
  formula : @logic.Term,
  span : @identity.SourceSpan?,
) -> Postcondition raise MlwError {
  if !formula.is_formula() {
    fail_mlw(InvalidComputationType, span, "postcondition must be a formula")
  }
  { result, formula }
}

///|
pub fn Postcondition::view(self : Postcondition) -> PostconditionView {
  { result: self.result, formula: self.formula }
}

///|
pub fn Cty::trusted_new(
  anchor : @identity.SemanticId,
  program_variables : ArrayView[PVariable],
  arguments : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  effect : Effect,
  result : Ity,
  mask : ProgramMask,
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  let variables = program_variables.to_owned()
  let known : Map[PVariable, Unit] = Map([])
  for variable in variables {
    require_mlw_context(anchor, variable.semantic_id(), span)
    if known.contains(variable) {
      fail_mlw(InvalidComputationType, span, "duplicate program variable")
    }
    known[variable] = ()
  }
  let arguments = arguments.to_owned()
  for argument in arguments {
    if !known.contains(argument) {
      fail_mlw(
        InvalidComputationType,
        span,
        "argument is absent from Cty variables",
      )
    }
  }
  let preconditions = preconditions.to_owned()
  for precondition in preconditions {
    if !precondition.is_formula() {
      fail_mlw(InvalidComputationType, span, "precondition must be a formula")
    }
  }
  require_mlw_context(anchor, result.context_anchor(), span)
  {
    program_variables: variables,
    arguments,
    preconditions,
    postconditions: postconditions.to_owned(),
    effect,
    result,
    mask,
  }
}

///|
pub fn Cty::context_anchor(self : Cty) -> @identity.SemanticId {
  self.result.context_anchor()
}

///|
pub fn Cty::view(self : Cty) -> CtyView {
  {
    program_variables: self.program_variables[:],
    arguments: self.arguments[:],
    preconditions: self.preconditions[:],
    postconditions: self.postconditions[:],
    effect: self.effect,
    result: self.result,
    mask: self.mask,
  }
}

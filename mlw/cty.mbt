// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

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
struct ExceptionalPostconditions {
  exception : XSymbol
  postconditions : Array[Postcondition]
}

///|
pub(all) struct ExceptionalPostconditionsView {
  exception : XSymbol
  postconditions : ArrayView[Postcondition]
}

///|
struct OldSnapshot {
  snapshot : PVariable
  original : PVariable
}

///|
pub(all) struct OldSnapshotView {
  snapshot : PVariable
  original : PVariable
}

///|
struct Cty {
  program_variables : Array[PVariable]
  arguments : Array[PVariable]
  preconditions : Array[@logic.Term]
  postconditions : Array[Postcondition]
  exceptional_postconditions : Array[ExceptionalPostconditions]
  oldies : Array[OldSnapshot]
  effect : Effect
  result : Ity
  mask : ProgramMask
  freeze : ItySubstitution
}

///|
pub(all) struct CtyView {
  program_variables : ArrayView[PVariable]
  arguments : ArrayView[PVariable]
  preconditions : ArrayView[@logic.Term]
  postconditions : ArrayView[Postcondition]
  exceptional_postconditions : ArrayView[ExceptionalPostconditions]
  oldies : ArrayView[OldSnapshot]
  effect : Effect
  result : Ity
  mask : ProgramMask
  freeze : ItySubstitution
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
pub fn ExceptionalPostconditions::new(
  exception : XSymbol,
  postconditions : ArrayView[Postcondition],
  span : @identity.SourceSpan?,
) -> ExceptionalPostconditions raise MlwError {
  let postconditions = postconditions.to_owned()
  for postcondition in postconditions {
    let post = postcondition.view()
    require_mlw_context(exception.id, post.result.semantic_id(), span)
  }
  { exception, postconditions }
}

///|
pub fn ExceptionalPostconditions::view(
  self : ExceptionalPostconditions,
) -> ExceptionalPostconditionsView {
  { exception: self.exception, postconditions: self.postconditions[:] }
}

///|
pub fn OldSnapshot::new(
  snapshot : PVariable,
  original : PVariable,
  span : @identity.SourceSpan?,
) -> OldSnapshot raise MlwError {
  let snapshot_view = snapshot.view()
  let original_view = original.view()
  require_mlw_context(snapshot.id, original.id, span)
  if !snapshot_view.ghost || snapshot_view.ity != original_view.ity.purify() {
    fail_mlw(
      InvalidOldSnapshot,
      span,
      "old snapshot must be ghost and purify its original variable",
    )
  }
  { snapshot, original }
}

///|
pub fn OldSnapshot::view(self : OldSnapshot) -> OldSnapshotView {
  { snapshot: self.snapshot, original: self.original }
}

///|
fn append_program_variable(
  variables : Array[PVariable],
  variable : PVariable,
) -> Unit {
  if !variables.any(existing => existing == variable) {
    variables.push(variable)
  }
}

///|
fn collect_cty_variables(
  arguments : ArrayView[PVariable],
  effect : Effect,
  oldies : ArrayView[OldSnapshot],
) -> Array[PVariable] {
  let variables : Array[PVariable] = []
  for argument in arguments {
    append_program_variable(variables, argument)
  }
  for read in effect.view().reads {
    append_program_variable(variables, read)
  }
  for oldie in oldies {
    append_program_variable(variables, oldie.snapshot)
    append_program_variable(variables, oldie.original)
  }
  variables
}

///|
fn find_program_variable(
  variables : ArrayView[PVariable],
  symbol : @logic.VSymbol,
) -> PVariable? {
  for variable in variables {
    if variable.view().pure_symbol == symbol {
      return Some(variable)
    }
  }
  None
}

///|
fn collect_formula_program_variables(
  formula : @logic.Term,
  variables : ArrayView[PVariable],
  bound : ArrayView[@logic.VSymbol],
  span : @identity.SourceSpan?,
) -> Array[PVariable] raise MlwError {
  let reads : Array[PVariable] = []
  for symbol in formula.free_variables() {
    if bound.any(variable => variable == symbol) {
      continue
    }
    guard find_program_variable(variables, symbol) is Some(variable) else {
      fail_mlw(
        UnboundSpecificationVariable,
        span,
        "specification references an unknown program variable",
      )
    }
    append_program_variable(reads, variable)
  }
  reads
}

///|
fn append_formula_program_variables(
  reads : Array[PVariable],
  formula : @logic.Term,
  variables : ArrayView[PVariable],
  bound : ArrayView[@logic.VSymbol],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for
    variable in collect_formula_program_variables(
      formula, variables, bound, span,
    ) {
    append_program_variable(reads, variable)
  }
}

///|
fn validate_formula_variables(
  formula : @logic.Term,
  variables : ArrayView[PVariable],
  additional : ArrayView[@logic.VSymbol],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for variable in formula.free_variables() {
    if !additional.any(symbol => symbol == variable) &&
      find_program_variable(variables, variable) is None {
      fail_mlw(
        UnboundSpecificationVariable,
        span,
        "specification references an unbound program variable",
      )
    }
  }
}

///|
fn validate_postcondition_type(
  postcondition : Postcondition,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let expected = ity.to_ty(span) catch {
    TypeError(_) =>
      fail_mlw(
        InvalidComputationType,
        span,
        "postcondition result type is invalid",
      )
  }
  if postcondition.result.ty() != expected {
    fail_mlw(
      InvalidComputationType,
      span,
      "postcondition result has the wrong type",
    )
  }
}

///|
fn validate_specification_type_variables(
  variables : ArrayView[PVariable],
  raises : ArrayView[XSymbol],
  result : Ity,
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  exceptional : ArrayView[ExceptionalPostconditions],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let allowed = result.free_type_variables()
  for variable in variables {
    for type_variable in variable.view().ity.free_type_variables() {
      if !allowed.any(existing => existing == type_variable) {
        allowed.push(type_variable)
      }
    }
  }
  for exception in raises {
    for type_variable in exception.view().ity.free_type_variables() {
      if !allowed.any(existing => existing == type_variable) {
        allowed.push(type_variable)
      }
    }
  }
  fn check(
    term : @logic.Term,
    allowed : ArrayView[@logic.TyVarSymbol],
    span : @identity.SourceSpan?,
  ) -> Unit raise MlwError {
    for variable in term.free_type_variables() {
      if !allowed.any(existing => existing == variable) {
        fail_mlw(
          UnboundProgramTypeVariable,
          span,
          "specification contains an unbound type variable",
        )
      }
    }
  }

  for precondition in preconditions {
    check(precondition, allowed, span)
  }
  for postcondition in postconditions {
    check(postcondition.formula, allowed, span)
  }
  for entry in exceptional {
    for postcondition in entry.postconditions {
      check(postcondition.formula, allowed, span)
    }
  }
}

///|
fn exceptional_post_is_false(
  exception : XSymbol,
  exceptional_postconditions : ArrayView[ExceptionalPostconditions],
) -> Bool {
  for entry in exceptional_postconditions {
    if entry.exception == exception && entry.postconditions.length() == 1 {
      return entry.postconditions[0].formula.view() is Tfalse
    }
  }
  false
}

///|
fn append_ity_reachable_regions(regions : Array[Region], ity : Ity) -> Unit {
  for region in ity.reachable_regions() {
    if !regions.any(existing => existing == region) {
      regions.push(region)
    }
  }
}

///|
fn append_ity_reachable_type_variables(
  variables : Array[@logic.TyVarSymbol],
  ity : Ity,
) -> Unit {
  for variable in ity.reachable_type_variables() {
    if !variables.any(existing => existing == variable) {
      variables.push(variable)
    }
  }
}

///|
fn computation_escape_type_variables(
  effect : Effect,
  result : Ity,
  span : @identity.SourceSpan?,
) -> Array[@logic.TyVarSymbol] raise MlwError {
  let variables : Array[@logic.TyVarSymbol] = []
  append_ity_reachable_type_variables(variables, result)
  for exception in effect.raises {
    append_ity_reachable_type_variables(variables, exception.view().ity)
  }
  for write in effect.writes {
    for field in write.fields {
      append_ity_reachable_type_variables(
        variables,
        write.region.instantiate_member_ity(field.view().ity, span),
      )
    }
  }
  variables
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
  Cty::trusted_new_full(
    anchor,
    program_variables,
    arguments,
    preconditions,
    postconditions,
    [],
    [],
    effect,
    result,
    mask,
    ItySubstitution::empty(),
    span,
  )
}

///|
pub fn Cty::trusted_new_full(
  anchor : @identity.SemanticId,
  program_variables : ArrayView[PVariable],
  arguments : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  exceptional_postconditions : ArrayView[ExceptionalPostconditions],
  oldies : ArrayView[OldSnapshot],
  effect : Effect,
  result : Ity,
  mask : ProgramMask,
  freeze : ItySubstitution,
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
  let argument_set : Map[PVariable, Unit] = Map([])
  for argument in arguments {
    if !known.contains(argument) {
      fail_mlw(
        InvalidComputationType,
        span,
        "argument is absent from Cty variables",
      )
    }
    if argument_set.contains(argument) {
      fail_mlw(InvalidComputationType, span, "duplicate Cty argument")
    }
    argument_set[argument] = ()
  }
  let preconditions = preconditions.to_owned()
  for precondition in preconditions {
    if !precondition.is_formula() {
      fail_mlw(InvalidComputationType, span, "precondition must be a formula")
    }
    validate_formula_variables(precondition, variables, [], span)
  }
  let postconditions = postconditions.to_owned()
  for postcondition in postconditions {
    validate_postcondition_type(postcondition, result, span)
    validate_formula_variables(
      postcondition.formula,
      variables,
      [postcondition.result],
      span,
    )
  }
  let exceptional_postconditions = exceptional_postconditions.to_owned()
  let exception_set : Map[XSymbol, Unit] = Map([])
  for entry in exceptional_postconditions {
    if exception_set.contains(entry.exception) {
      fail_mlw(
        InvalidComputationType,
        span,
        "duplicate exceptional postcondition entry",
      )
    }
    exception_set[entry.exception] = ()
    for postcondition in entry.postconditions {
      validate_postcondition_type(
        postcondition,
        entry.exception.view().ity,
        span,
      )
      validate_formula_variables(
        postcondition.formula,
        variables,
        [postcondition.result],
        span,
      )
    }
  }
  let oldies = oldies.to_owned()
  let snapshots : Map[PVariable, Unit] = Map([])
  for oldie in oldies {
    if snapshots.contains(oldie.snapshot) ||
      argument_set.contains(oldie.snapshot) {
      fail_mlw(InvalidOldSnapshot, span, "old snapshot is not fresh")
    }
    snapshots[oldie.snapshot] = ()
  }
  require_mlw_context(anchor, result.context_anchor(), span)
  let mask = mask.validate_for_ity(result, span)
  validate_specification_type_variables(
    variables,
    effect.view().raises,
    result,
    preconditions,
    postconditions,
    exceptional_postconditions,
    span,
  )
  {
    program_variables: variables,
    arguments,
    preconditions,
    postconditions,
    exceptional_postconditions,
    oldies,
    effect,
    result,
    mask: if effect.view().ghost {
      Ghost
    } else {
      mask
    },
    freeze,
  }
}

///|
/// Mirrors Why3's `create_cty`. `program_variables` supplies the restoration
/// table used to map free logical variables in specifications back to their
/// program-variable identities.
pub fn Cty::new_with_variables(
  program_variables : ArrayView[PVariable],
  arguments : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  exceptional_postconditions : ArrayView[ExceptionalPostconditions],
  oldies : ArrayView[OldSnapshot],
  effect : Effect,
  result : Ity,
  span : @identity.SourceSpan?,
  mask? : ProgramMask = Visible,
  defensive? : Bool = false,
) -> Cty raise MlwError {
  let arguments = arguments.to_owned()
  let preconditions = preconditions.to_owned()
  let postconditions = postconditions.to_owned()
  let exceptional_postconditions = exceptional_postconditions.to_owned()
  let oldies = oldies.to_owned()
  let variable_pool = program_variables.to_owned()
  for argument in arguments {
    append_program_variable(variable_pool, argument)
  }
  for read in effect.reads {
    append_program_variable(variable_pool, read)
  }
  for oldie in oldies {
    append_program_variable(variable_pool, oldie.snapshot)
    append_program_variable(variable_pool, oldie.original)
  }

  // Complete reads from preconditions, postconditions, and arguments.
  let precondition_reads = arguments.copy()
  for precondition in preconditions {
    append_formula_program_variables(
      precondition_reads,
      precondition,
      variable_pool,
      [],
      span,
    )
  }
  let postcondition_reads : Array[PVariable] = []
  for postcondition in postconditions {
    append_formula_program_variables(
      postcondition_reads,
      postcondition.formula,
      variable_pool,
      [postcondition.result],
      span,
    )
  }
  for entry in exceptional_postconditions {
    for postcondition in entry.postconditions {
      append_formula_program_variables(
        postcondition_reads,
        postcondition.formula,
        variable_pool,
        [postcondition.result],
        span,
      )
    }
  }

  let mut effect = effect
  effect = effect.read_post(postcondition_reads, span)

  // Retain only snapshots used after execution, replace those reads with the
  // corresponding original values, and reject snapshots visible beforehand.
  let retained_oldies : Array[OldSnapshot] = []
  let snapshots : Array[PVariable] = []
  for oldie in oldies {
    if effect.reads.any(read => read == oldie.snapshot) {
      retained_oldies.push(oldie)
      append_program_variable(snapshots, oldie.snapshot)
    }
  }
  effect = effect.bind(snapshots)
  for oldie in retained_oldies {
    append_program_variable(precondition_reads, oldie.original)
  }
  for snapshot in snapshots {
    if precondition_reads.any(read => read == snapshot) {
      fail_mlw(
        InvalidOldSnapshot,
        span,
        "old snapshot collides with an argument or pre-state read",
      )
    }
  }
  effect = effect.read_pre(precondition_reads, span)

  let external_reads : Array[PVariable] = []
  for read in effect.reads {
    if !arguments.any(argument => argument == read) {
      external_reads.push(read)
    }
  }
  let mut freeze = ItySubstitution::empty()
  for variable in external_reads {
    freeze = freeze.freeze(variable.view().ity, span)
  }
  for exception in effect.raises {
    freeze = freeze.freeze(exception.view().ity, span)
  }

  // A singleton `false` exceptional postcondition makes that exit impossible.
  let possible_raises : Array[XSymbol] = []
  for exception in effect.raises {
    if !exceptional_post_is_false(exception, exceptional_postconditions) {
      possible_raises.push(exception)
    }
  }
  effect = { ..effect, raises: possible_raises }

  // Resets invalidate writes and taints not covered by the final value.
  let retained_writes : Array[EffectWrite] = []
  for write in effect.writes {
    if effect.covers.any(region => region == write.region) {
      retained_writes.push(write)
    }
  }
  let retained_taints : Array[Region] = []
  for taint in effect.taints {
    if effect.covers.any(region => region == taint) {
      retained_taints.push(taint)
    }
  }
  effect = { ..effect, writes: retained_writes, taints: retained_taints }

  // Effects cannot mention regions that do not escape through a read, result,
  // or raised exception.
  let known_read_regions = read_regions(effect.reads)
  let known_value_regions = known_read_regions.copy()
  append_ity_reachable_regions(known_value_regions, result)
  for exception in effect.raises {
    append_ity_reachable_regions(known_value_regions, exception.view().ity)
  }
  let live_writes : Array[EffectWrite] = []
  for write in effect.writes {
    if known_read_regions.any(region => region == write.region) {
      live_writes.push(write)
    }
  }
  let live_covers : Array[Region] = []
  for cover in effect.covers {
    if known_read_regions.any(region => region == cover) {
      live_covers.push(cover)
    }
  }
  let live_resets : Array[Region] = []
  for reset in effect.resets {
    if known_value_regions.any(region => region == reset) {
      live_resets.push(reset)
    }
  }
  effect = {
    ..effect,
    writes: live_writes,
    covers: live_covers,
    resets: live_resets,
  }.reset_taints(span)

  // Immutable variables only matter when their instantiated types escape.
  let escape = computation_escape_type_variables(effect, result, span)
  let live_spoils : Array[@logic.TyVarSymbol] = []
  for variable in effect.spoils {
    if escape.any(escaped => escaped == variable) {
      live_spoils.push(variable)
    }
  }
  effect = { ..effect, spoils: live_spoils }

  if defensive {
    let defensive_resets : Array[Region] = []
    for region in known_value_regions {
      if !known_read_regions.any(known => known == region) {
        defensive_resets.push(region)
      }
    }
    effect = {
      ..effect,
      resets: merge_regions(effect.resets, defensive_resets),
      spoils: escape,
    }
  }

  effect = { ..effect, reads: external_reads }
  let variables = collect_cty_variables(arguments, effect, retained_oldies)
  Cty::trusted_new_full(
    result.context_anchor(),
    variables,
    arguments,
    preconditions,
    postconditions,
    exceptional_postconditions,
    retained_oldies,
    effect,
    result,
    mask,
    freeze,
    span,
  )
}

///|
pub fn Cty::new(
  arguments : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  exceptional_postconditions : ArrayView[ExceptionalPostconditions],
  oldies : ArrayView[OldSnapshot],
  effect : Effect,
  result : Ity,
  span : @identity.SourceSpan?,
  mask? : ProgramMask = Visible,
  defensive? : Bool = false,
) -> Cty raise MlwError {
  Cty::new_with_variables(
    collect_cty_variables(arguments, effect, oldies),
    arguments,
    preconditions,
    postconditions,
    exceptional_postconditions,
    oldies,
    effect,
    result,
    span,
    mask~,
    defensive~,
  )
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
    exceptional_postconditions: self.exceptional_postconditions[:],
    oldies: self.oldies[:],
    effect: self.effect,
    result: self.result,
    mask: self.mask,
    freeze: self.freeze,
  }
}

///|
fn function_value_ity(
  function_type : ProgramTypeSymbol,
  parameter : Ity,
  result : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise {
  let view = function_type.view()
  if view.logic_type.name() != b"infix ->" || view.logic_type.arity() != 2 {
    fail_mlw(
      InvalidComputationType,
      span,
      "function execution requires the builtin program function type",
    )
  }
  Ity::app(function_type, [parameter, result], span)
}

///|
fn function_value_result(
  function : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match function.view() {
    ItyApp(symbol, arguments, regions) if symbol.view().logic_type.name() ==
      b"infix ->" &&
      arguments.length() == 2 &&
      regions.is_empty() => arguments[1]
    _ =>
      fail_mlw(
        InvalidComputationType,
        span,
        "function-valued computation has an invalid result type",
      )
  }
}

///|
fn apply_function_result(
  application : @logic.LSymbol,
  function : @logic.Term,
  argument : PVariable,
  result : Ity,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  @logic.Term::elaborated_apply(
    application,
    [function, @logic.Term::variable(argument.view().pure_symbol)],
    Some(result.to_ty(span)),
    span,
  )
}

///|
/// Converts a routine computation with remaining parameters into the
/// function-valued computation type attached to an executable MLW expression.
/// This is Why3's `cty_exec` boundary: constructing the mapping is pure, while
/// its pre/postconditions are closed over the remaining arguments.
pub fn Cty::execute_as_function(
  self : Cty,
  context : @identity.CompilationContext,
  function_type : ProgramTypeSymbol,
  application : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> Cty raise {
  if self.arguments.is_empty() {
    return self
  }
  let effect_view = self.effect.view()
  if !self.effect.is_pure() || !effect_view.resets.is_empty() {
    fail_mlw(
      InvalidComputationType,
      span,
      "effectful computation cannot be used as a function value",
    )
  }
  if !self.freeze.view().regions.is_empty() {
    fail_mlw(
      InvalidComputationType,
      span,
      "stateful computation cannot be used as a function value",
    )
  }
  if !self.exceptional_postconditions.is_empty() {
    fail_mlw(
      InvalidComputationType,
      span,
      "function-valued computation cannot retain exceptional postconditions",
    )
  }
  let application_view = application.view()
  if application_view.name != b"infix @" ||
    application_view.argument_types.length() != 2 ||
    application_view.result_type is None {
    fail_mlw(
      InvalidComputationType,
      span,
      "function execution requires the builtin application symbol",
    )
  }
  let mut function_result = self.result
  for argument in self.arguments.rev() {
    function_result = function_value_ity(
      function_type,
      argument.view().ity,
      function_result,
      span,
    )
  }
  let argument_symbols = self.arguments.map(argument => {
    argument.view().pure_symbol
  })
  let mut old_substitution = @logic.TermSubstitution::new()
  for oldie in self.oldies {
    old_substitution = old_substitution.bind(
      oldie.snapshot.view().pure_symbol,
      @logic.Term::variable(oldie.original.view().pure_symbol),
      span,
    )
  }
  let preconditions : Array[@logic.Term] = []
  for precondition in self.preconditions {
    preconditions.push(
      @logic.Term::quantify(
        ForallQuantifier,
        argument_symbols,
        [],
        old_substitution.apply(context, precondition, span),
        span,
      ),
    )
  }
  let postconditions : Array[Postcondition] = []
  for postcondition in self.postconditions {
    let post = postcondition.view()
    let result_symbol = @logic.VSymbol::new(
      context,
      post.result.view().name,
      post.result.view().origin,
      function_result.to_ty(span),
      span,
    )
    let mut applied_result = @logic.Term::variable(result_symbol)
    let mut applied_type = function_result
    for argument in self.arguments {
      let next_type = function_value_result(applied_type, span)
      applied_result = apply_function_result(
        application, applied_result, argument, next_type, span,
      )
      applied_type = next_type
    }
    let substitution = old_substitution.bind(post.result, applied_result, span)
    postconditions.push(
      Postcondition::trusted_new(
        result_symbol,
        @logic.Term::quantify(
          ForallQuantifier,
          argument_symbols,
          [],
          substitution.apply(context, post.formula, span),
          span,
        ),
        span,
      ),
    )
  }
  let ghost = self.mask.is_ghost() ||
    self.arguments.any(argument => argument.view().ghost)
  let effect = self.effect.ghostify(ghost, span)
  Cty::new_with_variables(
    self.program_variables,
    [],
    preconditions,
    postconditions,
    [],
    [],
    effect,
    function_result,
    span,
    mask=Visible,
  )
}

///|
pub fn Cty::reads(self : Cty) -> ArrayView[PVariable] {
  self.effect.view().reads
}

///|
/// Adds pre-state dependencies while keeping arguments instantiable and
/// freezing only newly captured external variables.
pub fn Cty::read_pre(
  self : Cty,
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  let additions : Array[PVariable] = []
  let variables = self.program_variables.copy()
  for variable in reads {
    require_mlw_context(self.context_anchor(), variable.semantic_id(), span)
    append_program_variable(variables, variable)
    if !self.effect.reads.any(existing => existing == variable) &&
      !self.arguments.any(argument => argument == variable) {
      append_program_variable(additions, variable)
    }
  }
  if additions.is_empty() {
    return { ..self, program_variables: variables }
  }
  let mut freeze = self.freeze
  for variable in additions {
    freeze = freeze.freeze(variable.view().ity, span)
  }
  {
    ..self,
    program_variables: variables,
    effect: self.effect.read_pre(additions, span),
    freeze,
  }
}

///|
/// Adds post-state dependencies after checking updates and stale regions.
/// Existing `old` snapshots remain represented by their original reads.
pub fn Cty::read_post(
  self : Cty,
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  for variable in reads {
    require_mlw_context(self.context_anchor(), variable.semantic_id(), span)
  }
  check_writes(self.effect.writes, reads, span)
  check_covers(self.effect.resets, self.effect.covers, reads, span)
  let snapshots = [ for oldie in self.oldies => oldie.snapshot ]
  let original_reads : Array[PVariable] = []
  for variable in reads {
    if !snapshots.any(snapshot => snapshot == variable) {
      original_reads.push(variable)
    }
  }
  self.read_pre(original_reads, span)
}

///|
pub fn Cty::add_preconditions_with_variables(
  self : Cty,
  program_variables : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  if preconditions.is_empty() {
    return self
  }
  let pool = self.program_variables.copy()
  for variable in program_variables {
    append_program_variable(pool, variable)
  }
  let reads : Array[PVariable] = []
  for precondition in preconditions {
    if !precondition.is_formula() {
      fail_mlw(InvalidComputationType, span, "precondition must be a formula")
    }
    append_formula_program_variables(reads, precondition, pool, [], span)
  }
  let updated = self.read_pre(reads, span)
  let known = updated.effect.reads.copy()
  for argument in updated.arguments {
    append_program_variable(known, argument)
  }
  validate_specification_type_variables(
    known,
    updated.effect.raises,
    updated.result,
    preconditions,
    [],
    [],
    span,
  )
  { ..updated, preconditions: preconditions.to_owned() + updated.preconditions }
}

///|
pub fn Cty::add_preconditions(
  self : Cty,
  preconditions : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  self.add_preconditions_with_variables(
    self.program_variables,
    preconditions,
    span,
  )
}

///|
pub fn Cty::add_postconditions_with_variables(
  self : Cty,
  program_variables : ArrayView[PVariable],
  postconditions : ArrayView[Postcondition],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  if postconditions.is_empty() {
    return self
  }
  let pool = self.program_variables.copy()
  for variable in program_variables {
    append_program_variable(pool, variable)
  }
  let reads : Array[PVariable] = []
  for postcondition in postconditions {
    validate_postcondition_type(postcondition, self.result, span)
    append_formula_program_variables(
      reads,
      postcondition.formula,
      pool,
      [postcondition.result],
      span,
    )
  }
  let updated = self.read_post(reads, span)
  let known = updated.effect.reads.copy()
  for argument in updated.arguments {
    append_program_variable(known, argument)
  }
  validate_specification_type_variables(
    known,
    updated.effect.raises,
    updated.result,
    [],
    postconditions,
    [],
    span,
  )
  {
    ..updated,
    postconditions: postconditions.to_owned() + updated.postconditions,
  }
}

///|
pub fn Cty::add_postconditions(
  self : Cty,
  postconditions : ArrayView[Postcondition],
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  self.add_postconditions_with_variables(
    self.program_variables,
    postconditions,
    span,
  )
}

///|
pub fn Cty::is_ghost(self : Cty) -> Bool {
  self.effect.view().ghost
}

///|
pub fn Cty::is_pure(self : Cty) -> Bool {
  if !self.effect.is_pure() {
    return false
  }
  let live = self.effect.view().reads.to_owned() + self.arguments
  !live.any(variable => {
    variable.view().ity.has_stale_region(
      self.effect.view().resets,
      self.effect.view().covers,
    )
  })
}

///|
pub fn Cty::ghostify(
  self : Cty,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  if !ghost || self.effect.view().ghost {
    return self
  }
  { ..self, effect: self.effect.ghostify(true, span), mask: Ghost }
}

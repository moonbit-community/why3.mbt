// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) struct ProgramTypeArgumentFlag {
  frozen : Bool
  exposed : Bool
  liable : Bool
  fixed : Bool
  visible : Bool
} derive(Eq, Debug)

///|
pub(all) struct ProgramTypeFlags {
  nonfree : Bool
  private_ : Bool
  mutable_ : Bool
  fragile : Bool
  argument_flags : Array[ProgramTypeArgumentFlag]
  region_flags : Array[ProgramTypeArgumentFlag]
} derive(Eq, Debug)

///|
pub(all) enum ProgramTypeDefinition {
  ProgramNoDef
  ProgramAlias(Ity)
  ProgramRange(BigInt, BigInt)
  ProgramFloat(Int, Int)
}

///|
struct ProgramTypeSymbol {
  context : @identity.CompilationContext
  id : @identity.SemanticId
  logic_type : @logic.TypeSymbol
  origin : @identity.Origin
  flags : ProgramTypeFlags
  definition : ProgramTypeDefinition
  mutable_fields : Array[PVariable]
  immutable_fields : Array[PVariable]
  mut invariants : Array[@logic.Term]
  mut regions : Array[Region]
}

///|
priv enum ItyNode {
  ItyVariable(@logic.TyVarSymbol)
  ItyApplication(ProgramTypeSymbol, Array[Ity], Array[Ity])
  ItyRegion(Region)
}

///|
struct Ity {
  node : ItyNode
}

///|
struct Region {
  id : @identity.SemanticId
  name : @theory.SemanticName
  symbol : ProgramTypeSymbol
  arguments : Array[Ity]
  regions : Array[Ity]
  inference : Bool
}

///|
struct PVariable {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  ghost : Bool
  pure_symbol : @logic.VSymbol
}

///|
struct XSymbol {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  mask : ProgramMask
}

///|
pub(all) struct ProgramTypeSymbolView {
  id : @identity.SemanticId
  logic_type : @logic.TypeSymbol
  origin : @identity.Origin
  flags : ProgramTypeFlags
  definition : ProgramTypeDefinition
  mutable_fields : ArrayView[PVariable]
  immutable_fields : ArrayView[PVariable]
  invariants : ArrayView[@logic.Term]
  regions : ArrayView[Region]
}

///|
pub(all) enum ItyView {
  ItyVar(@logic.TyVarSymbol)
  ItyApp(ProgramTypeSymbol, ArrayView[Ity], ArrayView[Ity])
  ItyReg(Region)
}

///|
pub(all) struct RegionView {
  id : @identity.SemanticId
  name : @theory.SemanticName
  symbol : ProgramTypeSymbol
  arguments : ArrayView[Ity]
  regions : ArrayView[Ity]
  inference : Bool
}

///|
pub(all) struct PVariableView {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  ghost : Bool
  pure_symbol : @logic.VSymbol
}

///|
pub(all) struct XSymbolView {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  mask : ProgramMask
}

///|
fn make_program_type_symbol(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  flags : ProgramTypeFlags,
  definition : ProgramTypeDefinition,
  mutable_fields : ArrayView[PVariable],
  immutable_fields : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  let anchor = logic_type.semantic_id()
  if !context.contains(anchor) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "program type belongs to another context",
    )
  }
  if flags.argument_flags.length() != logic_type.arity() {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "program type argument flags do not match logical arity",
    )
  }
  match definition {
    ProgramAlias(target) =>
      require_mlw_context(anchor, target.context_anchor(), span)
    ProgramNoDef | ProgramRange(_, _) | ProgramFloat(_, _) => ()
  }
  let mutable_fields = mutable_fields.to_owned()
  let immutable_fields = immutable_fields.to_owned()
  for field in mutable_fields {
    require_mlw_context(anchor, field.id, span)
  }
  for field in immutable_fields {
    require_mlw_context(anchor, field.id, span)
  }
  {
    context,
    id: context.fresh_id(),
    logic_type,
    origin,
    flags,
    definition,
    mutable_fields,
    immutable_fields,
    invariants: [],
    regions: [],
  }
}

///|
pub fn ProgramTypeSymbol::new(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  flags : ProgramTypeFlags,
  definition : ProgramTypeDefinition,
  mutable_fields : ArrayView[PVariable],
  immutable_fields : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  make_program_type_symbol(
    context, logic_type, origin, flags, definition, mutable_fields, immutable_fields,
    span,
  )
}

///|
fn standard_program_type_flag(
  frozen : Bool,
  exposed : Bool,
  liable : Bool,
  fixed : Bool,
  visible : Bool,
) -> ProgramTypeArgumentFlag {
  { frozen, exposed, liable, fixed, visible }
}

///|
pub fn ProgramTypeSymbol::new_recursive(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  let flag = standard_program_type_flag(true, true, false, true, true)
  ProgramTypeSymbol::new(
    context,
    logic_type,
    origin,
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [
        for _ in logic_type.view().parameters => flag
      ],
      region_flags: [],
    },
    ProgramNoDef,
    [],
    [],
    span,
  )
}

///|
pub fn ProgramTypeSymbol::new_range(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  lower : BigInt,
  upper : BigInt,
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  guard logic_type.view().definition is Range(declared_lower, declared_upper) &&
    declared_lower == lower &&
    declared_upper == upper else {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "program range does not match its logical type definition",
    )
  }
  ProgramTypeSymbol::new(
    context,
    logic_type,
    origin,
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [],
      region_flags: [],
    },
    ProgramRange(lower, upper),
    [],
    [],
    span,
  )
}

///|
pub fn ProgramTypeSymbol::new_float(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  exponent_digits : Int,
  significand_digits : Int,
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  guard logic_type.view().definition
    is Float(declared_exponent_digits, declared_significand_digits) &&
    declared_exponent_digits == exponent_digits &&
    declared_significand_digits == significand_digits else {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "program float does not match its logical type definition",
    )
  }
  ProgramTypeSymbol::new(
    context,
    logic_type,
    origin,
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [],
      region_flags: [],
    },
    ProgramFloat(exponent_digits, significand_digits),
    [],
    [],
    span,
  )
}

///|
pub fn ProgramTypeSymbol::new_alias(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  target : Ity,
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  require_mlw_context(logic_type.semantic_id(), target.context_anchor(), span)
  let declared = logic_type.view().parameters
  for variable in target.free_type_variables() {
    if !declared.any(parameter => parameter == variable) {
      fail_mlw(
        UnboundProgramTypeVariable,
        span,
        "program alias contains an undeclared type variable",
      )
    }
  }
  let alias_body = match target.node {
    ItyRegion(region) =>
      { node: ItyApplication(region.symbol, region.arguments, region.regions) }
    _ => target
  }
  let regions = alias_body.top_regions()
  let flag = standard_program_type_flag(true, true, false, true, true)
  let symbol = ProgramTypeSymbol::new(
    context,
    logic_type,
    origin,
    {
      nonfree: false,
      private_: false,
      mutable_: target.view() is ItyReg(_),
      fragile: false,
      argument_flags: [
        for _ in declared => flag
      ],
      region_flags: [
        for _ in regions => flag
      ],
    },
    ProgramAlias(target),
    [],
    [],
    span,
  )
  symbol.regions = regions
  symbol
}

///|
pub fn ProgramTypeSymbol::new_variant(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  constructor_fields : ArrayView[Array[PVariable]],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  let fields : Array[PVariable] = []
  for constructor_entry in constructor_fields {
    for field in constructor_entry {
      if !fields.any(existing => existing == field) {
        fields.push(field)
      }
    }
  }
  ProgramTypeSymbol::new_record(
    context,
    logic_type,
    origin,
    false,
    false,
    [],
    fields,
    [],
    span,
  )
}

///|
fn append_unique_regions(
  result : Array[Region],
  regions : ArrayView[Region],
) -> Unit {
  for region in regions {
    add_unique_region(result, region)
  }
}

///|
fn append_unique_type_variables(
  result : Array[@logic.TyVarSymbol],
  variables : ArrayView[@logic.TyVarSymbol],
) -> Unit {
  for variable in variables {
    add_unique_type_variable(result, variable)
  }
}

///|
fn fields_top_regions(fields : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for field in fields {
    append_unique_regions(result, field.view().ity.top_regions())
  }
  result
}

///|
fn fields_exposed_regions(fields : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for field in fields {
    append_unique_regions(result, field.view().ity.exposed_regions())
  }
  result
}

///|
fn fields_reachable_regions(fields : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for field in fields {
    append_unique_regions(result, field.view().ity.reachable_regions())
  }
  result
}

///|
fn fields_frozen_regions(fields : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for field in fields {
    append_unique_regions(result, field.view().ity.frozen_regions())
  }
  result
}

///|
fn fields_visible_regions(fields : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for field in fields {
    append_unique_regions(result, field.view().ity.visible_regions())
  }
  result
}

///|
fn fields_reachable_type_variables(
  fields : ArrayView[PVariable],
) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  for field in fields {
    append_unique_type_variables(
      result,
      field.view().ity.reachable_type_variables(),
    )
  }
  result
}

///|
fn fields_exposed_type_variables(
  fields : ArrayView[PVariable],
) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  for field in fields {
    append_unique_type_variables(
      result,
      field.view().ity.exposed_type_variables(),
    )
  }
  result
}

///|
fn fields_frozen_type_variables(
  fields : ArrayView[PVariable],
) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  for field in fields {
    append_unique_type_variables(
      result,
      field.view().ity.frozen_type_variables(),
    )
  }
  result
}

///|
fn fields_visible_type_variables(
  fields : ArrayView[PVariable],
) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  for field in fields {
    append_unique_type_variables(
      result,
      field.view().ity.visible_type_variables(),
    )
  }
  result
}

///|
fn set_contains_type_variable(
  variables : ArrayView[@logic.TyVarSymbol],
  variable : @logic.TyVarSymbol,
) -> Bool {
  variables.any(candidate => candidate == variable)
}

///|
fn set_contains_region(regions : ArrayView[Region], region : Region) -> Bool {
  regions.any(candidate => candidate == region)
}

///|
pub fn ProgramTypeSymbol::new_record(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  private_ : Bool,
  force_mutable : Bool,
  mutable_fields : ArrayView[PVariable],
  immutable_fields : ArrayView[PVariable],
  invariants : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  let mutable_fields = mutable_fields.to_owned()
  let immutable_fields = immutable_fields.to_owned()
  let all_fields = mutable_fields + immutable_fields
  let declared = logic_type.view().parameters
  let field_symbols : Array[@logic.VSymbol] = []
  for field in all_fields {
    require_mlw_context(logic_type.semantic_id(), field.semantic_id(), span)
    if field_symbols.any(symbol => symbol == field.view().pure_symbol) {
      fail_mlw(
        InvalidProgramTypeInvariant,
        span,
        "record field is declared more than once",
      )
    }
    field_symbols.push(field.view().pure_symbol)
    for variable in field.view().ity.free_type_variables() {
      if !declared.any(parameter => parameter == variable) {
        fail_mlw(
          UnboundProgramTypeVariable,
          span,
          "record field contains an undeclared type variable",
        )
      }
    }
  }
  let liable_fields : Array[PVariable] = []
  for invariant in invariants {
    if !invariant.is_formula() {
      fail_mlw(
        InvalidProgramTypeInvariant,
        span,
        "type invariant is not a formula",
      )
    }
    for variable in invariant.free_variables() {
      if !field_symbols.any(field => field == variable) {
        fail_mlw(
          InvalidProgramTypeInvariant,
          span,
          "type invariant references a non-field variable",
        )
      }
      for field in all_fields {
        if field.view().pure_symbol == variable &&
          !liable_fields.any(existing => existing == field) {
          liable_fields.push(field)
        }
      }
    }
    for variable in invariant.free_type_variables() {
      if !declared.any(parameter => parameter == variable) {
        fail_mlw(
          UnboundProgramTypeVariable,
          span,
          "type invariant contains an undeclared type variable",
        )
      }
    }
  }
  let nonliable_fields : Array[PVariable] = []
  for field in all_fields {
    if !liable_fields.any(liable => liable == field) {
      nonliable_fields.push(field)
    }
  }
  let visible_fields = if private_ {
    all_fields
  } else {
    let visible : Array[PVariable] = []
    for field in all_fields {
      if !field.view().ghost {
        visible.push(field)
      }
    }
    visible
  }

  let regions = fields_top_regions(all_fields)
  let nonfree = private_ || !invariants.is_empty()
  let frozen_regions = if private_ {
    let result = fields_reachable_regions(liable_fields)
    append_unique_regions(result, fields_frozen_regions(nonliable_fields))
    result
  } else {
    fields_frozen_regions(all_fields)
  }
  let exposed_regions = fields_exposed_regions(all_fields)
  let liable_regions = fields_exposed_regions(liable_fields)
  let fixed_regions = fields_exposed_regions(immutable_fields)
  let visible_regions = fields_visible_regions(visible_fields)
  let mutable_ = force_mutable ||
    !mutable_fields.is_empty() ||
    (
      nonfree &&
      exposed_regions.any(region => !set_contains_region(frozen_regions, region))
    )
  let fragile = if private_ || (nonfree && !mutable_) {
    false
  } else if nonfree {
    liable_fields.any(field => {
      mutable_fields.any(mutable_field => mutable_field == field) ||
      field.view().ity.is_liquid_with_variables()
    }) ||
    nonliable_fields.any(field => {
      mutable_fields.any(mutable_field => mutable_field == field) &&
      field.view().ity.is_fragile_with_variables()
    })
  } else {
    all_fields.any(field => field.view().ity.is_fragile_with_variables())
  }

  let frozen_variables = if private_ {
    declared.to_owned()
  } else if nonfree && !mutable_ {
    fields_reachable_type_variables(all_fields)
  } else {
    fields_frozen_type_variables(all_fields)
  }
  let exposed_variables = if private_ {
    declared.to_owned()
  } else {
    fields_exposed_type_variables(all_fields)
  }
  let liable_variables = if private_ {
    declared.to_owned()
  } else {
    fields_exposed_type_variables(liable_fields)
  }
  let fixed_variables = if private_ {
    declared.to_owned()
  } else {
    fields_exposed_type_variables(immutable_fields)
  }
  let visible_variables = if private_ {
    declared.to_owned()
  } else {
    fields_visible_type_variables(visible_fields)
  }

  let argument_flags : Array[ProgramTypeArgumentFlag] = []
  for parameter in declared {
    argument_flags.push(
      standard_program_type_flag(
        set_contains_type_variable(frozen_variables, parameter),
        set_contains_type_variable(exposed_variables, parameter),
        set_contains_type_variable(liable_variables, parameter),
        set_contains_type_variable(fixed_variables, parameter),
        set_contains_type_variable(visible_variables, parameter),
      ),
    )
  }
  let region_flags : Array[ProgramTypeArgumentFlag] = []
  for region in regions {
    region_flags.push(
      standard_program_type_flag(
        set_contains_region(frozen_regions, region),
        set_contains_region(exposed_regions, region),
        set_contains_region(liable_regions, region),
        set_contains_region(fixed_regions, region),
        set_contains_region(visible_regions, region),
      ),
    )
  }
  let symbol = ProgramTypeSymbol::new(
    context,
    logic_type,
    origin,
    { nonfree, private_, mutable_, fragile, argument_flags, region_flags },
    ProgramNoDef,
    mutable_fields,
    immutable_fields,
    span,
  )
  symbol.invariants = invariants.to_owned()
  symbol.regions = regions
  symbol
}

///|
pub fn ProgramTypeSymbol::semantic_id(
  self : ProgramTypeSymbol,
) -> @identity.SemanticId {
  self.id
}

///|
pub fn ProgramTypeSymbol::view(
  self : ProgramTypeSymbol,
) -> ProgramTypeSymbolView {
  {
    id: self.id,
    logic_type: self.logic_type,
    origin: self.origin,
    flags: self.flags,
    definition: self.definition,
    mutable_fields: self.mutable_fields[:],
    immutable_fields: self.immutable_fields[:],
    invariants: self.invariants[:],
    regions: self.regions[:],
  }
}

///|
fn ProgramTypeSymbol::register_invariants(
  self : ProgramTypeSymbol,
  invariants : ArrayView[@logic.Term],
) -> Unit {
  if self.invariants.is_empty() {
    self.invariants = invariants.to_owned()
  } else if self.invariants != invariants.to_owned() {
    abort("program type symbol received inconsistent invariant metadata")
  }
}

///|
pub impl Eq for ProgramTypeSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for ProgramTypeSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
pub fn Ity::app(
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  Ity::app_with_regions(symbol, arguments, [], span)
}

///|
/// Constructs an immutable application with explicit shareable components.
/// Use `Ity::instantiate` when mutable symbols should allocate a fresh region.
pub fn Ity::app_with_regions(
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  regions : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  if arguments.length() != symbol.logic_type.arity() {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "program type application has the wrong arity",
    )
  }
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(symbol.id, argument.context_anchor(), span)
  }
  if regions.length() != symbol.flags.region_flags.length() {
    fail_mlw(
      BadRegionArity,
      span,
      "program type application has the wrong region arity",
    )
  }
  let regions = regions.to_owned()
  for region in regions {
    require_mlw_context(symbol.id, region.context_anchor(), span)
  }
  { node: ItyApplication(symbol, arguments, regions) }
}

///|
fn make_region(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  regions : ArrayView[Ity],
  inference : Bool,
  span : @identity.SourceSpan?,
) -> Region raise MlwError {
  if !context.contains(symbol.id) {
    fail_mlw(MlwContextMismatch, span, "region belongs to another context")
  }
  if !symbol.flags.mutable_ {
    fail_mlw(InvalidRegion, span, "region requires a mutable program type")
  }
  if arguments.length() != symbol.logic_type.arity() {
    fail_mlw(BadProgramTypeArity, span, "region has the wrong type arity")
  }
  if regions.length() != symbol.flags.region_flags.length() {
    fail_mlw(BadRegionArity, span, "region has the wrong region arity")
  }
  let arguments = arguments.to_owned()
  let regions = regions.to_owned()
  for argument in arguments {
    require_mlw_context(symbol.id, argument.context_anchor(), span)
  }
  for region in regions {
    require_mlw_context(symbol.id, region.context_anchor(), span)
  }
  { id: context.fresh_id(), name, symbol, arguments, regions, inference }
}

///|
pub fn Region::new(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  regions : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Region raise MlwError {
  make_region(context, name, symbol, arguments, regions, false, span)
}

///|
pub fn Ity::region(region : Region) -> Ity {
  { node: ItyRegion(region) }
}

///|
fn instantiate_template_ity(
  ity : Ity,
  parameters : ArrayView[@logic.TyVarSymbol],
  arguments : ArrayView[Ity],
  region_bindings : Map[Region, Ity],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      for index = 0; index < parameters.length(); index = index + 1 {
        if parameters[index] == variable {
          return arguments[index]
        }
      }
      fail_mlw(
        UnboundProgramTypeVariable,
        span,
        "program type template contains an undeclared type variable",
      )
    }
    ItyApplication(symbol, nested_arguments, nested_regions) =>
      {
        node: ItyApplication(
          symbol,
          nested_arguments.map(argument => {
            instantiate_template_ity(
              argument, parameters, arguments, region_bindings, span,
            )
          }),
          nested_regions.map(region => {
            instantiate_template_ity(
              region, parameters, arguments, region_bindings, span,
            )
          }),
        ),
      }
    ItyRegion(region) =>
      match region_bindings.get(region) {
        Some(instantiated) => instantiated
        None => {
          let instantiated_arguments = region.arguments.map(argument => {
            instantiate_template_ity(
              argument, parameters, arguments, region_bindings, span,
            )
          })
          let instantiated_regions = region.regions.map(nested => {
            instantiate_template_ity(
              nested, parameters, arguments, region_bindings, span,
            )
          })
          let instantiated = Ity::region(
            make_region(
              region.symbol.context,
              region.name,
              region.symbol,
              instantiated_arguments,
              instantiated_regions,
              region.inference,
              span,
            ),
          )
          region_bindings[region] = instantiated
          instantiated
        }
      }
  }
}

///|
fn Region::instantiate_member_ity(
  self : Region,
  template : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  let bindings : Map[Region, Ity] = Map([])
  let limit = if self.symbol.regions.length() < self.regions.length() {
    self.symbol.regions.length()
  } else {
    self.regions.length()
  }
  for index = 0; index < limit; index = index + 1 {
    bindings[self.symbol.regions[index]] = self.regions[index]
  }
  instantiate_template_ity(
    template,
    self.symbol.logic_type.view().parameters,
    self.arguments,
    bindings,
    span,
  )
}

///|
/// Instantiates a declared field type in this concrete region. This exposes
/// the same region graph used by assignment and effect validation without
/// allowing callers to manufacture region substitutions.
pub fn Region::member_ity(
  self : Region,
  field : PVariable,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  if !self.symbol.mutable_fields.any(candidate => candidate == field) &&
    !self.symbol.immutable_fields.any(candidate => candidate == field) {
    fail_mlw(
      InvalidRegion,
      span,
      "field does not belong to the region's program type",
    )
  }
  self.instantiate_member_ity(field.view().ity, span)
}

///|
pub fn Ity::member_ity(
  self : Ity,
  field : PVariable,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match self.node {
    ItyRegion(region) => region.member_ity(field, span)
    ItyApplication(symbol, arguments, regions) => {
      if !symbol.mutable_fields.any(candidate => candidate == field) &&
        !symbol.immutable_fields.any(candidate => candidate == field) {
        fail_mlw(
          InvalidRegion,
          span,
          "field does not belong to the program type",
        )
      }
      let bindings : Map[Region, Ity] = Map([])
      let limit = if symbol.regions.length() < regions.length() {
        symbol.regions.length()
      } else {
        regions.length()
      }
      for index = 0; index < limit; index = index + 1 {
        bindings[symbol.regions[index]] = regions[index]
      }
      instantiate_template_ity(
        field.view().ity,
        symbol.logic_type.view().parameters,
        arguments,
        bindings,
        span,
      )
    }
    ItyVariable(_) =>
      fail_mlw(
        InvalidRegion,
        span,
        "type-variable values have no program fields",
      )
  }
}

///|
/// Mirrors Why3's `ity_app`: mutable symbols allocate a fresh top region,
/// while immutable symbols remain ordinary applications.
pub fn Ity::instantiate(
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  regions : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  if arguments.length() != symbol.logic_type.arity() {
    fail_mlw(
      BadProgramTypeArity,
      span,
      "program type application has the wrong type arity",
    )
  }
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(symbol.id, argument.context_anchor(), span)
  }
  let region_bindings : Map[Region, Ity] = Map([])
  let actual_regions = if regions.is_empty() && !symbol.regions.is_empty() {
    [
      for region in symbol.regions => {
        instantiate_template_ity(
          Ity::region(region),
          symbol.logic_type.view().parameters,
          arguments,
          region_bindings,
          span,
        )
      }
    ]
  } else {
    if regions.length() != symbol.regions.length() {
      fail_mlw(
        BadRegionArity,
        span,
        "program type application has the wrong region arity",
      )
    }
    let actual = regions.to_owned()
    for index = 0; index < actual.length(); index = index + 1 {
      require_mlw_context(symbol.id, actual[index].context_anchor(), span)
      region_bindings[symbol.regions[index]] = actual[index]
    }
    actual
  }
  match symbol.definition {
    ProgramAlias(target) =>
      instantiate_template_ity(
        target,
        symbol.logic_type.view().parameters,
        arguments,
        region_bindings,
        span,
      )
    ProgramNoDef => {
      if !symbol.flags.mutable_ {
        return { node: ItyApplication(symbol, arguments, actual_regions) }
      }
      let region = Region::new(
        symbol.context,
        @theory.SemanticName::new(b"rho", [], None),
        symbol,
        arguments,
        actual_regions,
        span,
      )
      Ity::region(region)
    }
    ProgramRange(_, _) | ProgramFloat(_, _) => {
      if !arguments.is_empty() || !actual_regions.is_empty() {
        fail_mlw(
          BadProgramTypeArity,
          span,
          "numeric program type may not have arguments or regions",
        )
      }
      { node: ItyApplication(symbol, [], []) }
    }
  }
}

///|
/// Creates a named mutable region while allowing an omitted region argument
/// list to instantiate the symbol's shareable components freshly. This is the
/// region counterpart of `Ity::instantiate` and mirrors Why3's
/// `create_region` smart constructor.
pub fn Region::instantiate(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  regions : ArrayView[Ity],
  span : @identity.SourceSpan?,
  inference? : Bool = false,
) -> Region raise MlwError {
  let instantiated = Ity::instantiate(symbol, arguments, regions, span)
  guard instantiated.view() is ItyReg(region) else {
    fail_mlw(
      InvalidRegion,
      span,
      "region instantiation requires a mutable program type",
    )
  }
  let view = region.view()
  make_region(
    context,
    name,
    view.symbol,
    view.arguments,
    view.regions,
    inference,
    span,
  )
}

///|
/// Preserves a trusted polymorphic program type until a call site supplies a
/// monomorphic instantiation. User routines must reject this shape at their
/// declaration boundary.
pub fn Ity::variable(symbol : @logic.TyVarSymbol) -> Ity {
  { node: ItyVariable(symbol) }
}

///|
pub fn Ity::view(self : Ity) -> ItyView {
  match self.node {
    ItyVariable(symbol) => ItyVar(symbol)
    ItyApplication(symbol, arguments, regions) =>
      ItyApp(symbol, arguments[:], regions[:])
    ItyRegion(region) => ItyReg(region)
  }
}

///|
pub fn Ity::context_anchor(self : Ity) -> @identity.SemanticId {
  match self.node {
    ItyVariable(symbol) => symbol.semantic_id()
    ItyApplication(symbol, _, _) => symbol.id
    ItyRegion(region) => region.id
  }
}

///|
pub fn Ity::to_ty(
  self : Ity,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  match self.node {
    ItyVariable(symbol) => @logic.Ty::variable(symbol)
    ItyApplication(symbol, arguments, _) =>
      @logic.Ty::app(
        symbol.logic_type,
        [
          for argument in arguments => argument.to_ty(span)
        ],
        span,
      )
    ItyRegion(region) =>
      @logic.Ty::app(
        region.symbol.logic_type,
        [
          for argument in region.arguments => argument.to_ty(span)
        ],
        span,
      )
  }
}

///|
pub impl Eq for Ity with fn equal(self, other) {
  match (self.node, other.node) {
    (ItyVariable(left), ItyVariable(right)) => left == right
    (
      ItyApplication(left, left_args, left_regions),
      ItyApplication(right, right_args, right_regions),
    ) =>
      left == right && left_args == right_args && left_regions == right_regions
    (ItyRegion(left), ItyRegion(right)) => left == right
    _ => false
  }
}

///|
pub impl Hash for Ity with fn hash_combine(self, hasher) {
  match self.node {
    ItyVariable(symbol) => {
      hasher.combine(0)
      hasher.combine(symbol)
    }
    ItyApplication(symbol, arguments, regions) => {
      hasher.combine(1)
      hasher.combine(symbol)
      for argument in arguments {
        hasher.combine(argument)
      }
      for region in regions {
        hasher.combine(region)
      }
    }
    ItyRegion(region) => {
      hasher.combine(2)
      hasher.combine(region)
    }
  }
}

///|
pub fn Ity::is_closed(self : Ity) -> Bool {
  match self.node {
    ItyVariable(_) => false
    ItyApplication(_, arguments, _) => arguments.all(Ity::is_closed)
    ItyRegion(region) => region.arguments.all(Ity::is_closed)
  }
}

///|
/// Converts a core type through the exact program-type symbols already
/// present in the current Pmodule namespace. No symbol is reconstructed from
/// a spelling.
pub fn Ity::from_ty(
  program_space : ProgramNamespace,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Ity raise {
  match ty.view() {
    TyVar(variable) => Ity::variable(variable)
    TyApp(logic_symbol, arguments) => {
      let program_symbol = program_space.find_type_by_logic(logic_symbol, span)
      Ity::instantiate(
        program_symbol,
        [
          for argument in arguments => {
            Ity::from_ty(program_space, argument, span)
          }
        ],
        [],
        span,
      )
    }
  }
}

///|
pub fn Region::semantic_id(self : Region) -> @identity.SemanticId {
  self.id
}

///|
pub fn Region::view(self : Region) -> RegionView {
  {
    id: self.id,
    name: self.name,
    symbol: self.symbol,
    arguments: self.arguments[:],
    regions: self.regions[:],
    inference: self.inference,
  }
}

///|
pub impl Eq for Region with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for Region with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
fn add_unique_region(regions : Array[Region], region : Region) -> Unit {
  if !regions.any(existing => existing == region) {
    regions.push(region)
  }
}

///|
fn add_unique_type_variable(
  variables : Array[@logic.TyVarSymbol],
  variable : @logic.TyVarSymbol,
) -> Unit {
  if !variables.any(existing => existing == variable) {
    variables.push(variable)
  }
}

///|
pub fn Ity::is_pure(self : Ity) -> Bool {
  match self.node {
    ItyVariable(_) => true
    ItyApplication(_, arguments, regions) =>
      arguments.all(Ity::is_pure) && regions.all(Ity::is_pure)
    ItyRegion(_) => false
  }
}

///|
pub fn ProgramTypeSymbol::is_pure(self : ProgramTypeSymbol) -> Bool {
  !self.flags.mutable_ && self.flags.region_flags.is_empty()
}

///|
pub fn Ity::purify(self : Ity) -> Ity {
  match self.node {
    ItyVariable(_) => self
    ItyApplication(symbol, arguments, regions) =>
      {
        node: ItyApplication(
          symbol,
          arguments.map(Ity::purify),
          regions.map(Ity::purify),
        ),
      }
    ItyRegion(region) =>
      {
        node: ItyApplication(
          region.symbol,
          region.arguments.map(Ity::purify),
          region.regions.map(Ity::purify),
        ),
      }
  }
}

///|
fn Ity::collect_type_variables(
  self : Ity,
  result : Array[@logic.TyVarSymbol],
) -> Unit {
  match self.node {
    ItyVariable(variable) => add_unique_type_variable(result, variable)
    ItyApplication(_, arguments, _) =>
      for argument in arguments {
        argument.collect_type_variables(result)
      }
    ItyRegion(region) =>
      for argument in region.arguments {
        argument.collect_type_variables(result)
      }
  }
}

///|
pub fn Ity::free_type_variables(self : Ity) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  self.collect_type_variables(result)
  result
}

///|
fn Ity::collect_reachable_type_variables(
  self : Ity,
  result : Array[@logic.TyVarSymbol],
) -> Unit {
  match self.node {
    ItyVariable(variable) => add_unique_type_variable(result, variable)
    ItyApplication(symbol, arguments, regions) => {
      let argument_limit = if symbol.flags.argument_flags.length() <
        arguments.length() {
        symbol.flags.argument_flags.length()
      } else {
        arguments.length()
      }
      for index = 0; index < argument_limit; index = index + 1 {
        if symbol.flags.argument_flags[index].exposed {
          arguments[index].collect_reachable_type_variables(result)
        }
      }
      let region_limit = if symbol.flags.region_flags.length() <
        regions.length() {
        symbol.flags.region_flags.length()
      } else {
        regions.length()
      }
      for index = 0; index < region_limit; index = index + 1 {
        if symbol.flags.region_flags[index].exposed {
          regions[index].collect_reachable_type_variables(result)
        }
      }
    }
    ItyRegion(region) =>
      { node: ItyApplication(region.symbol, region.arguments, region.regions) }.collect_reachable_type_variables(
        result,
      )
  }
}

///|
pub fn Ity::reachable_type_variables(self : Ity) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  self.collect_reachable_type_variables(result)
  result
}

///|
fn Ity::collect_exposed_type_variables(
  self : Ity,
  result : Array[@logic.TyVarSymbol],
) -> Unit {
  match self.node {
    ItyVariable(variable) => add_unique_type_variable(result, variable)
    ItyApplication(symbol, arguments, regions) => {
      let argument_limit = if symbol.flags.argument_flags.length() <
        arguments.length() {
        symbol.flags.argument_flags.length()
      } else {
        arguments.length()
      }
      for index = 0; index < argument_limit; index = index + 1 {
        if symbol.flags.argument_flags[index].exposed {
          arguments[index].collect_exposed_type_variables(result)
        }
      }
      let region_limit = if symbol.flags.region_flags.length() <
        regions.length() {
        symbol.flags.region_flags.length()
      } else {
        regions.length()
      }
      for index = 0; index < region_limit; index = index + 1 {
        if symbol.flags.region_flags[index].exposed {
          regions[index].collect_exposed_type_variables(result)
        }
      }
    }
    ItyRegion(_) => ()
  }
}

///|
fn Ity::exposed_type_variables(self : Ity) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  self.collect_exposed_type_variables(result)
  result
}

///|
fn Ity::collect_frozen_type_variables(
  self : Ity,
  result : Array[@logic.TyVarSymbol],
) -> Unit {
  match self.node {
    ItyVariable(_) => ()
    ItyApplication(symbol, _, _) if symbol.flags.nonfree &&
      symbol.flags.mutable_ => self.collect_reachable_type_variables(result)
    ItyApplication(symbol, arguments, regions) => {
      let argument_limit = if symbol.flags.argument_flags.length() <
        arguments.length() {
        symbol.flags.argument_flags.length()
      } else {
        arguments.length()
      }
      for index = 0; index < argument_limit; index = index + 1 {
        let flag = symbol.flags.argument_flags[index]
        if flag.exposed {
          if flag.frozen {
            arguments[index].collect_reachable_type_variables(result)
          } else {
            arguments[index].collect_frozen_type_variables(result)
          }
        }
      }
      let region_limit = if symbol.flags.region_flags.length() <
        regions.length() {
        symbol.flags.region_flags.length()
      } else {
        regions.length()
      }
      for index = 0; index < region_limit; index = index + 1 {
        let flag = symbol.flags.region_flags[index]
        if flag.exposed {
          if flag.frozen {
            regions[index].collect_reachable_type_variables(result)
          } else {
            regions[index].collect_frozen_type_variables(result)
          }
        }
      }
    }
    ItyRegion(region) =>
      { node: ItyApplication(region.symbol, region.arguments, region.regions) }.collect_frozen_type_variables(
        result,
      )
  }
}

///|
fn Ity::frozen_type_variables(self : Ity) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  self.collect_frozen_type_variables(result)
  result
}

///|
fn Ity::collect_visible_type_variables(
  self : Ity,
  result : Array[@logic.TyVarSymbol],
) -> Unit {
  match self.node {
    ItyVariable(variable) => add_unique_type_variable(result, variable)
    ItyApplication(symbol, arguments, _) => {
      let limit = if symbol.flags.argument_flags.length() < arguments.length() {
        symbol.flags.argument_flags.length()
      } else {
        arguments.length()
      }
      for index = 0; index < limit; index = index + 1 {
        if symbol.flags.argument_flags[index].visible {
          arguments[index].collect_visible_type_variables(result)
        }
      }
    }
    ItyRegion(region) => {
      let limit = if region.symbol.flags.argument_flags.length() <
        region.arguments.length() {
        region.symbol.flags.argument_flags.length()
      } else {
        region.arguments.length()
      }
      for index = 0; index < limit; index = index + 1 {
        if region.symbol.flags.argument_flags[index].visible {
          region.arguments[index].collect_visible_type_variables(result)
        }
      }
    }
  }
}

///|
fn Ity::visible_type_variables(self : Ity) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  self.collect_visible_type_variables(result)
  result
}

///|
fn Ity::collect_top_regions(self : Ity, result : Array[Region]) -> Unit {
  if self.is_pure() {
    return
  }
  match self.node {
    ItyVariable(_) => ()
    ItyApplication(_, arguments, regions) => {
      for argument in arguments {
        argument.collect_top_regions(result)
      }
      for region in regions {
        region.collect_top_regions(result)
      }
    }
    ItyRegion(region) => add_unique_region(result, region)
  }
}

///|
pub fn Ity::top_regions(self : Ity) -> Array[Region] {
  let result : Array[Region] = []
  self.collect_top_regions(result)
  result
}

///|
fn collect_flagged_regions(
  flags : ArrayView[ProgramTypeArgumentFlag],
  components : ArrayView[Ity],
  exposed_only : Bool,
  visible_only : Bool,
  result : Array[Region],
) -> Unit {
  let limit = if flags.length() < components.length() {
    flags.length()
  } else {
    components.length()
  }
  for index = 0; index < limit; index = index + 1 {
    let flag = flags[index]
    if (!exposed_only || flag.exposed) && (!visible_only || flag.visible) {
      if visible_only {
        components[index].collect_visible_regions(result)
      } else {
        components[index].collect_exposed_regions(result)
      }
    }
  }
}

///|
fn Ity::collect_exposed_regions(self : Ity, result : Array[Region]) -> Unit {
  if self.is_pure() {
    return
  }
  match self.node {
    ItyVariable(_) => ()
    ItyApplication(symbol, arguments, regions) => {
      collect_flagged_regions(
        symbol.flags.argument_flags,
        arguments,
        true,
        false,
        result,
      )
      collect_flagged_regions(
        symbol.flags.region_flags,
        regions,
        true,
        false,
        result,
      )
    }
    ItyRegion(region) => add_unique_region(result, region)
  }
}

///|
fn Region::collect_reachable_regions(
  self : Region,
  result : Array[Region],
) -> Unit {
  if result.any(existing => existing == self) {
    return
  }
  result.push(self)
  let exposed : Array[Region] = []
  collect_flagged_regions(
    self.symbol.flags.argument_flags,
    self.arguments,
    true,
    false,
    exposed,
  )
  collect_flagged_regions(
    self.symbol.flags.region_flags,
    self.regions,
    true,
    false,
    exposed,
  )
  for region in exposed {
    region.collect_reachable_regions(result)
  }
}

///|
pub fn Ity::exposed_regions(self : Ity) -> Array[Region] {
  let result : Array[Region] = []
  self.collect_exposed_regions(result)
  result
}

///|
pub fn Ity::reachable_regions(self : Ity) -> Array[Region] {
  let result : Array[Region] = []
  let exposed = self.exposed_regions()
  for region in exposed {
    region.collect_reachable_regions(result)
  }
  result
}

///|
pub fn Region::reachable_regions(self : Region) -> Array[Region] {
  let result : Array[Region] = []
  self.collect_reachable_regions(result)
  result
}

///|
fn Ity::collect_visible_regions(self : Ity, result : Array[Region]) -> Unit {
  if self.is_pure() {
    return
  }
  match self.node {
    ItyVariable(_) => ()
    ItyApplication(symbol, arguments, regions) => {
      collect_flagged_regions(
        symbol.flags.argument_flags,
        arguments,
        false,
        true,
        result,
      )
      collect_flagged_regions(
        symbol.flags.region_flags,
        regions,
        false,
        true,
        result,
      )
    }
    ItyRegion(region) => {
      add_unique_region(result, region)
      collect_flagged_regions(
        region.symbol.flags.argument_flags,
        region.arguments,
        false,
        true,
        result,
      )
      collect_flagged_regions(
        region.symbol.flags.region_flags,
        region.regions,
        false,
        true,
        result,
      )
    }
  }
}

///|
pub fn Ity::visible_regions(self : Ity) -> Array[Region] {
  let result : Array[Region] = []
  self.collect_visible_regions(result)
  result
}

///|
fn collect_frozen_component(
  flag : ProgramTypeArgumentFlag,
  component : Ity,
  result : Array[Region],
) -> Unit {
  if !flag.exposed {
    return
  }
  if flag.frozen {
    for region in component.reachable_regions() {
      add_unique_region(result, region)
    }
  } else {
    component.collect_frozen_regions(result)
  }
}

///|
fn Ity::collect_frozen_regions(self : Ity, result : Array[Region]) -> Unit {
  if self.is_pure() {
    return
  }
  match self.node {
    ItyVariable(_) => ()
    ItyApplication(symbol, _, _) if symbol.flags.nonfree &&
      symbol.flags.mutable_ =>
      for region in self.reachable_regions() {
        add_unique_region(result, region)
      }
    ItyApplication(symbol, arguments, regions) => {
      let argument_limit = if symbol.flags.argument_flags.length() <
        arguments.length() {
        symbol.flags.argument_flags.length()
      } else {
        arguments.length()
      }
      for index = 0; index < argument_limit; index = index + 1 {
        collect_frozen_component(
          symbol.flags.argument_flags[index],
          arguments[index],
          result,
        )
      }
      let region_limit = if symbol.flags.region_flags.length() <
        regions.length() {
        symbol.flags.region_flags.length()
      } else {
        regions.length()
      }
      for index = 0; index < region_limit; index = index + 1 {
        collect_frozen_component(
          symbol.flags.region_flags[index],
          regions[index],
          result,
        )
      }
    }
    ItyRegion(region) => {
      let argument_limit = if region.symbol.flags.argument_flags.length() <
        region.arguments.length() {
        region.symbol.flags.argument_flags.length()
      } else {
        region.arguments.length()
      }
      for index = 0; index < argument_limit; index = index + 1 {
        collect_frozen_component(
          region.symbol.flags.argument_flags[index],
          region.arguments[index],
          result,
        )
      }
      let region_limit = if region.symbol.flags.region_flags.length() <
        region.regions.length() {
        region.symbol.flags.region_flags.length()
      } else {
        region.regions.length()
      }
      for index = 0; index < region_limit; index = index + 1 {
        collect_frozen_component(
          region.symbol.flags.region_flags[index],
          region.regions[index],
          result,
        )
      }
    }
  }
}

///|
pub fn Ity::frozen_regions(self : Ity) -> Array[Region] {
  let result : Array[Region] = []
  self.collect_frozen_regions(result)
  result
}

///|
fn Region::is_stale_under(
  self : Region,
  resets : ArrayView[Region],
  covers : ArrayView[Region],
  visited : Array[Region],
) -> Bool {
  if covers.any(region => region == self) ||
    visited.any(region => region == self) {
    return false
  }
  if resets.any(region => region == self) {
    return true
  }
  visited.push(self)
  let exposed : Array[Region] = []
  collect_flagged_regions(
    self.symbol.flags.argument_flags,
    self.arguments,
    true,
    false,
    exposed,
  )
  collect_flagged_regions(
    self.symbol.flags.region_flags,
    self.regions,
    true,
    false,
    exposed,
  )
  exposed.any(region => region.is_stale_under(resets, covers, visited))
}

///|
pub fn Ity::has_stale_region(
  self : Ity,
  resets : ArrayView[Region],
  covers : ArrayView[Region],
) -> Bool {
  let visited : Array[Region] = []
  self
  .exposed_regions()
  .any(region => region.is_stale_under(resets, covers, visited))
}

///|
fn Ity::fragile_with(
  self : Ity,
  liquid_variables : Bool,
  liable : Bool,
) -> Bool {
  fn fragile(ity : Ity, liquid_variables : Bool, liable : Bool) -> Bool {
    match ity.node {
      ItyVariable(_) => liable && liquid_variables
      ItyApplication(symbol, arguments, regions) => {
        if symbol.flags.fragile || (liable && symbol.flags.mutable_) {
          return true
        }
        if symbol.flags.nonfree && !symbol.flags.mutable_ {
          return false
        }
        let components = arguments.copy()
        for region in regions {
          components.push(region)
        }
        let flags = symbol.flags.argument_flags.copy()
        for flag in symbol.flags.region_flags {
          flags.push(flag)
        }
        let limit = if components.length() < flags.length() {
          components.length()
        } else {
          flags.length()
        }
        for index = 0; index < limit; index = index + 1 {
          let flag = flags[index]
          if flag.exposed &&
            !flag.frozen &&
            fragile(components[index], liquid_variables, liable || flag.liable) {
            return true
          }
        }
        false
      }
      ItyRegion(region) =>
        fragile(
          {
            node: ItyApplication(
              region.symbol,
              region.arguments,
              region.regions,
            ),
          },
          liquid_variables,
          liable,
        )
    }
  }

  fragile(self, liquid_variables, liable)
}

///|
fn Ity::is_liquid_with_variables(self : Ity) -> Bool {
  self.fragile_with(true, true)
}

///|
fn Ity::is_fragile_with_variables(self : Ity) -> Bool {
  self.fragile_with(true, false)
}

///|
pub fn Ity::is_fragile(self : Ity) -> Bool {
  self.fragile_with(false, false)
}

///|
pub(all) struct ItySubstitutionView {
  type_variables : ArrayView[(@logic.TyVarSymbol, Ity)]
  regions : ArrayView[(Region, Ity)]
}

///|
struct ItySubstitution {
  type_variables : Array[(@logic.TyVarSymbol, Ity)]
  regions : Array[(Region, Ity)]
  frozen_type_variables : Array[@logic.TyVarSymbol]
  frozen_regions : Array[Region]
  inference_regions : Array[Region]
}

///|
pub fn ItySubstitution::empty() -> ItySubstitution {
  {
    type_variables: [],
    regions: [],
    frozen_type_variables: [],
    frozen_regions: [],
    inference_regions: [],
  }
}

///|
pub fn ItySubstitution::view(self : ItySubstitution) -> ItySubstitutionView {
  { type_variables: self.type_variables[:], regions: self.regions[:] }
}

///|
fn is_program_inference_type_variable(variable : @logic.TyVarSymbol) -> Bool {
  variable
  .origin()
  .attributes()
  .any(attribute => attribute == b"mlw:inference_type_variable")
}

///|
fn is_program_inference_region(region : Region) -> Bool {
  region.inference ||
  region.name.view().attributes.any(attribute => {
    attribute == b"mlw:inference_region"
  })
}

///|
fn ItySubstitution::bind_type_variable(
  self : ItySubstitution,
  variable : @logic.TyVarSymbol,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  for entry in self.type_variables {
    if entry.0 == variable {
      if entry.1 == ity {
        return self
      }
      if self.frozen_type_variables.any(frozen => frozen == variable) {
        fail_mlw(
          ProgramTypeMismatch,
          span,
          "incompatible type substitution for '\{variable.name()}#\{variable.semantic_id().local_id()}: \{entry.1.diagnostic_shape()} vs \{ity.diagnostic_shape()}",
        )
      }
      let previous = self.resolve_inference_variables(entry.1, span)
      let actual = self.resolve_inference_variables(ity, span)
      if previous == actual {
        return self
      }
      if previous.free_type_variables().any(is_program_inference_type_variable) ||
        actual.free_type_variables().any(is_program_inference_type_variable) ||
        previous
        .reachable_regions()
        .any(region => {
          is_program_inference_region(region) ||
          self.inference_regions.any(candidate => candidate == region)
        }) ||
        actual
        .reachable_regions()
        .any(region => {
          is_program_inference_region(region) ||
          self.inference_regions.any(candidate => candidate == region)
        }) {
        return self.match_inference_ity(previous, actual, span)
      }
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "incompatible type substitution for '\{variable.name()}#\{variable.semantic_id().local_id()}: \{entry.1.diagnostic_shape()} vs \{ity.diagnostic_shape()}",
      )
    }
  }
  { ..self, type_variables: self.type_variables + [(variable, ity)] }
}

///|
fn ItySubstitution::match_inference_ity(
  self : ItySubstitution,
  left : Ity,
  right : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  let left = self.resolve_inference_variables(left, span)
  let right = self.resolve_inference_variables(right, span)
  if left == right {
    return self
  }
  match (left.node, right.node) {
    (ItyVariable(variable), _) if is_program_inference_type_variable(variable) =>
      self.bind_type_variable(variable, right, span)
    (_, ItyVariable(variable)) if is_program_inference_type_variable(variable) =>
      self.bind_type_variable(variable, left, span)
    (ItyRegion(region), _) if is_program_inference_region(region) ||
      self.inference_regions.any(candidate => candidate == region) => {
      let substitution = self.bind_region(region, right, span)
      substitution.match_inference_region(left, right, span)
    }
    (_, ItyRegion(region)) if is_program_inference_region(region) ||
      self.inference_regions.any(candidate => candidate == region) => {
      let substitution = self.bind_region(region, left, span)
      substitution.match_inference_region(left, right, span)
    }
    (
      ItyApplication(left_symbol, left_arguments, left_regions),
      ItyApplication(right_symbol, right_arguments, right_regions),
    ) if left_symbol == right_symbol &&
      left_arguments.length() == right_arguments.length() &&
      left_regions.length() == right_regions.length() => {
      let mut substitution = self
      for index = 0; index < left_arguments.length(); index = index + 1 {
        substitution = substitution.match_inference_ity(
          left_arguments[index],
          right_arguments[index],
          span,
        )
      }
      for index = 0; index < left_regions.length(); index = index + 1 {
        substitution = substitution.match_inference_ity(
          left_regions[index],
          right_regions[index],
          span,
        )
      }
      substitution
    }
    _ =>
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "incompatible inferred program types: \{left.diagnostic_shape()} vs \{right.diagnostic_shape()}",
      )
  }
}

///|
fn ItySubstitution::bind_region(
  self : ItySubstitution,
  region : Region,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  for entry in self.regions {
    if entry.0 == region {
      if entry.1 != ity {
        let previous_is_inference = entry.1.node is ItyRegion(previous) &&
          (
            is_program_inference_region(previous) ||
            self.inference_regions.any(candidate => candidate == previous)
          )
        let actual_is_inference = ity.node is ItyRegion(actual) &&
          (
            is_program_inference_region(actual) ||
            self.inference_regions.any(candidate => candidate == actual)
          )
        if previous_is_inference || actual_is_inference {
          let substitution = self.match_inference_region(entry.1, ity, span)
          if previous_is_inference {
            let regions = substitution.regions.copy()
            guard entry.1.node is ItyRegion(previous_region) else {
              abort("inference-region classification lost its region")
            }
            for index, binding in regions {
              if binding.0 == region {
                regions[index] = (region, ity)
                let mut redirected = false
                for redirect_index, redirect in regions {
                  if redirect.0 == previous_region {
                    regions[redirect_index] = (previous_region, ity)
                    redirected = true
                    break
                  }
                }
                if !redirected {
                  regions.push((previous_region, ity))
                }
                return { ..substitution, regions, }
              }
            }
          }
          return substitution
        }
        fail_mlw(
          ProgramTypeMismatch,
          span,
          "incompatible region substitution for rho#\{region.semantic_id().local_id()}: \{entry.1.diagnostic_shape()} vs \{ity.diagnostic_shape()}",
        )
      }
      return self
    }
  }
  { ..self, regions: self.regions + [(region, ity)] }
}

///|
fn ItySubstitution::match_inference_region(
  self : ItySubstitution,
  left : Ity,
  right : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  let (left_symbol, left_arguments, left_regions) = match left.node {
    ItyRegion(region) => (region.symbol, region.arguments[:], region.regions[:])
    ItyApplication(symbol, arguments, regions) =>
      (symbol, arguments[:], regions[:])
    ItyVariable(_) =>
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "inferred region cannot match a type variable",
      )
  }
  let (right_symbol, right_arguments, right_regions) = match right.node {
    ItyRegion(region) => (region.symbol, region.arguments[:], region.regions[:])
    ItyApplication(symbol, arguments, regions) =>
      (symbol, arguments[:], regions[:])
    ItyVariable(_) =>
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "inferred region cannot match a type variable",
      )
  }
  if left_symbol != right_symbol ||
    left_arguments.length() != right_arguments.length() ||
    left_regions.length() != right_regions.length() {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "inferred region skeletons do not match",
    )
  }
  let mut substitution = self
  for index, argument in left_arguments {
    substitution = substitution.match_inference_ity(
      argument,
      right_arguments[index],
      span,
    )
  }
  for index, nested in left_regions {
    if nested == right_regions[index] {
      continue
    }
    let left_inference = nested.node is ItyRegion(region) &&
      (
        is_program_inference_region(region) ||
        substitution.inference_regions.any(candidate => candidate == region)
      )
    let right_inference = right_regions[index].node is ItyRegion(region) &&
      (
        is_program_inference_region(region) ||
        substitution.inference_regions.any(candidate => candidate == region)
      )
    if !left_inference && !right_inference {
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "nested inferred regions do not match",
      )
    }
    substitution = substitution.match_inference_region(
      nested,
      right_regions[index],
      span,
    )
  }
  substitution
}

///|
pub fn ItySubstitution::match_ity(
  self : ItySubstitution,
  pattern : Ity,
  actual : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  match (pattern.node, actual.node) {
    (ItyVariable(variable), _) =>
      self.bind_type_variable(variable, actual, span)
    (_, ItyVariable(variable)) =>
      if is_program_inference_type_variable(variable) {
        self.bind_type_variable(variable, pattern, span)
      } else {
        fail_mlw(
          ProgramTypeMismatch,
          span,
          "program type does not match rigid variable '\{variable.name()}#\{variable.semantic_id().local_id()}",
        )
      }
    (ItyRegion(region), _) => self.match_region(region, actual, span)
    (
      ItyApplication(left, left_arguments, left_regions),
      ItyApplication(right, right_arguments, right_regions),
    ) if left == right &&
      left_arguments.length() == right_arguments.length() &&
      left_regions.length() == right_regions.length() => {
      let mut substitution = self
      for index = 0; index < left_arguments.length(); index = index + 1 {
        substitution = substitution.match_ity(
          left_arguments[index],
          right_arguments[index],
          span,
        )
      }
      for index = 0; index < left_regions.length(); index = index + 1 {
        substitution = substitution.match_ity(
          left_regions[index],
          right_regions[index],
          span,
        )
      }
      substitution
    }
    _ =>
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "program types do not match (\{pattern.diagnostic_head()} vs \{actual.diagnostic_head()})",
      )
  }
}

///|
fn Ity::diagnostic_head(self : Ity) -> String {
  match self.node {
    ItyVariable(_) => "type variable"
    ItyApplication(symbol, _, _) => "application \{symbol.logic_type.name()}"
    ItyRegion(region) =>
      "region \{region.symbol.logic_type.name()}#\{region.id.local_id()}"
  }
}

///|
fn Ity::diagnostic_shape(self : Ity) -> String {
  match self.node {
    ItyVariable(variable) =>
      "'\{variable.name()}#\{variable.semantic_id().local_id()}"
    ItyApplication(symbol, arguments, regions) => {
      let components = arguments.map(argument => argument.diagnostic_shape())
      components.push_iter(
        regions.map(region => region.diagnostic_shape()).iter(),
      )
      if components.is_empty() {
        "\{symbol.logic_type.name()}"
      } else {
        "\{symbol.logic_type.name()}<\{components.join(",")}>"
      }
    }
    ItyRegion(region) => {
      let expanded : Ity = {
        node: ItyApplication(region.symbol, region.arguments, region.regions),
      }
      "rho#\{region.id.local_id()}:\{expanded.diagnostic_shape()}"
    }
  }
}

///|
pub fn Ity::same_skeleton(
  self : Ity,
  other : Ity,
  span : @identity.SourceSpan?,
) -> Bool raise MlwError {
  try {
    ignore(ItySubstitution::empty().match_ity(self, other, span))
    true
  } catch {
    MlwError(diagnostic) =>
      if diagnostic.kind == ProgramTypeMismatch {
        false
      } else {
        raise MlwError(diagnostic)
      }
  }
}

///|
pub fn ItySubstitution::match_region(
  self : ItySubstitution,
  pattern : Region,
  actual : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  if actual.node is ItyVariable(variable) &&
    is_program_inference_type_variable(variable) {
    return self.bind_type_variable(variable, Ity::region(pattern), span)
  }
  let mut substitution = self.bind_region(pattern, actual, span)
  let (target_symbol, target_arguments, target_regions) = match actual.node {
    ItyRegion(target) => (target.symbol, target.arguments, target.regions)
    ItyApplication(symbol, arguments, regions) => (symbol, arguments, regions)
    ItyVariable(_) =>
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "region skeleton does not match (\{Ity::region(pattern).diagnostic_head()} vs \{actual.diagnostic_head()})",
      )
  }
  if pattern.symbol != target_symbol ||
    pattern.arguments.length() != target_arguments.length() ||
    pattern.regions.length() != target_regions.length() {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "region skeleton does not match (\{Ity::region(pattern).diagnostic_head()} vs \{actual.diagnostic_head()})",
    )
  }
  for index = 0; index < pattern.arguments.length(); index = index + 1 {
    substitution = substitution.match_ity(
      pattern.arguments[index],
      target_arguments[index],
      span,
    )
  }
  for index = 0; index < pattern.regions.length(); index = index + 1 {
    substitution = substitution.match_ity(
      pattern.regions[index],
      target_regions[index],
      span,
    )
  }
  substitution
}

///|
pub fn ItySubstitution::instantiate(
  self : ItySubstitution,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      for entry in self.type_variables {
        if entry.0 == variable {
          return self.resolve_inference_variables(entry.1, span)
        }
      }
      fail_mlw(
        UnboundProgramTypeVariable,
        span,
        "type substitution is incomplete",
      )
    }
    ItyRegion(region) => {
      for entry in self.regions {
        if entry.0 == region {
          return self.resolve_inference_variables(entry.1, span)
        }
      }
      fail_mlw(UnboundRegion, span, "region substitution is incomplete")
    }
    ItyApplication(symbol, arguments, regions) =>
      {
        node: ItyApplication(
          symbol,
          arguments.map(argument => self.instantiate(argument, span)),
          regions.map(region => self.instantiate(region, span)),
        ),
      }
  }
}

///|
fn ItySubstitution::resolve_inference_variables_cached(
  self : ItySubstitution,
  ity : Ity,
  region_cache : Array[(Region, Ity)],
  active_types : ArrayView[@logic.TyVarSymbol],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      if !is_program_inference_type_variable(variable) ||
        active_types.any(active => active == variable) {
        return ity
      }
      for entry in self.type_variables {
        if entry.0 == variable {
          return self.resolve_inference_variables_cached(
            entry.1,
            region_cache,
            active_types.to_owned() + [variable],
            span,
          )
        }
      }
      ity
    }
    ItyApplication(symbol, arguments, regions) =>
      {
        node: ItyApplication(
          symbol,
          arguments.map(argument => {
            self.resolve_inference_variables_cached(
              argument, region_cache, active_types, span,
            )
          }),
          regions.map(region => {
            self.resolve_inference_variables_cached(
              region, region_cache, active_types, span,
            )
          }),
        ),
      }
    ItyRegion(region) => {
      for entry in region_cache {
        if entry.0 == region {
          return entry.1
        }
      }
      if is_program_inference_region(region) {
        for entry in self.regions {
          if entry.0 == region && entry.1 != ity {
            let resolved = self.resolve_inference_variables_cached(
              entry.1,
              region_cache,
              active_types,
              span,
            )
            region_cache.push((region, resolved))
            return resolved
          }
        }
      }
      let arguments = region.arguments.map(argument => {
        self.resolve_inference_variables_cached(
          argument, region_cache, active_types, span,
        )
      })
      let regions = region.regions.map(nested => {
        self.resolve_inference_variables_cached(
          nested, region_cache, active_types, span,
        )
      })
      let mut unchanged = true
      for index, argument in arguments {
        unchanged = unchanged && argument == region.arguments[index]
      }
      for index, nested in regions {
        unchanged = unchanged && nested == region.regions[index]
      }
      let resolved = if unchanged {
        ity
      } else {
        Ity::region(
          make_region(
            region.symbol.context,
            region.name,
            region.symbol,
            arguments,
            regions,
            region.inference,
            span,
          ),
        )
      }
      region_cache.push((region, resolved))
      resolved
    }
  }
}

///|
fn ItySubstitution::resolve_inference_variables(
  self : ItySubstitution,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  self.resolve_inference_variables_cached(ity, [], [], span)
}

///|
fn ItySubstitution::instantiate_partial_cached(
  self : ItySubstitution,
  ity : Ity,
  region_cache : Array[(Region, Ity)],
  type_cache : Array[(@logic.TyVarSymbol, Ity)],
  active_regions : ArrayView[Region],
  active_types : ArrayView[@logic.TyVarSymbol],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      for entry in type_cache {
        if entry.0 == variable {
          return entry.1
        }
      }
      for entry in self.type_variables {
        if entry.0 == variable {
          let resolved = self.resolve_inference_variables(entry.1, span)
          type_cache.push((variable, resolved))
          return resolved
        }
      }
      ity
    }
    ItyApplication(symbol, arguments, regions) =>
      Ity::app_with_regions(
        symbol,
        arguments.map(argument => {
          self.instantiate_partial_cached(
            argument, region_cache, type_cache, active_regions, active_types, span,
          )
        }),
        regions.map(region => {
          self.instantiate_partial_cached(
            region, region_cache, type_cache, active_regions, active_types, span,
          )
        }),
        span,
      )
    ItyRegion(region) => {
      for entry in region_cache {
        if entry.0 == region {
          return entry.1
        }
      }
      let source = Ity::region(region)
      for entry in self.regions {
        if entry.0 == region {
          let resolved = self.resolve_inference_variables(entry.1, span)
          region_cache.push((region, resolved))
          return resolved
        }
      }
      let arguments = region.arguments.map(argument => {
        self.instantiate_partial_cached(
          argument, region_cache, type_cache, active_regions, active_types, span,
        )
      })
      let regions = region.regions.map(nested => {
        self.instantiate_partial_cached(
          nested, region_cache, type_cache, active_regions, active_types, span,
        )
      })
      let mut unchanged = arguments.length() == region.arguments.length() &&
        regions.length() == region.regions.length()
      for index, argument in arguments {
        unchanged = unchanged && argument == region.arguments[index]
      }
      for index, nested in regions {
        unchanged = unchanged && nested == region.regions[index]
      }
      let resolved = if unchanged {
        source
      } else {
        Ity::region(
          make_region(
            region.symbol.context,
            region.name,
            region.symbol,
            arguments,
            regions,
            region.inference,
            span,
          ),
        )
      }
      region_cache.push((region, resolved))
      resolved
    }
  }
}

///|
/// Applies the bindings currently known to the substitution while retaining
/// unmatched variables and regions. Rewriting a batch shares its region cache,
/// so aliases already present in the source types remain aliases afterward.
pub fn ItySubstitution::instantiate_partial(
  self : ItySubstitution,
  ities : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Array[Ity] raise MlwError {
  let region_cache : Array[(Region, Ity)] = []
  let type_cache : Array[(@logic.TyVarSymbol, Ity)] = []
  ities.map(ity => {
    self.instantiate_partial_cached(ity, region_cache, type_cache, [], [], span)
  })
}

///|
fn ItySubstitution::instantiate_call_result_with_fresh_regions(
  self : ItySubstitution,
  context : @identity.CompilationContext,
  ity : Ity,
  span : @identity.SourceSpan?,
  generalize : Bool,
) -> (ItySubstitution, Ity) raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      for entry in self.type_variables {
        if entry.0 == variable {
          return (self, self.resolve_inference_variables(entry.1, span))
        }
      }
      if generalize {
        let origin = @identity.Origin::user(b"xi", span, [
          b"mlw:inference_type_variable",
        ])
        let generalized = Ity::variable(
          @logic.TyVarSymbol::new(context, b"xi", origin),
        )
        return (
          self.bind_type_variable(variable, generalized, span),
          generalized,
        )
      }
      fail_mlw(
        UnboundProgramTypeVariable,
        span,
        "call result leaves an unresolved program type variable",
      )
    }
    ItyApplication(symbol, arguments, regions) => {
      let mut substitution = self
      let instantiated_arguments : Array[Ity] = []
      for argument in arguments {
        let (next, instantiated) = substitution.instantiate_call_result_with_fresh_regions(
          context, argument, span, generalize,
        )
        substitution = next
        instantiated_arguments.push(instantiated)
      }
      let instantiated_regions : Array[Ity] = []
      for region in regions {
        let (next, instantiated) = substitution.instantiate_call_result_with_fresh_regions(
          context, region, span, generalize,
        )
        substitution = next
        instantiated_regions.push(instantiated)
      }
      (
        substitution,
        {
          node: ItyApplication(
            symbol, instantiated_arguments, instantiated_regions,
          ),
        },
      )
    }
    ItyRegion(region) => {
      for entry in self.regions {
        if entry.0 == region {
          return (self, self.resolve_inference_variables(entry.1, span))
        }
      }
      let mut substitution = self
      let instantiated_arguments : Array[Ity] = []
      for argument in region.arguments {
        let (next, instantiated) = substitution.instantiate_call_result_with_fresh_regions(
          context, argument, span, generalize,
        )
        substitution = next
        instantiated_arguments.push(instantiated)
      }
      let instantiated_regions : Array[Ity] = []
      for nested in region.regions {
        let (next, instantiated) = substitution.instantiate_call_result_with_fresh_regions(
          context, nested, span, generalize,
        )
        substitution = next
        instantiated_regions.push(instantiated)
      }
      let fresh_region = make_region(
        context,
        region.name,
        region.symbol,
        instantiated_arguments,
        instantiated_regions,
        generalize,
        span,
      )
      let fresh = Ity::region(fresh_region)
      substitution = substitution.bind_region(region, fresh, span)
      if generalize &&
        !substitution.inference_regions.any(candidate => {
          candidate == fresh_region
        }) {
        substitution = {
          ..substitution,
          inference_regions: substitution.inference_regions + [fresh_region],
        }
      }
      (substitution, fresh)
    }
  }
}

///|
/// Instantiates a fully applied call result while allocating fresh identities
/// for result regions that are not fixed by arguments or an expected type.
/// Type variables still have to be determined by the call signature.
pub fn ItySubstitution::instantiate_call_result(
  self : ItySubstitution,
  context : @identity.CompilationContext,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  self.instantiate_call_result_with_fresh_regions(context, ity, span, false).1
}

///|
/// Instantiates a call result while generalizing type variables that occur
/// only covariantly in that result. This is the delayed-typing behavior used
/// when an enclosing routine is itself being inferred.
pub fn ItySubstitution::instantiate_generalized_call_result(
  self : ItySubstitution,
  context : @identity.CompilationContext,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  self.instantiate_call_result_with_fresh_regions(context, ity, span, true).1
}

///|
/// Produces an expected type for a still-underconstrained call argument and
/// returns the inference bindings that were introduced for it. Unlike final
/// result instantiation, callers retain the updated substitution so later
/// arguments can specialize the same temporary variables.
pub fn ItySubstitution::instantiate_inference_expected(
  self : ItySubstitution,
  context : @identity.CompilationContext,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> (ItySubstitution, Ity) raise MlwError {
  self.instantiate_call_result_with_fresh_regions(context, ity, span, true)
}

///|
pub fn ItySubstitution::freeze(
  self : ItySubstitution,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> ItySubstitution raise MlwError {
  match ity.node {
    ItyVariable(variable) => {
      let mut substitution = self.bind_type_variable(variable, ity, span)
      if !substitution.frozen_type_variables.any(frozen => frozen == variable) {
        substitution = {
          ..substitution,
          frozen_type_variables: substitution.frozen_type_variables + [variable],
        }
      }
      substitution
    }
    ItyApplication(_, arguments, regions) => {
      let mut substitution = self
      for argument in arguments {
        substitution = substitution.freeze(argument, span)
      }
      for region in regions {
        substitution = substitution.freeze(region, span)
      }
      substitution
    }
    ItyRegion(region) => {
      let mut substitution = self.bind_region(region, ity, span)
      if !substitution.frozen_regions.any(frozen => frozen == region) {
        substitution = {
          ..substitution,
          frozen_regions: substitution.frozen_regions + [region],
        }
      }
      for argument in region.arguments {
        substitution = substitution.freeze(argument, span)
      }
      for nested in region.regions {
        substitution = substitution.freeze(nested, span)
      }
      substitution
    }
  }
}

///|
pub fn PVariable::trusted_new(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  ity : Ity,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> PVariable raise {
  if !context.contains(ity.context_anchor()) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "program variable belongs to another context",
    )
  }
  let name_view = name.view()
  let origin = @identity.Origin::user(
    name_view.name,
    name_view.source_span,
    name_view.attributes,
  )
  let pure_symbol = @logic.VSymbol::new(
    context,
    name_view.name,
    origin,
    ity.to_ty(span),
    span,
  )
  { id: context.fresh_id(), name, ity, ghost, pure_symbol }
}

///|
/// Creates Why3's `old_of_pv` snapshot: the program type is purified, the
/// variable is ghost, and the logical identifier retains the clone edge to
/// the original program variable.
pub fn PVariable::trusted_old_snapshot(
  self : PVariable,
  context : @identity.CompilationContext,
  span : @identity.SourceSpan?,
) -> PVariable raise {
  if !context.contains(self.id) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "old snapshot belongs to another compilation context",
    )
  }
  let ity = self.ity.purify()
  let pure_symbol = self.pure_symbol.clone_with_type(
    context,
    ity.to_ty(span),
    span,
  )
  { id: context.fresh_id(), name: self.name, ity, ghost: true, pure_symbol }
}

///|
pub fn PVariable::semantic_id(self : PVariable) -> @identity.SemanticId {
  self.id
}

///|
pub fn PVariable::view(self : PVariable) -> PVariableView {
  {
    id: self.id,
    name: self.name,
    ity: self.ity,
    ghost: self.ghost,
    pure_symbol: self.pure_symbol,
  }
}

///|
pub impl Eq for PVariable with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for PVariable with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
pub fn XSymbol::new(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  ity : Ity,
  span : @identity.SourceSpan?,
  mask? : ProgramMask = Visible,
) -> XSymbol raise MlwError {
  if !context.contains(ity.context_anchor()) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "exception symbol belongs to another context",
    )
  }
  let mask = mask.validate_for_ity(ity, span)
  { id: context.fresh_id(), name, ity, mask }
}

///|
pub fn XSymbol::semantic_id(self : XSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn XSymbol::view(self : XSymbol) -> XSymbolView {
  { id: self.id, name: self.name, ity: self.ity, mask: self.mask }
}

///|
pub impl Eq for XSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for XSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

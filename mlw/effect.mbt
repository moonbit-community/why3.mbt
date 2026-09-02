// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum ProgramTermination {
  Total
  Partial
  Diverges
} derive(Eq, Debug)

///|
pub(all) enum ProgramMask {
  Visible
  Tuple(Array[ProgramMask])
  Ghost
} derive(Eq, Debug)

///|
struct EffectWrite {
  region : Region
  fields : Array[PVariable]
}

///|
priv struct AssignmentWrite {
  region : Region
  fields : Array[(PVariable, Ity)]
}

///|
pub(all) struct EffectWriteView {
  region : Region
  fields : ArrayView[PVariable]
}

///|
struct Effect {
  reads : Array[PVariable]
  writes : Array[EffectWrite]
  taints : Array[Region]
  covers : Array[Region]
  resets : Array[Region]
  raises : Array[XSymbol]
  spoils : Array[@logic.TyVarSymbol]
  termination : ProgramTermination
  ghost : Bool
}

///|
pub(all) struct EffectView {
  reads : ArrayView[PVariable]
  writes : ArrayView[EffectWrite]
  taints : ArrayView[Region]
  covers : ArrayView[Region]
  resets : ArrayView[Region]
  raises : ArrayView[XSymbol]
  spoils : ArrayView[@logic.TyVarSymbol]
  termination : ProgramTermination
  ghost : Bool
}

///|
pub fn ProgramTermination::is_total(self : ProgramTermination) -> Bool {
  self is Total
}

///|
pub fn ProgramTermination::is_partial(self : ProgramTermination) -> Bool {
  self is Partial
}

///|
pub fn ProgramTermination::diverges(self : ProgramTermination) -> Bool {
  self is Diverges
}

///|
fn termination_union(
  left : ProgramTermination,
  right : ProgramTermination,
) -> ProgramTermination {
  match (left, right) {
    (Total, Total) => Total
    (Diverges, _) | (_, Diverges) => Diverges
    _ => Partial
  }
}

///|
pub fn ProgramMask::is_ghost(self : ProgramMask) -> Bool {
  match self {
    Visible => false
    Tuple(items) => items.any(ProgramMask::is_ghost)
    Ghost => true
  }
}

///|
pub fn ProgramMask::reduce(self : ProgramMask) -> ProgramMask {
  match self {
    Visible | Ghost => self
    Tuple(items) => {
      let reduced = items.map(ProgramMask::reduce)
      if reduced.all(item => item is Visible) {
        Visible
      } else if reduced.all(item => item is Ghost) {
        Ghost
      } else {
        Tuple(reduced)
      }
    }
  }
}

///|
pub fn ProgramMask::validate_for_ity(
  self : ProgramMask,
  ity : Ity,
  span : @identity.SourceSpan?,
) -> ProgramMask raise MlwError {
  match self {
    Visible | Ghost => self
    Tuple(masks) =>
      match ity.view() {
        ItyApp(_, arguments, _) if arguments.length() == masks.length() => {
          let validated : Array[ProgramMask] = []
          for index = 0; index < masks.length(); index = index + 1 {
            validated.push(
              masks[index].validate_for_ity(arguments[index], span),
            )
          }
          Tuple(validated).reduce()
        }
        _ =>
          fail_mlw(
            InvalidProgramMask,
            span,
            "tuple mask does not match the program type",
          )
      }
  }
}

///|
pub fn ProgramMask::union(
  self : ProgramMask,
  other : ProgramMask,
  span : @identity.SourceSpan?,
) -> ProgramMask raise MlwError {
  match (self, other) {
    (Visible, mask) | (mask, Ghost) => mask
    (mask, Visible) | (Ghost, mask) => mask
    (Tuple(left), Tuple(right)) => {
      if left.length() != right.length() {
        fail_mlw(InvalidProgramMask, span, "tuple masks have different arity")
      }
      Tuple(
        [
          for index = 0; index < left.length(); index = index + 1 => {
            left[index].union(right[index], span)
          }
        ],
      ).reduce()
    }
  }
}

///|
fn ProgramMask::submask(self : ProgramMask, other : ProgramMask) -> Bool {
  match (self, other) {
    (Visible, _) | (_, Ghost) => true
    (Ghost, mask) => mask.reduce() is Ghost
    (mask, Visible) => mask.reduce() is Visible
    (Tuple(left), Tuple(right)) =>
      left.length() == right.length() &&
      ({
        let mut result = true
        for index = 0; index < left.length(); index = index + 1 {
          result = result && left[index].submask(right[index])
        }
        result
      })
  }
}

///|
pub fn ProgramMask::spills_into(
  self : ProgramMask,
  other : ProgramMask,
) -> Bool {
  !self.submask(other)
}

///|
pub fn ProgramMask::of_variable(variable : PVariable) -> ProgramMask {
  if variable.view().ghost {
    Ghost
  } else {
    Visible
  }
}

///|
pub fn EffectWrite::new(
  region : Region,
  fields : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> EffectWrite raise MlwError {
  let unique : Array[PVariable] = []
  for field in fields {
    require_mlw_context(region.id, field.semantic_id(), span)
    if unique.any(existing => existing == field) {
      fail_mlw(DuplicateEffectField, span, "duplicate field in write effect")
    }
    if !region.symbol.mutable_fields.any(candidate => candidate == field) {
      fail_mlw(WriteImmutable, span, "write targets an immutable field")
    }
    unique.push(field)
  }
  if unique.is_empty() && !region.symbol.flags.private_ {
    fail_mlw(InvalidEffect, span, "empty write requires a private region")
  }
  { region, fields: unique }
}

///|
pub fn EffectWrite::view(self : EffectWrite) -> EffectWriteView {
  { region: self.region, fields: self.fields[:] }
}

///|
fn unique_variables(values : ArrayView[PVariable]) -> Array[PVariable] {
  let result : Array[PVariable] = []
  for value in values {
    if !result.any(existing => existing == value) {
      result.push(value)
    }
  }
  result
}

///|
fn unique_regions(values : ArrayView[Region]) -> Array[Region] {
  let result : Array[Region] = []
  for value in values {
    if !result.any(existing => existing == value) {
      result.push(value)
    }
  }
  result
}

///|
fn unique_exceptions(values : ArrayView[XSymbol]) -> Array[XSymbol] {
  let result : Array[XSymbol] = []
  for value in values {
    if !result.any(existing => existing == value) {
      result.push(value)
    }
  }
  result
}

///|
fn unique_type_variables(
  values : ArrayView[@logic.TyVarSymbol],
) -> Array[@logic.TyVarSymbol] {
  let result : Array[@logic.TyVarSymbol] = []
  for value in values {
    if !result.any(existing => existing == value) {
      result.push(value)
    }
  }
  result
}

///|
fn merge_variables(
  left : ArrayView[PVariable],
  right : ArrayView[PVariable],
) -> Array[PVariable] {
  unique_variables(left.to_owned() + right.to_owned())
}

///|
fn merge_regions(
  left : ArrayView[Region],
  right : ArrayView[Region],
) -> Array[Region] {
  unique_regions(left.to_owned() + right.to_owned())
}

///|
fn merge_exceptions(
  left : ArrayView[XSymbol],
  right : ArrayView[XSymbol],
) -> Array[XSymbol] {
  unique_exceptions(left.to_owned() + right.to_owned())
}

///|
fn merge_type_variables(
  left : ArrayView[@logic.TyVarSymbol],
  right : ArrayView[@logic.TyVarSymbol],
) -> Array[@logic.TyVarSymbol] {
  unique_type_variables(left.to_owned() + right.to_owned())
}

///|
fn validate_effect_context(
  anchor : @identity.SemanticId,
  reads : ArrayView[PVariable],
  writes : ArrayView[EffectWrite],
  regions : ArrayView[Region],
  raises : ArrayView[XSymbol],
  spoils : ArrayView[@logic.TyVarSymbol],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for variable in reads {
    require_mlw_context(anchor, variable.semantic_id(), span)
  }
  for write in writes {
    require_mlw_context(anchor, write.region.id, span)
    for field in write.fields {
      require_mlw_context(anchor, field.semantic_id(), span)
    }
  }
  for region in regions {
    require_mlw_context(anchor, region.id, span)
  }
  for exception in raises {
    require_mlw_context(anchor, exception.id, span)
  }
  for variable in spoils {
    require_mlw_context(anchor, variable.semantic_id(), span)
  }
}

///|
pub fn Effect::trusted_new(
  anchor : @identity.SemanticId,
  reads : ArrayView[PVariable],
  writes : ArrayView[EffectWrite],
  taints : ArrayView[Region],
  covers : ArrayView[Region],
  resets : ArrayView[Region],
  raises : ArrayView[XSymbol],
  spoils : ArrayView[@logic.TyVarSymbol],
  termination : ProgramTermination,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  validate_effect_context(
    anchor,
    reads,
    writes,
    taints.to_owned() + covers.to_owned() + resets.to_owned(),
    raises,
    spoils,
    span,
  )
  if ghost && (termination is Partial || termination is Diverges) {
    fail_mlw(GhostDivergence, span, "ghost computation may not fail or diverge")
  }
  {
    reads: unique_variables(reads),
    writes: merge_writes([], writes),
    taints: unique_regions(taints),
    covers: unique_regions(covers),
    resets: unique_regions(resets),
    raises: unique_exceptions(raises),
    spoils: unique_type_variables(spoils),
    termination,
    ghost,
  }
}

///|
pub fn Effect::pure(ghost : Bool) -> Effect {
  {
    reads: [],
    writes: [],
    taints: [],
    covers: [],
    resets: [],
    raises: [],
    spoils: [],
    termination: Total,
    ghost,
  }
}

///|
pub fn Effect::from_reads(reads : ArrayView[PVariable], ghost : Bool) -> Effect {
  { ..Effect::pure(ghost), reads: unique_variables(reads) }
}

///|
pub fn Effect::view(self : Effect) -> EffectView {
  {
    reads: self.reads[:],
    writes: self.writes[:],
    taints: self.taints[:],
    covers: self.covers[:],
    resets: self.resets[:],
    raises: self.raises[:],
    spoils: self.spoils[:],
    termination: self.termination,
    ghost: self.ghost,
  }
}

///|
pub fn Effect::is_pure(self : Effect) -> Bool {
  self.writes.is_empty() && self.raises.is_empty() && self.termination is Total
}

///|
fn[A : Eq] same_set(left : ArrayView[A], right : ArrayView[A]) -> Bool {
  left.length() == right.length() &&
  left.all(value => right.any(candidate => candidate == value))
}

///|
fn same_writes(
  left : ArrayView[EffectWrite],
  right : ArrayView[EffectWrite],
) -> Bool {
  left.length() == right.length() &&
  left.all(write => {
    right.any(candidate => {
      candidate.region == write.region &&
      same_set(candidate.fields, write.fields)
    })
  })
}

///|
pub impl Eq for Effect with fn equal(self, other) {
  same_set(self.reads, other.reads) &&
  same_writes(self.writes, other.writes) &&
  same_set(self.taints, other.taints) &&
  same_set(self.covers, other.covers) &&
  same_set(self.resets, other.resets) &&
  same_set(self.raises, other.raises) &&
  same_set(self.spoils, other.spoils) &&
  self.termination == other.termination &&
  self.ghost == other.ghost
}

///|
fn read_regions(reads : ArrayView[PVariable]) -> Array[Region] {
  let result : Array[Region] = []
  for variable in reads {
    for region in variable.view().ity.reachable_regions() {
      if !result.any(existing => existing == region) {
        result.push(region)
      }
    }
  }
  result
}

///|
fn visible_write_regions(writes : ArrayView[EffectWrite]) -> Array[Region] {
  let result : Array[Region] = []
  for write in writes {
    if write.region.symbol.flags.private_ ||
      write.fields.any(field => !field.view().ghost) {
      result.push(write.region)
    }
  }
  unique_regions(result)
}

///|
fn check_taints(
  taints : ArrayView[Region],
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if taints.is_empty() {
    return
  }
  for variable in reads {
    if !variable.view().ghost {
      for region in variable.view().ity.visible_regions() {
        if taints.any(taint => taint == region) {
          fail_mlw(
            BadGhostWrite,
            span,
            "ghost write is visible from non-ghost variable \{variable.view().name.view().name} through region \{region.view().symbol.view().logic_type.name()}",
          )
        }
      }
    }
  }
}

///|
fn check_writes(
  writes : ArrayView[EffectWrite],
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let written = [ for write in writes => write.region ]
  for variable in reads {
    for frozen in variable.view().ity.frozen_regions() {
      if written.any(region => region == frozen) {
        fail_mlw(
          IllegalUpdate,
          span,
          "write reaches a frozen component of a live variable",
        )
      }
    }
  }
}

///|
fn check_covers(
  resets : ArrayView[Region],
  covers : ArrayView[Region],
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for variable in reads {
    if variable.view().ity.has_stale_region(resets, covers) {
      fail_mlw(StaleVariable, span, "effect leaves a live variable stale")
    }
  }
}

///|
fn Effect::reset_taints(
  self : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  let visible = visible_write_regions(self.writes)
  if self.ghost {
    check_taints(visible, self.reads, span)
    return { ..self, taints: visible }
  }
  let mut taints = visible.copy()
  for variable in self.reads {
    if !variable.view().ghost {
      for region in variable.view().ity.visible_regions() {
        taints = [ for taint in taints if taint != region => taint ]
      }
    }
  }
  { ..self, taints, }
}

///|
pub fn Effect::read_pre(
  self : Effect,
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  let reads = unique_variables(reads)
  check_taints(self.taints, reads, span)
  { ..self, reads: merge_variables(self.reads, reads) }
}

///|
pub fn Effect::read_post(
  self : Effect,
  reads : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  check_writes(self.writes, reads, span)
  check_covers(self.resets, self.covers, reads, span)
  self.read_pre(reads, span)
}

///|
pub fn Effect::bind(self : Effect, variables : ArrayView[PVariable]) -> Effect {
  let reads : Array[PVariable] = []
  for read in self.reads {
    if !variables.any(variable => variable == read) {
      reads.push(read)
    }
  }
  { ..self, reads, }
}

///|
fn merge_writes(
  left : ArrayView[EffectWrite],
  right : ArrayView[EffectWrite],
) -> Array[EffectWrite] {
  let result = left.to_owned()
  for write in right {
    let mut found = false
    for index = 0; index < result.length(); index = index + 1 {
      if result[index].region == write.region {
        result[index] = {
          region: write.region,
          fields: merge_variables(result[index].fields, write.fields),
        }
        found = true
        break
      }
    }
    if !found {
      result.push(write)
    }
  }
  result
}

///|
pub fn Effect::write(
  reads : ArrayView[PVariable],
  writes : ArrayView[EffectWrite],
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if writes.is_empty() {
    return Effect::from_reads(reads, false)
  }
  let known = read_regions(reads)
  let retained : Array[EffectWrite] = []
  for write in writes {
    if known.any(region => region == write.region) {
      retained.push(write)
    }
  }
  {
    ..Effect::from_reads(reads, false),
    writes: retained,
    covers: [
      for write in retained => write.region
    ],
  }.reset_taints(span)
}

///|
fn check_assignment_skeleton(
  expected : Ity,
  actual : Ity,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if expected == actual {
    return
  }
  match (expected.node, actual.node) {
    (ItyRegion(expected_region), ItyRegion(actual_region)) if expected_region.symbol ==
      actual_region.symbol => {
      if expected_region.arguments.length() != actual_region.arguments.length() ||
        expected_region.regions.length() != actual_region.regions.length() {
        fail_mlw(
          IllegalAssignment,
          span,
          "assigned value has an incompatible region skeleton: expected \{expected.diagnostic_shape()}, received \{actual.diagnostic_shape()}",
        )
      }
      for index = 0
          index < expected_region.arguments.length()
          index = index + 1 {
        check_assignment_skeleton(
          expected_region.arguments[index],
          actual_region.arguments[index],
          span,
        )
      }
      for index = 0; index < expected_region.regions.length(); index = index + 1 {
        check_assignment_skeleton(
          expected_region.regions[index],
          actual_region.regions[index],
          span,
        )
      }
    }
    (
      ItyApplication(expected_symbol, expected_arguments, expected_regions),
      ItyApplication(actual_symbol, actual_arguments, actual_regions),
    ) if expected_symbol == actual_symbol => {
      if expected_arguments.length() != actual_arguments.length() ||
        expected_regions.length() != actual_regions.length() {
        fail_mlw(
          IllegalAssignment,
          span,
          "assigned value has an incompatible region skeleton: expected \{expected.diagnostic_shape()}, received \{actual.diagnostic_shape()}",
        )
      }
      for index = 0; index < expected_arguments.length(); index = index + 1 {
        check_assignment_skeleton(
          expected_arguments[index],
          actual_arguments[index],
          span,
        )
      }
      for index = 0; index < expected_regions.length(); index = index + 1 {
        check_assignment_skeleton(
          expected_regions[index],
          actual_regions[index],
          span,
        )
      }
    }
    _ =>
      fail_mlw(
        IllegalAssignment,
        span,
        "assigned value has an incompatible region skeleton: expected \{expected.diagnostic_shape()}, received \{actual.diagnostic_shape()}",
      )
  }
}

///|
fn assignment_fields_for_region(
  writes : ArrayView[AssignmentWrite],
  region : Region,
) -> Array[(PVariable, Ity)] {
  for write in writes {
    if write.region == region {
      return write.fields
    }
  }
  []
}

///|
fn assigned_field_type(
  fields : ArrayView[(PVariable, Ity)],
  field : PVariable,
  fallback : Ity,
) -> Ity {
  for entry in fields {
    if entry.0 == field {
      return entry.1
    }
  }
  fallback
}

///|
fn append_direct_exposed_regions(regions : Array[Region], ity : Ity) -> Unit {
  for region in ity.exposed_regions() {
    regions.push(region)
  }
}

///|
fn assignment_region_exposed(
  region : Region,
  assigned_fields : ArrayView[(PVariable, Ity)],
  span : @identity.SourceSpan?,
) -> Array[Region] raise MlwError {
  let result : Array[Region] = []
  for field in region.symbol.mutable_fields {
    let expected = region.instantiate_member_ity(field.view().ity, span)
    let actual = assigned_field_type(assigned_fields, field, expected)
    check_assignment_skeleton(expected, actual, span)
    append_direct_exposed_regions(result, actual)
  }
  let argument_limit = if region.symbol.flags.argument_flags.length() <
    region.arguments.length() {
    region.symbol.flags.argument_flags.length()
  } else {
    region.arguments.length()
  }
  for index = 0; index < argument_limit; index = index + 1 {
    if region.symbol.flags.argument_flags[index].fixed {
      append_direct_exposed_regions(result, region.arguments[index])
    }
  }
  let region_limit = if region.symbol.flags.region_flags.length() <
    region.regions.length() {
    region.symbol.flags.region_flags.length()
  } else {
    region.regions.length()
  }
  for index = 0; index < region_limit; index = index + 1 {
    if region.symbol.flags.region_flags[index].fixed {
      append_direct_exposed_regions(result, region.regions[index])
    }
  }
  result
}

///|
fn stitch_assignment_regions(
  pairs : Array[(Region, Region)],
  source : Region,
  target : Region,
  writes : ArrayView[AssignmentWrite],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let source_regions = assignment_region_exposed(source, [], span)
  let target_regions = assignment_region_exposed(
    target,
    assignment_fields_for_region(writes, target),
    span,
  )
  if source_regions.length() != target_regions.length() {
    fail_mlw(
      IllegalAssignment,
      span,
      "assignment changes the region skeleton arity",
    )
  }
  for index = 0; index < source_regions.length(); index = index + 1 {
    let source_region = source_regions[index]
    let target_region = target_regions[index]
    pairs.push((source_region, target_region))
    stitch_assignment_regions(pairs, source_region, target_region, writes, span)
  }
}

///|
fn bind_assignment_region(
  bindings : Array[(Region, Region)],
  source : Region,
  target : Region,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for binding in bindings {
    if binding.0 == source {
      if binding.1 != target {
        fail_mlw(
          IllegalAssignment,
          span,
          "assignment induces inconsistent region aliases",
        )
      }
      return
    }
  }
  bindings.push((source, target))
}

///|
pub fn Effect::assign(
  assignments : ArrayView[(PVariable, PVariable, PVariable)],
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  let reads : Array[PVariable] = []
  let assignment_writes : Array[AssignmentWrite] = []
  let taints : Array[Region] = []
  let mut ghost = true
  for assignment in assignments {
    let (target, field, value) = assignment
    let target_view = target.view()
    let field_view = field.view()
    let value_view = value.view()
    guard target_view.ity.view() is ItyReg(region) else {
      fail_mlw(
        AssignSnapshot,
        span,
        "assignment target is an immutable snapshot",
      )
    }
    if region.symbol.flags.private_ {
      fail_mlw(AssignPrivate, span, "assignment targets a private region")
    }
    if !region.symbol.mutable_fields.any(candidate => candidate == field) {
      fail_mlw(WriteImmutable, span, "assignment targets an immutable field")
    }
    let expected = region.instantiate_member_ity(field_view.ity, span)
    check_assignment_skeleton(expected, value_view.ity, span)
    let mut write_index = -1
    for index = 0; index < assignment_writes.length(); index = index + 1 {
      if assignment_writes[index].region == region {
        write_index = index
        break
      }
    }
    if write_index < 0 {
      assignment_writes.push({ region, fields: [(field, value_view.ity)] })
    } else {
      if assignment_writes[write_index].fields.any(candidate => {
          candidate.0 == field
        }) {
        fail_mlw(DuplicateEffectField, span, "field is assigned twice")
      }
      assignment_writes[write_index] = {
        region,
        fields: assignment_writes[write_index].fields +
        [(field, value_view.ity)],
      }
    }
    if !reads.any(variable => variable == target) {
      reads.push(target)
    }
    if !reads.any(variable => variable == value) {
      reads.push(value)
    }
    ghost = ghost && (target_view.ghost || field_view.ghost || value_view.ghost)
    if (target_view.ghost || value_view.ghost) &&
      !field_view.ghost &&
      !taints.any(candidate => candidate == region) {
      taints.push(region)
    }
  }
  check_taints(taints, reads, span)

  // Stitch the exposed region graph before and after every field update.
  // Deeper transitions are processed first, matching Why3's level map.
  let transitions : Array[(Int, Region, Array[(Region, Region)])] = []
  for write in assignment_writes {
    let pairs : Array[(Region, Region)] = []
    stitch_assignment_regions(
      pairs,
      write.region,
      write.region,
      assignment_writes,
      span,
    )
    transitions.push((-pairs.length(), write.region, pairs))
  }
  transitions.sort_by((left, right) => left.0.compare(right.0))
  let resets : Array[Region] = []
  let forward : Array[(Region, Region)] = []
  let backward : Array[(Region, Region)] = []
  for transition in transitions {
    let (_, root, pairs) = transition
    if resets.any(region => region == root) {
      continue
    }
    for pair in pairs {
      let (source, target) = pair
      if source != target {
        if !resets.any(region => region == source) {
          resets.push(source)
        }
        if !resets.any(region => region == target) {
          resets.push(target)
        }
      }
      bind_assignment_region(forward, source, target, span)
      bind_assignment_region(backward, target, source, span)
    }
  }

  let writes : Array[EffectWrite] = [
    for write in assignment_writes => {
      { region: write.region, fields: [ for entry in write.fields => entry.0 ] }
    }
  ]
  let covers : Array[Region] = []
  for write in writes {
    if !resets.any(region => region == write.region) {
      covers.push(write.region)
    }
  }
  let effect : Effect = {
    reads,
    writes,
    taints,
    covers,
    resets,
    raises: [],
    spoils: [],
    termination: Total,
    ghost,
  }
  check_writes(effect.writes, effect.reads, span)
  effect
}

///|
pub fn Effect::reset(
  self : Effect,
  regions : ArrayView[Region],
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  for region in regions {
    if self.writes.any(write => write.region == region) {
      fail_mlw(InvalidEffect, span, "reset overlaps a write")
    }
  }
  { ..self, resets: merge_regions(self.resets, regions) }
}

///|
fn collect_unwritten_exposed_region(
  result : Array[Region],
  region : Region,
  writes : ArrayView[EffectWrite],
) -> Unit {
  if writes.any(write => write.region == region) ||
    result.any(existing => existing == region) {
    return
  }
  result.push(region)
  let argument_limit = if region.symbol.flags.argument_flags.length() <
    region.arguments.length() {
    region.symbol.flags.argument_flags.length()
  } else {
    region.arguments.length()
  }
  for index = 0; index < argument_limit; index = index + 1 {
    if region.symbol.flags.argument_flags[index].exposed {
      for nested in region.arguments[index].exposed_regions() {
        collect_unwritten_exposed_region(result, nested, writes)
      }
    }
  }
  let region_limit = if region.symbol.flags.region_flags.length() <
    region.regions.length() {
    region.symbol.flags.region_flags.length()
  } else {
    region.regions.length()
  }
  for index = 0; index < region_limit; index = index + 1 {
    if region.symbol.flags.region_flags[index].exposed {
      for nested in region.regions[index].exposed_regions() {
        collect_unwritten_exposed_region(result, nested, writes)
      }
    }
  }
}

///|
fn collect_unwritten_exposed_ity(
  result : Array[Region],
  ity : Ity,
  writes : ArrayView[EffectWrite],
) -> Unit {
  for region in ity.exposed_regions() {
    collect_unwritten_exposed_region(result, region, writes)
  }
}

///|
fn collect_fixed_region_components(
  result : Array[Region],
  region : Region,
  writes : ArrayView[EffectWrite],
) -> Unit {
  let argument_limit = if region.symbol.flags.argument_flags.length() <
    region.arguments.length() {
    region.symbol.flags.argument_flags.length()
  } else {
    region.arguments.length()
  }
  for index = 0; index < argument_limit; index = index + 1 {
    if region.symbol.flags.argument_flags[index].fixed {
      collect_unwritten_exposed_ity(result, region.arguments[index], writes)
    }
  }
  let region_limit = if region.symbol.flags.region_flags.length() <
    region.regions.length() {
    region.symbol.flags.region_flags.length()
  } else {
    region.regions.length()
  }
  for index = 0; index < region_limit; index = index + 1 {
    if region.symbol.flags.region_flags[index].fixed {
      collect_unwritten_exposed_ity(result, region.regions[index], writes)
    }
  }
}

///|
/// Computes the regions made stale when mutable fields are fully overwritten.
/// This is the direct counterpart of Why3's `eff_reset_overwritten`.
pub fn Effect::reset_overwritten(
  self : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if !self.resets.is_empty() {
    fail_mlw(
      InvalidEffect,
      span,
      "overwritten resets require an effect without existing resets",
    )
  }
  let preserved : Array[Region] = []
  let replaced : Array[Region] = []
  for write in self.writes {
    if !preserved.any(region => region == write.region) {
      preserved.push(write.region)
    }
    collect_fixed_region_components(preserved, write.region, self.writes)
    for field in write.region.symbol.mutable_fields {
      let field_type = write.region.instantiate_member_ity(
        field.view().ity,
        span,
      )
      if write.fields.any(written => written == field) {
        collect_unwritten_exposed_ity(replaced, field_type, self.writes)
      } else {
        collect_unwritten_exposed_ity(preserved, field_type, self.writes)
      }
    }
  }
  let resets : Array[Region] = []
  for region in replaced {
    if !preserved.any(saved => saved == region) {
      resets.push(region)
    }
  }
  { ..self, resets, }
}

///|
fn instantiate_effect_region(
  substitution : ItySubstitution,
  source : Region,
  span : @identity.SourceSpan?,
) -> Region raise MlwError {
  for entry in substitution.regions {
    if entry.0 == source {
      guard entry.1.view() is ItyReg(target) else {
        fail_mlw(
          IllegalSnapshot,
          span,
          "affected region was instantiated with a snapshot",
        )
      }
      return target
    }
  }
  fail_mlw(UnboundRegion, span, "effect region substitution is incomplete")
}

///|
fn effect_region_is_safe(effect : Effect, region : Region) -> Bool {
  !effect.covers.any(cover => cover == region) &&
  !Ity::region(region).has_stale_region(effect.resets, effect.covers)
}

///|
fn validate_effect_impact(
  substitution : ItySubstitution,
  sources : ArrayView[Region],
  span : @identity.SourceSpan?,
) -> Array[(Region, Region)] raise MlwError {
  let mapped : Array[(Region, Region)] = []
  for source in sources {
    let mut direct_target : Region? = None
    for entry in substitution.regions {
      let container = entry.0
      if !container.reachable_regions().any(region => region == source) {
        continue
      }
      match entry.1.node {
        ItyApplication(_, _, _) =>
          fail_mlw(
            IllegalSnapshot,
            span,
            "a region containing an affected component became a snapshot",
          )
        ItyRegion(target) if container == source => direct_target = Some(target)
        ItyVariable(_) if container == source =>
          fail_mlw(
            IllegalSnapshot,
            span,
            "an affected region became a type variable",
          )
        ItyRegion(_) | ItyVariable(_) => ()
      }
    }
    guard direct_target is Some(target) else {
      fail_mlw(UnboundRegion, span, "effect region substitution is incomplete")
    }
    if mapped.any(entry => entry.1 == target && entry.0 != source) {
      fail_mlw(
        IllegalAlias,
        span,
        "distinct affected regions were instantiated with one region",
      )
    }
    mapped.push((source, target))
  }
  mapped
}

///|
pub fn Effect::instantiate(
  self : Effect,
  substitution : ItySubstitution,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  let safe_sources : Array[Region] = []
  let impact_sources : Array[Region] = []
  for entry in substitution.regions {
    if effect_region_is_safe(self, entry.0) {
      if !safe_sources.any(region => region == entry.0) {
        safe_sources.push(entry.0)
      }
    } else if !impact_sources.any(region => region == entry.0) {
      impact_sources.push(entry.0)
    }
  }
  let impact = validate_effect_impact(substitution, impact_sources, span)

  // Unaffected region and type substitutions must stay outside the region
  // graph impacted by writes, covers, taints, or resets.
  let unaffected_targets : Array[Region] = []
  for source in safe_sources {
    for entry in substitution.regions {
      if entry.0 == source && entry.1.node is ItyRegion(target) {
        if !unaffected_targets.any(region => region == target) {
          unaffected_targets.push(target)
        }
      }
    }
  }
  for entry in substitution.type_variables {
    for region in entry.1.reachable_regions() {
      if !unaffected_targets.any(existing => existing == region) {
        unaffected_targets.push(region)
      }
    }
  }
  for entry in impact {
    if unaffected_targets.any(region => region == entry.1) {
      let aliases : Array[String] = []
      for source in safe_sources {
        for binding in substitution.regions {
          if binding.0 == source &&
            binding.1.node is ItyRegion(target) &&
            target == entry.1 {
            aliases.push("safe rho#\{source.semantic_id().local_id()}")
          }
        }
      }
      for binding in substitution.type_variables {
        if binding.1.reachable_regions().any(region => region == entry.1) {
          aliases.push(
            "type '\{binding.0.name()}#\{binding.0.semantic_id().local_id()}",
          )
        }
      }
      fail_mlw(
        IllegalAlias,
        span,
        "an unaffected instantiation (\{aliases.join(", ")}) aliases affected rho#\{entry.0.semantic_id().local_id()} at rho#\{entry.1.semantic_id().local_id()}",
      )
    }
  }

  let writes : Array[EffectWrite] = []
  for write in self.writes {
    writes.push({
      region: instantiate_effect_region(substitution, write.region, span),
      fields: write.fields,
    })
  }
  let spoils : Array[@logic.TyVarSymbol] = []
  for entry in substitution.type_variables {
    if self.spoils.any(variable => variable == entry.0) {
      if !entry.1.is_pure() {
        fail_mlw(
          ImpureVariable,
          span,
          "spoiled type variable was instantiated with an impure type",
        )
      }
      for escaped in entry.1.reachable_type_variables() {
        if !spoils.any(existing => existing == escaped) {
          spoils.push(escaped)
        }
      }
    }
  }
  {
    ..self,
    writes,
    taints: self.taints.map(region => {
      instantiate_effect_region(substitution, region, span)
    }),
    covers: self.covers.map(region => {
      instantiate_effect_region(substitution, region, span)
    }),
    resets: self.resets.map(region => {
      instantiate_effect_region(substitution, region, span)
    }),
    spoils,
  }
}

///|
fn Effect::remap_variables(
  self : Effect,
  substitutions : ArrayView[(PVariable, PVariable)],
) -> Effect {
  fn remap(
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

  {
    ..self,
    reads: unique_variables(
      self.reads.map(variable => remap(substitutions, variable)),
    ),
  }
}

///|
pub fn Effect::raise_exception(self : Effect, exception : XSymbol) -> Effect {
  { ..self, raises: unique_exceptions(self.raises + [exception]) }
}

///|
pub fn Effect::catch_exception(self : Effect, exception : XSymbol) -> Effect {
  {
    ..self,
    raises: [
      for raised in self.raises if raised != exception => raised
    ],
  }
}

///|
pub fn Effect::spoil(self : Effect, ity : Ity) -> Effect {
  {
    ..self,
    spoils: merge_type_variables(self.spoils, ity.reachable_type_variables()),
  }
}

///|
pub fn Effect::partial(
  self : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if self.termination is Partial || self.termination is Diverges {
    return self
  }
  if self.ghost {
    fail_mlw(GhostDivergence, span, "ghost computation may not fail")
  }
  { ..self, termination: Partial }
}

///|
pub fn Effect::diverge(
  self : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if self.termination is Diverges {
    return self
  }
  if self.ghost {
    fail_mlw(GhostDivergence, span, "ghost computation may not diverge")
  }
  { ..self, termination: Diverges }
}

///|
pub fn Effect::ghostify(
  self : Effect,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if !ghost || self.ghost {
    return self
  }
  if !(self.termination is Total) {
    fail_mlw(GhostDivergence, span, "ghost computation may not fail or diverge")
  }
  { ..self, ghost: true }.reset_taints(span)
}

///|
fn Effect::ghostify_weak(
  self : Effect,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if !ghost || self.ghost {
    return self
  }
  if !(self.termination is Total) || !self.raises.is_empty() {
    return self
  }
  let visible = visible_write_regions(self.writes)
  if unique_regions(self.taints) != visible {
    return self
  }
  self.ghostify(true, span)
}

///|
fn contaminate(
  source : Effect,
  target : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if source.ghost && !source.raises.is_empty() {
    target.ghostify(true, span)
  } else {
    target
  }
}

///|
fn contaminate_weak(
  source : Effect,
  target : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  if !source.ghost {
    target
  } else if source.raises.is_empty() {
    target.ghostify_weak(true, span)
  } else {
    target.ghostify(true, span)
  }
}

///|
fn remove_stale_regions(
  regions : ArrayView[Region],
  effect : Effect,
) -> Array[Region] {
  let live : Array[Region] = []
  for region in regions {
    if !Ity::region(region).has_stale_region(effect.resets, effect.covers) {
      live.push(region)
    }
  }
  live
}

///|
fn Effect::union_raw(self : Effect, other : Effect) -> Effect {
  {
    reads: merge_variables(self.reads, other.reads),
    writes: merge_writes(self.writes, other.writes),
    taints: merge_regions(self.taints, other.taints),
    covers: merge_regions(
      remove_stale_regions(self.covers, other),
      remove_stale_regions(other.covers, self),
    ),
    resets: merge_regions(self.resets, other.resets),
    raises: merge_exceptions(self.raises, other.raises),
    spoils: merge_type_variables(self.spoils, other.spoils),
    termination: termination_union(self.termination, other.termination),
    ghost: self.ghost && other.ghost,
  }
}

///|
pub fn Effect::union_parallel(
  self : Effect,
  other : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  check_taints(self.taints, other.reads, span)
  check_taints(other.taints, self.reads, span)
  let left = contaminate_weak(other, self, span)
  let right = contaminate_weak(self, other, span)
  left.union_raw(right)
}

///|
pub fn Effect::union_sequential(
  self : Effect,
  other : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  check_writes(self.writes, other.reads, span)
  check_covers(self.resets, self.covers, other.reads, span)
  check_taints(self.taints, other.reads, span)
  check_taints(other.taints, self.reads, span)
  let left = contaminate_weak(other, self, span)
  let right = contaminate(self, other, span)
  left.union_raw(right)
}

///|
pub fn Effect::fusion(
  self : Effect,
  other : Effect,
  span : @identity.SourceSpan?,
) -> Effect raise MlwError {
  let combined = self.union_parallel(other, span)
  let writes : Array[EffectWrite] = []
  for write in combined.writes {
    if combined.covers.any(region => region == write.region) {
      writes.push(write)
    }
  }
  let taints : Array[Region] = []
  for region in combined.taints {
    if combined.covers.any(cover => cover == region) {
      taints.push(region)
    }
  }
  { ..combined, writes, taints }
}

///|
pub fn Effect::affected(self : Effect, ity : Ity) -> Bool {
  let written = [ for write in self.writes => write.region ]
  ity
  .reachable_regions()
  .any(region => written.any(candidate => candidate == region))
}

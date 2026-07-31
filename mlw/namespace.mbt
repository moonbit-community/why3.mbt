// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct ProgramNamespace {
  types : Array[(Bytes, ProgramTypeSymbol)]
  variables : Array[(Bytes, PVariable)]
  routines : Array[(Bytes, RoutineSymbol)]
  routine_overloads : Array[(Bytes, Array[RoutineSymbol])]
  exceptions : Array[(Bytes, XSymbol)]
  subspaces : Array[(Bytes, ProgramNamespace)]
}

///|
pub(all) struct ProgramNamespaceView {
  types : ArrayView[(Bytes, ProgramTypeSymbol)]
  variables : ArrayView[(Bytes, PVariable)]
  routines : ArrayView[(Bytes, RoutineSymbol)]
  routine_overloads : ArrayView[(Bytes, Array[RoutineSymbol])]
  exceptions : ArrayView[(Bytes, XSymbol)]
  subspaces : ArrayView[(Bytes, ProgramNamespace)]
}

///|
pub fn ProgramNamespace::empty() -> ProgramNamespace {
  {
    types: [],
    variables: [],
    routines: [],
    routine_overloads: [],
    exceptions: [],
    subspaces: [],
  }
}

///|
pub fn ProgramNamespace::view(self : ProgramNamespace) -> ProgramNamespaceView {
  {
    types: self.types[:],
    variables: self.variables[:],
    routines: self.routines[:],
    routine_overloads: self.routine_overloads[:],
    exceptions: self.exceptions[:],
    subspaces: self.subspaces[:],
  }
}

///|
fn[A] find_program_entry(
  entries : ArrayView[(Bytes, A)],
  name : BytesView,
) -> A? {
  for entry in entries {
    let (entry_name, value) = entry
    if entry_name[:] == name {
      return Some(value)
    }
  }
  None
}

///|
fn[A : Eq] add_program_entry(
  entries : ArrayView[(Bytes, A)],
  name : BytesView,
  value : A,
  span : @identity.SourceSpan?,
) -> Array[(Bytes, A)] raise MlwError {
  let result = entries.to_owned()
  for entry in result {
    let (entry_name, existing) = entry
    if entry_name[:] == name {
      if existing == value {
        return result
      }
      fail_mlw(
        DuplicateProgramName,
        span,
        "program name '\{name}' is already bound",
      )
    }
  }
  result.push((name.to_owned(), value))
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
fn routine_has_reference_argument(routine : RoutineSymbol) -> Bool {
  routine.view().cty.view().arguments.any(argument => {
    argument.view().name.view().attributes.any(attribute => {
      attribute == b"mlw:reference_var"
    })
  })
}

///|
priv enum RoutineOverload {
  FixedResult(Ity)
  SameType
  NotOverloadable
}

///|
fn routine_overload(routine : RoutineSymbol) -> RoutineOverload {
  let cty = routine.view().cty
  let view = cty.view()
  if cty.is_ghost() || view.mask != Visible || view.arguments.is_empty() {
    return NotOverloadable
  }
  let first = view.arguments[0].view()
  if first.ghost ||
    view.arguments.any(argument => {
      argument.view().ghost || argument.view().ity != first.ity
    }) {
    return NotOverloadable
  }
  if view.result == first.ity {
    SameType
  } else if view.result.is_closed() && view.result.is_pure() {
    FixedResult(view.result)
  } else {
    NotOverloadable
  }
}

///|
fn routines_share_overload(left : RoutineSymbol, right : RoutineSymbol) -> Bool {
  let left_view = left.view().cty.view()
  let right_view = right.view().cty.view()
  if left_view.arguments.length() != right_view.arguments.length() {
    return false
  }
  match (routine_overload(left), routine_overload(right)) {
    (SameType, SameType) => true
    (FixedResult(left), FixedResult(right)) => left == right
    _ => false
  }
}

///|
fn imported_routine_candidates(
  existing : ArrayView[RoutineSymbol],
  incoming : RoutineSymbol,
) -> Array[RoutineSymbol] {
  if existing.any(routine => routine == incoming) {
    return existing.to_owned()
  }
  if existing.is_empty() {
    return [incoming]
  }
  let representative = existing[0]
  if routine_has_reference_argument(representative) ||
    routine_has_reference_argument(incoming) ||
    !routines_share_overload(representative, incoming) {
    return [incoming]
  }
  let incoming_arguments = incoming.view().cty.view().arguments
  let incoming_first = incoming_arguments[0].view().ity
  let result = [
    for routine in existing if routine.view().cty.view().arguments[0].view().ity !=
    incoming_first => routine
  ]
  result.push(incoming)
  result
}

///|
fn ProgramNamespace::unqualified_routine_candidates(
  self : ProgramNamespace,
  name : BytesView,
) -> Array[RoutineSymbol] {
  match find_program_entry(self.routine_overloads, name) {
    Some(routines) => routines.copy()
    None =>
      match find_program_entry(self.routines, name) {
        Some(routine) => [routine]
        None => []
      }
  }
}

///|
fn set_named_routine_candidates(
  routines : ArrayView[(Bytes, RoutineSymbol)],
  overloads : ArrayView[(Bytes, Array[RoutineSymbol])],
  name : BytesView,
  candidates : ArrayView[RoutineSymbol],
) -> (Array[(Bytes, RoutineSymbol)], Array[(Bytes, Array[RoutineSymbol])]) {
  let updated_routines = routines.to_owned()
  let updated_overloads = overloads.to_owned()
  let mut routine_found = false
  for index, entry in updated_routines {
    if entry.0[:] == name {
      updated_routines[index] = (entry.0, candidates[candidates.length() - 1])
      routine_found = true
      break
    }
  }
  if !routine_found {
    updated_routines.push(
      (name.to_owned(), candidates[candidates.length() - 1]),
    )
  }
  let mut overload_index = -1
  for index, entry in updated_overloads {
    if entry.0[:] == name {
      overload_index = index
      break
    }
  }
  if candidates.length() > 1 {
    let entry = (name.to_owned(), candidates.to_owned())
    if overload_index >= 0 {
      updated_overloads[overload_index] = entry
    } else {
      updated_overloads.push(entry)
    }
  } else if overload_index >= 0 {
    ignore(updated_overloads.remove(overload_index))
  }
  updated_routines.sort_by((left, right) => left.0.lexical_compare(right.0))
  updated_overloads.sort_by((left, right) => left.0.lexical_compare(right.0))
  (updated_routines, updated_overloads)
}

///|
pub fn ProgramNamespace::add_type(
  self : ProgramNamespace,
  name : BytesView,
  symbol : ProgramTypeSymbol,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  { ..self, types: add_program_entry(self.types, name, symbol, span) }
}

///|
pub fn ProgramNamespace::add_variable(
  self : ProgramNamespace,
  name : BytesView,
  variable : PVariable,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  { ..self, variables: add_program_entry(self.variables, name, variable, span) }
}

///|
pub fn ProgramNamespace::add_routine(
  self : ProgramNamespace,
  name : BytesView,
  symbol : RoutineSymbol,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  { ..self, routines: add_program_entry(self.routines, name, symbol, span) }
}

///|
pub fn ProgramNamespace::add_exception(
  self : ProgramNamespace,
  name : BytesView,
  symbol : XSymbol,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  { ..self, exceptions: add_program_entry(self.exceptions, name, symbol, span) }
}

///|
pub fn ProgramNamespace::add_subspace(
  self : ProgramNamespace,
  name : BytesView,
  nested : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  let subspaces = self.subspaces.copy()
  for index, entry in subspaces {
    if entry.0[:] == name {
      subspaces[index] = (entry.0, entry.1.merge(nested, span))
      return { ..self, subspaces, }
    }
  }
  subspaces.push((name.to_owned(), nested))
  subspaces.sort_by((left, right) => left.0.lexical_compare(right.0))
  { ..self, subspaces, }
}

///|
fn ProgramNamespace::qualified_parent(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> (ProgramNamespace, Bytes) raise MlwError {
  if path.is_empty() {
    fail_mlw(UnboundProgramName, span, "qualified program name is empty")
  }
  let mut current = self
  for index = 0; index + 1 < path.length(); index = index + 1 {
    match find_program_entry(current.subspaces, path[index]) {
      Some(nested) => current = nested
      None => fail_mlw(UnboundProgramName, span, "unknown program subspace")
    }
  }
  (current, path[path.length() - 1])
}

///|
pub fn ProgramNamespace::find_type(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  let (parent, name) = self.qualified_parent(path, span)
  match find_program_entry(parent.types, name) {
    Some(symbol) => symbol
    None => fail_mlw(UnboundProgramName, span, "unknown program type")
  }
}

///|
fn ProgramNamespace::find_type_by_logic_option(
  self : ProgramNamespace,
  symbol : @logic.TypeSymbol,
) -> ProgramTypeSymbol? {
  for entry in self.types {
    if entry.1.view().logic_type == symbol {
      return Some(entry.1)
    }
  }
  for entry in self.subspaces {
    match entry.1.find_type_by_logic_option(symbol) {
      Some(found) => return Some(found)
      None => ()
    }
  }
  None
}

///|
/// Resolves the program counterpart of an already resolved core type symbol
/// by semantic identity, including qualified imported subspaces.
pub fn ProgramNamespace::find_type_by_logic(
  self : ProgramNamespace,
  symbol : @logic.TypeSymbol,
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  match self.find_type_by_logic_option(symbol) {
    Some(found) => found
    None =>
      fail_mlw(
        UnboundProgramName,
        span,
        "core type '\{symbol.name()}' (#\{symbol.semantic_id().local_id()}) has no program-type counterpart in this namespace",
      )
  }
}

///|
pub fn ProgramNamespace::find_variable(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> PVariable raise MlwError {
  match self.find_variable_option(path) {
    Some(variable) => variable
    None => fail_mlw(UnboundProgramName, span, "unknown program variable")
  }
}

///|
pub fn ProgramNamespace::find_variable_option(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
) -> PVariable? {
  if path.is_empty() {
    return None
  }
  let mut current = self
  for index = 0; index + 1 < path.length(); index = index + 1 {
    match find_program_entry(current.subspaces, path[index]) {
      Some(nested) => current = nested
      None => return None
    }
  }
  find_program_entry(current.variables, path[path.length() - 1])
}

///|
pub fn ProgramNamespace::find_routine(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  match self.find_routine_option(path) {
    Some(symbol) => symbol
    None => fail_mlw(UnboundProgramName, span, "unknown routine")
  }
}

///|
pub fn ProgramNamespace::find_exception(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> XSymbol raise MlwError {
  let (parent, name) = self.qualified_parent(path, span)
  match find_program_entry(parent.exceptions, name) {
    Some(symbol) => symbol
    None => fail_mlw(UnboundProgramName, span, "unknown exception")
  }
}

///|
/// Performs the program-first half of Why3's expression lookup.  The caller
/// may fall back to the pure namespace when no routine is present (notably for
/// the polymorphic built-in equality symbol).
pub fn ProgramNamespace::find_routine_option(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
) -> RoutineSymbol? {
  if path.is_empty() {
    return None
  }
  let mut current = self
  for index = 0; index + 1 < path.length(); index = index + 1 {
    match find_program_entry(current.subspaces, path[index]) {
      Some(nested) => current = nested
      None => return None
    }
  }
  find_program_entry(current.routines, path[path.length() - 1])
}

///|
/// Returns every compatible program notation retained by import merging.
/// Export namespaces contain at most one candidate for each name.
pub fn ProgramNamespace::find_routine_candidates(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
) -> Array[RoutineSymbol] {
  if path.is_empty() {
    return []
  }
  let mut current = self
  for index = 0; index + 1 < path.length(); index = index + 1 {
    match find_program_entry(current.subspaces, path[index]) {
      Some(nested) => current = nested
      None => return []
    }
  }
  current.unqualified_routine_candidates(path[path.length() - 1])
}

///|
fn ProgramNamespace::find_routine_by_logic_option(
  self : ProgramNamespace,
  symbol : @logic.LSymbol,
) -> RoutineSymbol? {
  for entry in self.routines {
    if entry.1.view().logic is RLls(logic_symbol) && logic_symbol == symbol {
      return Some(entry.1)
    }
  }
  for entry in self.subspaces {
    match entry.1.find_routine_by_logic_option(symbol) {
      Some(found) => return Some(found)
      None => ()
    }
  }
  None
}

///|
/// Resolves the program counterpart of an already resolved logical symbol by
/// semantic identity. This is used for generated constructors and projections
/// whose source spelling may be qualified or imported under another scope.
pub fn ProgramNamespace::find_routine_by_logic(
  self : ProgramNamespace,
  symbol : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  match self.find_routine_by_logic_option(symbol) {
    Some(found) => found
    None =>
      fail_mlw(
        UnboundProgramName,
        span,
        "logical symbol has no program-routine counterpart in this namespace",
      )
  }
}

///|
fn ProgramNamespace::find_projection_by_field_option(
  self : ProgramNamespace,
  field : PVariable,
) -> RoutineSymbol? {
  for entry in self.routines {
    if entry.1.view().field is Some(candidate) && candidate == field {
      return Some(entry.1)
    }
  }
  for entry in self.subspaces {
    match entry.1.find_projection_by_field_option(field) {
      Some(found) => return Some(found)
      None => ()
    }
  }
  None
}

///|
pub fn ProgramNamespace::find_projection_by_field(
  self : ProgramNamespace,
  field : PVariable,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  match self.find_projection_by_field_option(field) {
    Some(found) => found
    None =>
      fail_mlw(
        UnboundProgramName,
        span,
        "program field has no projection in this namespace",
      )
  }
}

///|
/// Selects a qualified program subspace for `scope ... in` expressions.
/// This mirrors the pure Namespace operation without rebuilding symbols from
/// their names.
pub fn ProgramNamespace::import_scope(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  if path.is_empty() {
    fail_mlw(UnboundProgramName, span, "program scope path is empty")
  }
  let mut current = self
  for segment in path {
    match find_program_entry(current.subspaces, segment) {
      Some(nested) => current = nested
      None => fail_mlw(UnboundProgramName, span, "unknown program scope")
    }
  }
  self.merge(current, span)
}

///|
/// Opens a program subspace for lexical lookup, allowing its local bindings to
/// shadow ambient unqualified bindings without changing either namespace.
pub fn ProgramNamespace::open_scope(
  self : ProgramNamespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  if path.is_empty() {
    fail_mlw(UnboundProgramName, span, "program scope path is empty")
  }
  let mut current = self
  for segment in path {
    match find_program_entry(current.subspaces, segment) {
      Some(nested) => current = nested
      None => fail_mlw(UnboundProgramName, span, "unknown program scope")
    }
  }
  self.overlay(current)
}

///|
fn[A : Eq] merge_program_entries(
  left : ArrayView[(Bytes, A)],
  right : ArrayView[(Bytes, A)],
  span : @identity.SourceSpan?,
) -> Array[(Bytes, A)] raise MlwError {
  let result = left.to_owned()
  for entry in right {
    let (name, value) = entry
    match find_program_entry(result, name) {
      None => result.push((name, value))
      Some(existing) =>
        if existing != value {
          fail_mlw(
            AmbiguousProgramName,
            span,
            "program import creates an ambiguous name",
          )
        }
    }
  }
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
fn[A] overlay_program_entries(
  inherited : ArrayView[(Bytes, A)],
  overrides : ArrayView[(Bytes, A)],
) -> Array[(Bytes, A)] {
  let result = inherited.to_owned()
  for entry in overrides {
    let (name, value) = entry
    let mut replaced = false
    for index, existing in result {
      if existing.0 == name {
        result[index] = (name, value)
        replaced = true
        break
      }
    }
    if !replaced {
      result.push((name, value))
    }
  }
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
fn overlay_program_subspaces(
  inherited : ArrayView[(Bytes, ProgramNamespace)],
  overrides : ArrayView[(Bytes, ProgramNamespace)],
) -> Array[(Bytes, ProgramNamespace)] {
  let result = inherited.to_owned()
  for entry in overrides {
    let (name, nested) = entry
    let mut merged = false
    for index, existing in result {
      if existing.0 == name {
        result[index] = (name, existing.1.overlay(nested))
        merged = true
        break
      }
    }
    if !merged {
      result.push((name, nested))
    }
  }
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
/// Overlays scope-local program bindings on inherited lookup bindings after
/// the local export namespace has independently rejected duplicates.
pub fn ProgramNamespace::overlay(
  self : ProgramNamespace,
  overrides : ProgramNamespace,
) -> ProgramNamespace {
  let mut routines = self.routines.copy()
  let mut routine_overloads = self.routine_overloads.copy()
  for entry in overrides.routines {
    let name = entry.0
    let incoming = overrides.unqualified_routine_candidates(name)
    for routine in incoming {
      let current = match find_program_entry(routine_overloads, name) {
        Some(candidates) => candidates
        None =>
          match find_program_entry(routines, name) {
            Some(existing) => [existing]
            None => []
          }
      }
      let candidates = imported_routine_candidates(current, routine)
      let updated = set_named_routine_candidates(
        routines, routine_overloads, name, candidates,
      )
      routines = updated.0
      routine_overloads = updated.1
    }
  }
  {
    types: overlay_program_entries(self.types, overrides.types),
    variables: overlay_program_entries(self.variables, overrides.variables),
    routines,
    routine_overloads,
    exceptions: overlay_program_entries(self.exceptions, overrides.exceptions),
    subspaces: overlay_program_subspaces(self.subspaces, overrides.subspaces),
  }
}

///|
pub fn ProgramNamespace::merge(
  self : ProgramNamespace,
  imported : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  let subspaces = self.subspaces.copy()
  for entry in imported.subspaces {
    let (name, imported_space) = entry
    match find_program_entry(subspaces, name) {
      None => subspaces.push((name, imported_space))
      Some(existing) => {
        let merged = existing.merge(imported_space, span)
        for index, current in subspaces {
          if current.0 == name {
            subspaces[index] = (name, merged)
            break
          }
        }
      }
    }
  }
  subspaces.sort_by((left, right) => left.0.lexical_compare(right.0))
  {
    types: merge_program_entries(self.types, imported.types, span),
    variables: merge_program_entries(self.variables, imported.variables, span),
    routines: merge_program_entries(self.routines, imported.routines, span),
    routine_overloads: [],
    exceptions: merge_program_entries(
      self.exceptions,
      imported.exceptions,
      span,
    ),
    subspaces,
  }
}

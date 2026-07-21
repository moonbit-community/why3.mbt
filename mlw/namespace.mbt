// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct ProgramNamespace {
  types : Array[(Bytes, ProgramTypeSymbol)]
  routines : Array[(Bytes, RoutineSymbol)]
  subspaces : Array[(Bytes, ProgramNamespace)]
}

///|
pub(all) struct ProgramNamespaceView {
  types : ArrayView[(Bytes, ProgramTypeSymbol)]
  routines : ArrayView[(Bytes, RoutineSymbol)]
  subspaces : ArrayView[(Bytes, ProgramNamespace)]
}

///|
pub fn ProgramNamespace::empty() -> ProgramNamespace {
  { types: [], routines: [], subspaces: [] }
}

///|
pub fn ProgramNamespace::view(self : ProgramNamespace) -> ProgramNamespaceView {
  {
    types: self.types[:],
    routines: self.routines[:],
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
      fail_mlw(DuplicateProgramName, span, "program name is already bound")
    }
  }
  result.push((name.to_owned(), value))
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
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
pub fn ProgramNamespace::add_routine(
  self : ProgramNamespace,
  name : BytesView,
  symbol : RoutineSymbol,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  { ..self, routines: add_program_entry(self.routines, name, symbol, span) }
}

///|
pub fn ProgramNamespace::add_subspace(
  self : ProgramNamespace,
  name : BytesView,
  nested : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> ProgramNamespace raise MlwError {
  let subspaces = self.subspaces.copy()
  if find_program_entry(subspaces, name) is Some(_) {
    fail_mlw(DuplicateProgramName, span, "program subspace is already bound")
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
        "core type has no program-type counterpart in this namespace",
      )
  }
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
    routines: merge_program_entries(self.routines, imported.routines, span),
    subspaces,
  }
}

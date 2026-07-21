// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct Namespace {
  types : Array[(Bytes, @logic.TypeSymbol)]
  logic : Array[(Bytes, @logic.LSymbol)]
  propositions : Array[(Bytes, @logic.PrSymbol)]
  subspaces : Array[(Bytes, Namespace)]
}

///|
pub(all) struct NamespaceView {
  types : ArrayView[(Bytes, @logic.TypeSymbol)]
  logic : ArrayView[(Bytes, @logic.LSymbol)]
  propositions : ArrayView[(Bytes, @logic.PrSymbol)]
  subspaces : ArrayView[(Bytes, Namespace)]
}

///|
pub fn Namespace::empty() -> Namespace {
  { types: [], logic: [], propositions: [], subspaces: [] }
}

///|
pub fn Namespace::view(self : Namespace) -> NamespaceView {
  {
    types: self.types[:],
    logic: self.logic[:],
    propositions: self.propositions[:],
    subspaces: self.subspaces[:],
  }
}

///|
fn Namespace::validate_context(
  self : Namespace,
  anchor : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  for entry in self.types {
    require_same_id(anchor, entry.1.semantic_id(), span)
  }
  for entry in self.logic {
    require_same_id(anchor, entry.1.semantic_id(), span)
  }
  for entry in self.propositions {
    require_same_id(anchor, entry.1.semantic_id(), span)
  }
  for entry in self.subspaces {
    entry.1.validate_context(anchor, span)
  }
}

///|
fn[A] lookup_entry(entries : ArrayView[(Bytes, A)], name : BytesView) -> A? {
  for entry in entries {
    let (entry_name, value) = entry
    if entry_name[:] == name {
      return Some(value)
    }
  }
  None
}

///|
fn[A : Eq] add_entry(
  entries : ArrayView[(Bytes, A)],
  name : BytesView,
  value : A,
  span : @identity.SourceSpan?,
) -> Array[(Bytes, A)] raise TheoryError {
  let result = entries.to_owned()
  for entry in result {
    let (existing_name, existing_value) = entry
    if existing_name[:] == name {
      if existing_value == value {
        return result
      }
      fail_theory(DuplicateName, span, "namespace name is already bound")
    }
  }
  result.push((name.to_owned(), value))
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
pub fn Namespace::add_type(
  self : Namespace,
  name : BytesView,
  symbol : @logic.TypeSymbol,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  { ..self, types: add_entry(self.types, name, symbol, span) }
}

///|
pub fn Namespace::add_logic(
  self : Namespace,
  name : BytesView,
  symbol : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  { ..self, logic: add_entry(self.logic, name, symbol, span) }
}

///|
pub fn Namespace::add_proposition(
  self : Namespace,
  name : BytesView,
  symbol : @logic.PrSymbol,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  { ..self, propositions: add_entry(self.propositions, name, symbol, span) }
}

///|
pub fn Namespace::add_subspace(
  self : Namespace,
  name : BytesView,
  nested : Namespace,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  let subspaces = self.subspaces.copy()
  for entry in subspaces {
    let (existing_name, _) = entry
    if existing_name[:] == name {
      fail_theory(DuplicateName, span, "namespace subspace is already bound")
    }
  }
  subspaces.push((name.to_owned(), nested))
  subspaces.sort_by((left, right) => left.0.lexical_compare(right.0))
  { ..self, subspaces, }
}

///|
pub fn Namespace::find_subspace(
  self : Namespace,
  name : BytesView,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  match lookup_entry(self.subspaces, name) {
    Some(nested) => nested
    None => fail_theory(UnboundName, span, "unknown namespace subspace")
  }
}

///|
pub fn Namespace::find_namespace(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  let mut current = self
  for segment in path {
    current = current.find_subspace(segment, span)
  }
  current
}

///|
pub fn Namespace::import_scope(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  self.merge(self.find_namespace(path, span), span)
}

///|
fn Namespace::qualified_parent(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> (Namespace, Bytes) raise TheoryError {
  if path.is_empty() {
    fail_theory(InvalidQualifiedName, span, "qualified name is empty")
  }
  let mut current = self
  for index = 0; index + 1 < path.length(); index = index + 1 {
    current = current.find_subspace(path[index], span)
  }
  (current, path[path.length() - 1])
}

///|
pub fn Namespace::find_type(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.TypeSymbol raise TheoryError {
  let (parent, name) = self.qualified_parent(path, span)
  match lookup_entry(parent.types, name) {
    Some(symbol) => symbol
    None => fail_theory(UnboundName, span, "unknown type name")
  }
}

///|
pub fn Namespace::find_logic(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.LSymbol raise TheoryError {
  let (parent, name) = self.qualified_parent(path, span)
  match lookup_entry(parent.logic, name) {
    Some(symbol) => symbol
    None => fail_theory(UnboundName, span, "unknown logic name")
  }
}

///|
pub fn Namespace::find_proposition(
  self : Namespace,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.PrSymbol raise TheoryError {
  let (parent, name) = self.qualified_parent(path, span)
  match lookup_entry(parent.propositions, name) {
    Some(symbol) => symbol
    None => fail_theory(UnboundName, span, "unknown proposition name")
  }
}

///|
fn[A : Eq] merge_entries(
  left : ArrayView[(Bytes, A)],
  right : ArrayView[(Bytes, A)],
  span : @identity.SourceSpan?,
) -> Array[(Bytes, A)] raise TheoryError {
  let result = left.to_owned()
  for entry in right {
    let (name, value) = entry
    guard lookup_entry(result, name) is Some(existing) else {
      result.push((name, value))
      continue
    }
    if existing != value {
      fail_theory(AmbiguousName, span, "import creates an ambiguous name")
    }
  }
  result.sort_by((left, right) => left.0.lexical_compare(right.0))
  result
}

///|
pub fn Namespace::merge(
  self : Namespace,
  imported : Namespace,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  let subspaces = self.subspaces.copy()
  for imported_entry in imported.subspaces {
    let (name, imported_space) = imported_entry
    match lookup_entry(subspaces, name) {
      None => subspaces.push((name, imported_space))
      Some(existing) => {
        let merged = existing.merge(imported_space, span)
        for index, entry in subspaces {
          if entry.0 == name {
            subspaces[index] = (name, merged)
            break
          }
        }
      }
    }
  }
  subspaces.sort_by((left, right) => left.0.lexical_compare(right.0))
  {
    types: merge_entries(self.types, imported.types, span),
    logic: merge_entries(self.logic, imported.logic, span),
    propositions: merge_entries(self.propositions, imported.propositions, span),
    subspaces,
  }
}

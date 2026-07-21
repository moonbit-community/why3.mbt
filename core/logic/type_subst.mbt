// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// An immutable substitution from semantic type-variable identities to
/// immutable semantic types. `order` preserves deterministic insertion order;
/// the map is used only for lookup.
struct TySubstitution {
  entries : Map[TyVarSymbol, Ty]
  order : Array[TyVarSymbol]
}

///|
pub fn TySubstitution::new() -> TySubstitution {
  { entries: Map([]), order: [] }
}

///|
pub fn TySubstitution::is_empty(self : TySubstitution) -> Bool {
  self.order.is_empty()
}

///|
pub fn TySubstitution::get(
  self : TySubstitution,
  variable : TyVarSymbol,
) -> Ty? {
  self.entries.get(variable)
}

///|
/// Returns a new substitution with one binding. Existing values and insertion
/// order are left untouched.
pub fn TySubstitution::bind(
  self : TySubstitution,
  variable : TyVarSymbol,
  replacement : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  if !variable.semantic_id().same_context(replacement.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "type substitution combines different compilation contexts",
    )
  }
  let entries = self.entries.copy()
  let order = self.order.copy()
  if !entries.contains(variable) {
    order.push(variable)
  }
  entries[variable] = replacement
  { entries, order }
}

///|
pub fn TySubstitution::bindings(
  self : TySubstitution,
) -> Array[(TyVarSymbol, Ty)] {
  [
    for variable in self.order => (variable, self.entries[variable])
  ]
}

///|
fn apply_substitution(substitution : TySubstitution, ty : Ty) -> Ty {
  match ty.node {
    VariableNode(variable) =>
      match substitution.entries.get(variable) {
        Some(replacement) => replacement
        None => ty
      }
    ApplicationNode(symbol, arguments) => {
      let mapped = [
        for argument in arguments => apply_substitution(substitution, argument)
      ]
      Ty::application_unchecked(symbol, mapped)
    }
  }
}

///|
/// Instantiates a type without introducing delayed variables or mutable links.
pub fn TySubstitution::apply(
  self : TySubstitution,
  ty : Ty,
  span : @identity.SourceSpan?,
) -> Ty raise TypeError {
  if !self.order.is_empty() {
    let first = self.order[0]
    if !first.semantic_id().same_context(ty.context_anchor()) {
      fail_type(
        ContextMismatch,
        span,
        "type substitution applied across compilation contexts",
      )
    }
  }
  apply_substitution(self, ty)
}

///|
/// Composes substitutions from left to right. The result satisfies
/// `self.then(after).apply(ty) == after.apply(self.apply(ty))`.
pub fn TySubstitution::then(
  self : TySubstitution,
  after : TySubstitution,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  let mut result = TySubstitution::new()
  for variable in self.order {
    result = result.bind(
      variable,
      after.apply(self.entries[variable], span),
      span,
    )
  }
  for variable in after.order {
    if !self.entries.contains(variable) {
      result = result.bind(variable, after.entries[variable], span)
    }
  }
  result
}

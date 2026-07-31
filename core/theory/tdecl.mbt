// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// A theory declaration node with its own semantic identity boundary. Why3
/// hash-conses this wrapper; MoonBit keeps the validated node immutable and
/// excludes runtime identity from canonical output.
struct TDecl {
  td_node : TheoryItem
}

///|
pub(all) struct TDeclView {
  td_node : TheoryItem
}

///|
pub fn TDecl::view(self : TDecl) -> TDeclView {
  { td_node: self.td_node }
}

///|
pub fn TDecl::declaration(declaration : @logic.Decl) -> TDecl {
  { td_node: TheoryDecl(declaration) }
}

///|
pub fn TDecl::use_(theory : Theory) -> TDecl {
  { td_node: TheoryUse(theory.key) }
}

///|
pub fn TDecl::clone(witness : CloneWitness) -> TDecl {
  { td_node: TheoryClone(witness) }
}

///|
pub fn TDecl::meta(meta : Meta) -> TDecl {
  { td_node: TheoryMeta(meta) }
}

///|
fn TDecl::from_item(item : TheoryItem) -> TDecl {
  { td_node: item }
}

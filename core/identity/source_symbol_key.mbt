// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// The semantic kind addressed by a context-free source locator.
pub(all) enum SourceSymbolKind {
  Type
  Logic
  Proposition
  Program
  Region
} derive(Eq, Debug)

///|
/// A context-free locator for one symbol in a pinned Why3 source theory.
/// Export and alias names are intentionally absent.
struct SourceSymbolKey {
  theory_key : Bytes
  theory_item_ordinal : UInt
  declaration_inner_ordinal : UInt
  symbol_kind : SourceSymbolKind
  symbol_digest : Bytes
} derive(Eq, Debug)

///|
/// Read-only projection used by driver profiles and canonical encoders.
pub(all) struct SourceSymbolKeyView {
  theory_key : Bytes
  theory_item_ordinal : UInt
  declaration_inner_ordinal : UInt
  symbol_kind : SourceSymbolKind
  symbol_digest : Bytes
} derive(Eq, Debug)

///|
pub fn SourceSymbolKey::new(
  theory_key : BytesView,
  theory_item_ordinal : UInt,
  declaration_inner_ordinal : UInt,
  symbol_kind : SourceSymbolKind,
  symbol_digest : BytesView,
) -> SourceSymbolKey {
  {
    theory_key: theory_key.to_owned(),
    theory_item_ordinal,
    declaration_inner_ordinal,
    symbol_kind,
    symbol_digest: symbol_digest.to_owned(),
  }
}

///|
pub fn SourceSymbolKey::view(self : SourceSymbolKey) -> SourceSymbolKeyView {
  {
    theory_key: self.theory_key,
    theory_item_ordinal: self.theory_item_ordinal,
    declaration_inner_ordinal: self.declaration_inner_ordinal,
    symbol_kind: self.symbol_kind,
    symbol_digest: self.symbol_digest,
  }
}

///|
pub fn SourceSymbolKind::canonical_name(self : SourceSymbolKind) -> BytesView {
  match self {
    Type => b"type"
    Logic => b"logic"
    Proposition => b"proposition"
    Program => b"program"
    Region => b"region"
  }
}

///|
fn SourceSymbolKind::hash_tag(self : SourceSymbolKind) -> Int {
  match self {
    Type => 0
    Logic => 1
    Proposition => 2
    Program => 3
    Region => 4
  }
}

///|
pub impl Hash for SourceSymbolKey with fn hash_combine(self, hasher) {
  hasher.combine(self.theory_key)
  hasher.combine(self.theory_item_ordinal)
  hasher.combine(self.declaration_inner_ordinal)
  hasher.combine(self.symbol_kind.hash_tag())
  hasher.combine(self.symbol_digest)
}

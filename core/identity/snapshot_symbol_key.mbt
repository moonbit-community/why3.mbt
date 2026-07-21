// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// The semantic kind addressed by a context-free snapshot key.
pub(all) enum SnapshotSymbolKind {
  Type
  Logic
  Proposition
  Program
  Region
} derive(Eq, Debug)

///|
/// A context-free key for one symbol in a frozen theory snapshot. Export and
/// alias names are intentionally absent.
struct SnapshotSymbolKey {
  theory_key : Bytes
  theory_item_ordinal : UInt
  declaration_inner_ordinal : UInt
  symbol_kind : SnapshotSymbolKind
  symbol_digest : Bytes
} derive(Eq, Debug)

///|
/// Read-only projection used by snapshot loaders and canonical encoders.
pub(all) struct SnapshotSymbolKeyView {
  theory_key : Bytes
  theory_item_ordinal : UInt
  declaration_inner_ordinal : UInt
  symbol_kind : SnapshotSymbolKind
  symbol_digest : Bytes
} derive(Eq, Debug)

///|
pub fn SnapshotSymbolKey::new(
  theory_key : BytesView,
  theory_item_ordinal : UInt,
  declaration_inner_ordinal : UInt,
  symbol_kind : SnapshotSymbolKind,
  symbol_digest : BytesView,
) -> SnapshotSymbolKey {
  {
    theory_key: theory_key.to_owned(),
    theory_item_ordinal,
    declaration_inner_ordinal,
    symbol_kind,
    symbol_digest: symbol_digest.to_owned(),
  }
}

///|
pub fn SnapshotSymbolKey::view(
  self : SnapshotSymbolKey,
) -> SnapshotSymbolKeyView {
  {
    theory_key: self.theory_key,
    theory_item_ordinal: self.theory_item_ordinal,
    declaration_inner_ordinal: self.declaration_inner_ordinal,
    symbol_kind: self.symbol_kind,
    symbol_digest: self.symbol_digest,
  }
}

///|
pub fn SnapshotSymbolKind::canonical_name(
  self : SnapshotSymbolKind,
) -> BytesView {
  match self {
    Type => b"type"
    Logic => b"logic"
    Proposition => b"proposition"
    Program => b"program"
    Region => b"region"
  }
}

///|
fn SnapshotSymbolKind::hash_tag(self : SnapshotSymbolKind) -> Int {
  match self {
    Type => 0
    Logic => 1
    Proposition => 2
    Program => 3
    Region => 4
  }
}

///|
pub impl Hash for SnapshotSymbolKey with fn hash_combine(self, hasher) {
  hasher.combine(self.theory_key)
  hasher.combine(self.theory_item_ordinal)
  hasher.combine(self.declaration_inner_ordinal)
  hasher.combine(self.symbol_kind.hash_tag())
  hasher.combine(self.symbol_digest)
}

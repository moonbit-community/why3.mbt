// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// Global semantic symbol classes with independent first-encounter counters.
pub(all) enum GlobalSymbolKind {
  Type
  Logic
  Program
  Region
  Proposition
}

///|
fn GlobalSymbolKind::tag(self : GlobalSymbolKind) -> Int {
  match self {
    Type => 0
    Logic => 1
    Program => 2
    Region => 3
    Proposition => 4
  }
}

///|
fn GlobalSymbolKind::canonical_name(self : GlobalSymbolKind) -> BytesView {
  match self {
    Type => b"type"
    Logic => b"logic"
    Program => b"program"
    Region => b"region"
    Proposition => b"proposition"
  }
}

///|
/// Mutable numbering state used by one canonical preorder traversal.
struct GlobalSymbolNumbering {
  entries : Map[(Int, @identity.SemanticId), UInt]
  next_indices : FixedArray[UInt]
}

///|
pub fn GlobalSymbolNumbering::new() -> GlobalSymbolNumbering {
  { entries: Map([]), next_indices: FixedArray::make(5, 0U) }
}

///|
pub fn GlobalSymbolNumbering::encounter(
  self : GlobalSymbolNumbering,
  kind : GlobalSymbolKind,
  id : @identity.SemanticId,
) -> UInt {
  let tag = kind.tag()
  let key = (tag, id)
  match self.entries.get(key) {
    Some(index) => index
    None => {
      let index = self.next_indices[tag]
      self.next_indices[tag] = index + 1U
      self.entries[key] = index
      index
    }
  }
}

///|
/// Encodes the frozen first-encounter cross-language event shape.
pub fn encode_symbol_events(
  events : ArrayView[(Bytes, GlobalSymbolKind, @identity.SemanticId, Bytes)],
) -> CanonicalJson {
  let numbering = GlobalSymbolNumbering::new()
  let encoded : Array[CanonicalValue] = []
  for entry in events {
    let (event, kind, id, name) = entry
    let index = numbering.encounter(kind, id)
    encoded.push(
      canonical_array([
        canonical_text(event),
        canonical_array([canonical_text(kind.canonical_name()), Unsigned(index)]),
        canonical_hex(name),
      ]),
    )
  }
  encode_canonical_value(
    canonical_array([canonical_text(b"events"), canonical_array(encoded)]),
  )
}

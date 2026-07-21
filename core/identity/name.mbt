// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// A deterministic set of semantic attributes represented by their original
/// bytes. The stored order is byte-lexicographic and duplicate-free.
struct SemanticAttributes {
  items : Array[Bytes]
} derive(Eq, Debug)

///|
pub fn SemanticAttributes::empty() -> SemanticAttributes {
  { items: [] }
}

///|
/// Copies, sorts, and deduplicates attributes without UTF-8 decoding.
pub fn SemanticAttributes::from_array(
  attributes : ArrayView[Bytes],
) -> SemanticAttributes {
  let sorted = attributes.to_owned()
  sorted.sort_by((left, right) => left.lexical_compare(right))
  let items : Array[Bytes] = []
  for attribute in sorted {
    if items.is_empty() || items[items.length() - 1] != attribute {
      items.push(attribute)
    }
  }
  { items, }
}

///|
pub fn SemanticAttributes::items(self : SemanticAttributes) -> ArrayView[Bytes] {
  self.items[:]
}

///|
pub fn SemanticAttributes::contains(
  self : SemanticAttributes,
  attribute : BytesView,
) -> Bool {
  self.items.any(item => item[:] == attribute)
}

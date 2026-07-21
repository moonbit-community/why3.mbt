// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct TheoryKey {
  path : Array[Bytes]
  name : Bytes
}

///|
pub(all) struct TheoryKeyView {
  path : ArrayView[Bytes]
  name : Bytes
}

///|
pub fn TheoryKey::new(
  path : ArrayView[Bytes],
  name : BytesView,
) -> TheoryKey raise TheoryError {
  if name.is_empty() || path.any(segment => segment.is_empty()) {
    fail_theory(
      InvalidQualifiedName,
      None,
      "theory path segments and name must be non-empty",
    )
  }
  { path: path.to_owned(), name: name.to_owned() }
}

///|
pub fn TheoryKey::view(self : TheoryKey) -> TheoryKeyView {
  { path: self.path[:], name: self.name }
}

///|
pub fn TheoryKey::segments(self : TheoryKey) -> Array[Bytes] {
  let result = self.path.copy()
  result.push(self.name)
  result
}

///|
pub impl Eq for TheoryKey with fn equal(self, other) {
  self.path == other.path && self.name == other.name
}

///|
pub impl Hash for TheoryKey with fn hash_combine(self, hasher) {
  hasher.combine(self.path.length())
  for segment in self.path {
    hasher.combine(segment)
  }
  hasher.combine(self.name)
}

///|
pub fn TheoryKey::lexical_compare(self : TheoryKey, other : TheoryKey) -> Int {
  let shared = self.path.length().min(other.path.length())
  for index = 0; index < shared; index = index + 1 {
    let order = self.path[index].lexical_compare(other.path[index])
    if order != 0 {
      return order
    }
  }
  if self.path.length() != other.path.length() {
    return self.path.length().compare(other.path.length())
  }
  self.name.lexical_compare(other.name)
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct SemanticName {
  name : Bytes
  attributes : @identity.SemanticAttributes
  source_span : @identity.SourceSpan?
}

///|
pub(all) struct SemanticNameView {
  name : Bytes
  attributes : ArrayView[Bytes]
  source_span : @identity.SourceSpan?
}

///|
pub fn SemanticName::new(
  name : BytesView,
  attributes : ArrayView[Bytes],
  source_span : @identity.SourceSpan?,
) -> SemanticName {
  {
    name: name.to_owned(),
    attributes: @identity.SemanticAttributes::from_array(attributes),
    source_span,
  }
}

///|
pub fn SemanticName::view(self : SemanticName) -> SemanticNameView {
  {
    name: self.name,
    attributes: self.attributes.items(),
    source_span: self.source_span,
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_attributes(attributes : ArrayView[Bytes]) -> CanonicalValue {
  let sorted = attributes.to_owned()
  sorted.sort_by((left, right) => left.lexical_compare(right))
  canonical_array([ for attribute in sorted => canonical_hex(attribute) ])
}

///|
fn canonical_source_span(span : @identity.SourceSpan) -> CanonicalValue {
  let view = span.view()
  canonical_array([
    canonical_text(b"SourceSpan"),
    canonical_hex(view.relative_path),
    Signed(view.start_byte.to_int64()),
    Signed(view.end_byte.to_int64()),
    Signed(view.start_line),
    Signed(view.start_column),
    Signed(view.end_line),
    Signed(view.end_column),
  ])
}

///|
fn canonical_source_span_option(span : @identity.SourceSpan?) -> CanonicalValue {
  match span {
    None => canonical_array([canonical_text(b"none")])
    Some(value) =>
      canonical_array([canonical_text(b"some"), canonical_source_span(value)])
  }
}

///|
fn canonical_snapshot_symbol_key_value(
  key : @identity.SnapshotSymbolKey,
) -> CanonicalValue {
  let view = key.view()
  canonical_array([
    canonical_text(b"SnapshotSymbolKey"),
    canonical_hex(view.theory_key),
    Unsigned(view.theory_item_ordinal),
    Unsigned(view.declaration_inner_ordinal),
    canonical_text(view.symbol_kind.canonical_name()),
    canonical_hex(view.symbol_digest),
  ])
}

///|
pub fn encode_snapshot_symbol_key(
  key : @identity.SnapshotSymbolKey,
) -> CanonicalJson {
  encode_canonical_value(canonical_snapshot_symbol_key_value(key))
}

///|
/// Encodes identity provenance without context tokens or runtime identities.
fn canonical_origin(origin : @identity.Origin) -> CanonicalValue {
  match origin.view() {
    UserOrigin(name, span, attributes) =>
      canonical_array([
        canonical_text(b"Origin.User"),
        canonical_hex(name),
        canonical_source_span_option(span),
        canonical_attributes(attributes),
      ])
    SnapshotOrigin(name, key, attributes) =>
      canonical_array([
        canonical_text(b"Origin.Snapshot"),
        canonical_hex(name),
        canonical_snapshot_symbol_key_value(key),
        canonical_attributes(attributes),
      ])
    GeneratedOrigin(stage, name, span, attributes) =>
      canonical_array([
        canonical_text(b"Origin.Generated"),
        canonical_text(stage.canonical_name()),
        canonical_hex(name),
        canonical_source_span_option(span),
        canonical_attributes(attributes),
      ])
  }
}

///|
pub fn encode_origin(origin : @identity.Origin) -> CanonicalJson {
  encode_canonical_value(canonical_origin(origin))
}

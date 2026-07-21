// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn source_span(span : @parser.Span) -> @identity.SourceSpan {
  @identity.SourceSpan::new(
    span.start.filename,
    span.start.byte_offset,
    span.end.byte_offset,
    span.start.line,
    span.start.column,
    span.end.line,
    span.end.column,
  )
}

///|
fn attribute_is_prefix(attribute : BytesView, prefix : BytesView) -> Bool {
  attribute.length() >= prefix.length() && attribute[:prefix.length()] == prefix
}

///|
fn is_control_attribute(attribute : BytesView) -> Bool {
  attribute_is_prefix(attribute, b"vc:") ||
  attribute_is_prefix(attribute, b"encoding:") ||
  attribute_is_prefix(attribute, b"algebraic:") ||
  attribute_is_prefix(attribute, b"remove_unused:") ||
  attribute == b"select_alginst_default" ||
  attribute == b"eliminate_algebraic" ||
  attribute == b"get_counterexmp" ||
  attribute == b"stop_split"
}

///|
fn checked_text_attribute(
  attribute : BytesView,
  span : @identity.SourceSpan?,
) -> Bytes raise ElabError {
  if is_control_attribute(attribute) {
    fail_unsupported(
      ControlAttribute,
      FeatureClassification,
      span,
      "user control attribute is outside the frozen allowlist",
    )
  }
  attribute.to_owned()
}

///|
fn ident_parts(
  ident : @parser.Ident,
) -> (@identity.SourceSpan, Array[Bytes]) raise ElabError {
  let mut location = source_span(ident.span)
  let attributes : Array[Bytes] = []
  for attribute in ident.attributes {
    match attribute {
      Text(text) =>
        attributes.push(checked_text_attribute(text, Some(location)))
      Position(position) => location = source_span(position)
    }
  }
  (location, attributes)
}

///|
fn user_origin(ident : @parser.Ident) -> @identity.Origin raise ElabError {
  let (span, attributes) = ident_parts(ident)
  @identity.Origin::user(ident.name, Some(span), attributes)
}

///|
fn semantic_name(ident : @parser.Ident) -> @theory.SemanticName raise ElabError {
  let (span, attributes) = ident_parts(ident)
  @theory.SemanticName::new(ident.name, attributes, Some(span))
}

///|
fn qualid_segments(qualid : @parser.QualId) -> Array[Bytes] {
  match qualid {
    Qident(ident) => [ident.name]
    Qdot(parent, ident) => {
      let result = qualid_segments(parent)
      result.push(ident.name)
      result
    }
  }
}

///|
fn qualid_span(qualid : @parser.QualId) -> @identity.SourceSpan {
  match qualid {
    Qident(ident) => source_span(ident.span)
    Qdot(parent, ident) => {
      let first = qualid_span(parent).view()
      let last = source_span(ident.span).view()
      @identity.SourceSpan::new(
        first.relative_path,
        first.start_byte,
        last.end_byte,
        first.start_line,
        first.start_column,
        last.end_line,
        last.end_column,
      )
    }
  }
}

///|
fn qualid_last(qualid : @parser.QualId) -> @parser.Ident {
  match qualid {
    Qident(ident) | Qdot(_, ident) => ident
  }
}

///|
fn theory_key_of_qualid(
  qualid : @parser.QualId,
) -> @theory.TheoryKey raise @theory.TheoryError {
  let segments = qualid_segments(qualid)
  @theory.TheoryKey::new(
    segments[:segments.length() - 1],
    segments[segments.length() - 1],
  )
}

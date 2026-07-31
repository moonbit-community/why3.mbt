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
fn checked_text_attribute(
  attribute : BytesView,
  span : @identity.SourceSpan?,
) -> Bytes {
  ignore(span)
  attribute.to_owned()
}

///|
fn ident_parts(ident : @parser.Ident) -> (@identity.SourceSpan, Array[Bytes]) {
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
fn user_origin(ident : @parser.Ident) -> @identity.Origin {
  let (span, attributes) = ident_parts(ident)
  @identity.Origin::user(ident.name, Some(span), attributes)
}

///|
fn user_origin_with_attributes(
  ident : @parser.Ident,
  added : ArrayView[Bytes],
) -> @identity.Origin {
  let (span, attributes) = ident_parts(ident)
  for attribute in added {
    attributes.push(attribute)
  }
  @identity.Origin::user(ident.name, Some(span), attributes)
}

///|
fn semantic_name(ident : @parser.Ident) -> @theory.SemanticName {
  let (span, attributes) = ident_parts(ident)
  let view = span.view()
  let source_span = if view.relative_path.is_empty() &&
    view.start_byte == 0 &&
    view.end_byte == 0 &&
    view.start_line == 1L &&
    view.start_column == 0L &&
    view.end_line == 1L &&
    view.end_column == 0L {
    None
  } else {
    Some(span)
  }
  @theory.SemanticName::new(ident.name, attributes, source_span)
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

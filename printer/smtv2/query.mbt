// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct SmtV26Query {
  anchor : @identity.SemanticId
  preludes : Array[Bytes]
}

///|
pub fn SmtV26Query::new(
  anchor : @identity.SemanticId,
  preludes : ArrayView[Bytes],
) -> SmtV26Query {
  { anchor, preludes: preludes.to_owned() }
}

///|
pub fn SmtV26Query::context_anchor(self : SmtV26Query) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn SmtV26Query::preludes(self : SmtV26Query) -> ArrayView[Bytes] {
  self.preludes[:]
}

///|
pub(all) struct PrintedIdentifier {
  start : Int
  end : Int
  semantic_id : @identity.SemanticId
  origin : @identity.Origin
}

///|
struct SmtQuery {
  bytes : Bytes
  identifiers : Array[PrintedIdentifier]
}

///|
pub fn SmtQuery::bytes(self : SmtQuery) -> BytesView {
  self.bytes[:]
}

///|
pub fn SmtQuery::identifiers(self : SmtQuery) -> ArrayView[PrintedIdentifier] {
  self.identifiers[:]
}

///|
priv struct QueryWriter {
  buffer : Buffer
  identifiers : Array[PrintedIdentifier]
}

///|
fn QueryWriter::new() -> QueryWriter {
  { buffer: Buffer(), identifiers: [] }
}

///|
fn QueryWriter::write(self : QueryWriter, bytes : BytesView) -> Unit {
  self.buffer.write_bytes(bytes)
}

///|
fn QueryWriter::write_string_utf8(
  self : QueryWriter,
  text : StringView,
) -> Unit {
  self.buffer.write_string_utf8(text)
}

///|
fn QueryWriter::identifier(
  self : QueryWriter,
  bytes : BytesView,
  semantic_id : @identity.SemanticId,
  origin : @identity.Origin,
) -> Unit {
  let start = self.buffer.length()
  self.buffer.write_bytes(bytes)
  self.identifiers.push({
    start,
    end: self.buffer.length(),
    semantic_id,
    origin,
  })
}

///|
fn QueryWriter::finish(self : QueryWriter) -> SmtQuery {
  if self.buffer.is_empty() ||
    self.buffer.view()[self.buffer.length() - 1] != b'\n' {
    self.buffer.write_byte(b'\n')
  }
  { bytes: self.buffer.to_bytes(), identifiers: self.identifiers }
}

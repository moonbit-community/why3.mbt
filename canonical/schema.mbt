// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// The frozen portable canonical semantic schema version.
pub fn canonical_schema_version() -> Int {
  2
}

///|
/// Exact compact JSON bytes for one canonical value. Every instance ends in
/// exactly one LF and is therefore ready to hash.
struct CanonicalJson {
  encoded : Bytes
} derive(Eq, Debug)

///|
pub fn CanonicalJson::bytes(self : CanonicalJson) -> BytesView {
  self.encoded[:]
}

///|
pub fn CanonicalJson::sha256(self : CanonicalJson) -> Bytes {
  sha256(self.encoded)
}

///|
pub fn CanonicalJson::sha256_hex(self : CanonicalJson) -> Bytes {
  sha256_hex(self.encoded)
}

///|
priv enum CanonicalValue {
  Text(Bytes)
  Hex(Bytes)
  Boolean(Bool)
  Signed(Int64)
  Unsigned(UInt)
  Decimal(BigInt)
  Array(Array[CanonicalValue])
}

///|
fn canonical_text(text : BytesView) -> CanonicalValue {
  Text(text.to_owned())
}

///|
fn canonical_hex(bytes : BytesView) -> CanonicalValue {
  Hex(bytes.to_owned())
}

///|
fn canonical_bool(value : Bool) -> CanonicalValue {
  Boolean(value)
}

///|
fn canonical_array(values : Array[CanonicalValue]) -> CanonicalValue {
  Array(values)
}

///|
fn write_json_string(buffer : @buffer.Buffer, text : BytesView) -> Unit {
  buffer.write_byte(b'"')
  for byte in text {
    match byte {
      b'"' => buffer.write_bytes(b"\\\"")
      b'\\' => buffer.write_bytes(b"\\\\")
      b'\x08' => buffer.write_bytes(b"\\b")
      b'\x0c' => buffer.write_bytes(b"\\f")
      b'\n' => buffer.write_bytes(b"\\n")
      b'\r' => buffer.write_bytes(b"\\r")
      b'\t' => buffer.write_bytes(b"\\t")
      b'\x00'..=b'\x1f' => {
        let value = byte.to_int()
        buffer.write_bytes(b"\\u00")
        buffer.write_byte(lowercase_hex_digits[value >> 4])
        buffer.write_byte(lowercase_hex_digits[value & 0x0f])
      }
      b'\x20'..=b'\x7e' => buffer.write_byte(byte)
      b'\x7f' => buffer.write_bytes(b"\\u007f")
      _ =>
        abort(
          "canonical JSON text must already be UTF-8; semantic Bytes use Hex",
        )
    }
  }
  buffer.write_byte(b'"')
}

///|
fn CanonicalValue::write_json(
  self : CanonicalValue,
  buffer : @buffer.Buffer,
) -> Unit {
  match self {
    Text(text) => write_json_string(buffer, text)
    Hex(bytes) => write_json_string(buffer, bytes_to_lower_hex(bytes))
    Boolean(value) => buffer.write_bytes(if value { b"true" } else { b"false" })
    Signed(value) => buffer.write_string_utf8(value.to_string())
    Unsigned(value) => buffer.write_string_utf8(value.to_string())
    Decimal(value) => buffer.write_string_utf8(value.to_string())
    Array(values) => {
      buffer.write_byte(b'[')
      for index, value in values {
        if index > 0 {
          buffer.write_byte(b',')
        }
        value.write_json(buffer)
      }
      buffer.write_byte(b']')
    }
  }
}

///|
/// Canonical semantic-map representation. The input order is ignored; keys
/// and then values are compared by their compact canonical JSON bytes.
fn canonical_semantic_map(
  entries : Array[(CanonicalValue, CanonicalValue)],
) -> CanonicalValue {
  let sortable = [
    for entry in entries => {
      (
        encode_canonical_value_without_lf(entry.0),
        encode_canonical_value_without_lf(entry.1),
        entry.0,
        entry.1,
      )
    }
  ]
  sortable.sort_by((left, right) => {
    let key_order = left.0.lexical_compare(right.0)
    if key_order != 0 {
      key_order
    } else {
      left.1.lexical_compare(right.1)
    }
  })
  canonical_array(
    [
      for entry in sortable => canonical_array([entry.2, entry.3])
    ],
  )
}

///|
fn encode_canonical_value(value : CanonicalValue) -> CanonicalJson {
  let buffer = @buffer.Buffer()
  value.write_json(buffer)
  buffer.write_byte(b'\n')
  { encoded: buffer.to_bytes() }
}

///|
fn encode_canonical_value_without_lf(value : CanonicalValue) -> Bytes {
  let buffer = @buffer.Buffer()
  value.write_json(buffer)
  buffer.to_bytes()
}

///|
/// Canonical base representation for semantic bytes.
pub fn encode_bytes(bytes : BytesView) -> CanonicalJson {
  encode_canonical_value(
    canonical_array([canonical_text(b"bytes"), canonical_hex(bytes)]),
  )
}

///|
/// Canonical explicit sentinel for an absent optional value.
pub fn encode_none() -> CanonicalJson {
  encode_canonical_value(canonical_array([canonical_text(b"none")]))
}

///|
/// Canonical optional wrapper specialized to the base Bytes node.
pub fn encode_some_bytes(bytes : BytesView) -> CanonicalJson {
  encode_canonical_value(
    canonical_array([
      canonical_text(b"some"),
      canonical_array([canonical_text(b"bytes"), canonical_hex(bytes)]),
    ]),
  )
}

///|
/// Canonical base encoder for a semantic map with byte keys and trusted JSON
/// text values. Entries are sorted by canonical byte key, then value.
pub fn encode_bytes_text_map(
  entries : ArrayView[(Bytes, Bytes)],
) -> CanonicalJson {
  let sorted = entries.to_owned()
  sorted.sort_by((left, right) => {
    let key_order = left.0.lexical_compare(right.0)
    if key_order != 0 {
      key_order
    } else {
      encode_canonical_value_without_lf(canonical_text(left.1)).lexical_compare(
        encode_canonical_value_without_lf(canonical_text(right.1)),
      )
    }
  })
  let encoded_entries : Array[CanonicalValue] = []
  for entry in sorted {
    let (key, value) = entry
    encoded_entries.push(
      canonical_array([canonical_hex(key), canonical_text(value)]),
    )
  }
  encode_canonical_value(
    canonical_array([canonical_text(b"map"), canonical_array(encoded_entries)]),
  )
}

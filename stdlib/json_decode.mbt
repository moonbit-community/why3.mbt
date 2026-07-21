// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn json_object(
  value : Json,
  path : String,
) -> Map[String, Json] raise SnapshotError {
  match value {
    Object(fields) => fields
    _ => fail_snapshot(MalformedSnapshot, path, "expected a JSON object")
  }
}

///|
fn json_array(value : Json, path : String) -> Array[Json] raise SnapshotError {
  match value {
    Array(values) => values
    _ => fail_snapshot(MalformedSnapshot, path, "expected a JSON array")
  }
}

///|
fn json_string(value : Json, path : String) -> String raise SnapshotError {
  match value {
    String(text) => text
    _ => fail_snapshot(MalformedSnapshot, path, "expected a JSON string")
  }
}

///|
fn json_bool(value : Json, path : String) -> Bool raise SnapshotError {
  match value {
    True => true
    False => false
    _ => fail_snapshot(MalformedSnapshot, path, "expected a JSON boolean")
  }
}

///|
fn json_int(value : Json, path : String) -> Int raise SnapshotError {
  match value {
    Number(number, ..) => {
      let integer = number.to_int()
      if integer.to_double() != number {
        fail_snapshot(
          MalformedSnapshot,
          path,
          "expected an integral JSON number",
        )
      }
      integer
    }
    _ => fail_snapshot(MalformedSnapshot, path, "expected a JSON number")
  }
}

///|
fn json_uint(value : Json, path : String) -> UInt raise SnapshotError {
  let integer = json_int(value, path)
  if integer < 0 {
    fail_snapshot(MalformedSnapshot, path, "expected a non-negative integer")
  }
  integer.reinterpret_as_uint()
}

///|
fn json_field(
  object : Map[String, Json],
  name : String,
  path : String,
) -> Json raise SnapshotError {
  match object.get(name) {
    Some(value) => value
    None => fail_snapshot(MalformedSnapshot, path, "missing field " + name)
  }
}

///|
fn json_expect_empty(value : Json, path : String) -> Unit raise SnapshotError {
  if !json_array(value, path).is_empty() {
    fail_snapshot(
      UnsupportedSnapshotVariant,
      path,
      "snapshot field must be empty in the frozen closure",
    )
  }
}

///|
fn tagged(
  value : Json,
  path : String,
) -> (String, Array[Json]) raise SnapshotError {
  let fields = json_array(value, path)
  if fields.is_empty() {
    fail_snapshot(MalformedSnapshot, path, "tagged array is empty")
  }
  (json_string(fields[0], path + "[0]"), fields)
}

///|
fn require_tag_arity(
  fields : ArrayView[Json],
  arity : Int,
  path : String,
) -> Unit raise SnapshotError {
  if fields.length() != arity + 1 {
    fail_snapshot(MalformedSnapshot, path, "tagged array has the wrong arity")
  }
}

///|
fn hex_nibble(byte : Byte, path : String) -> Byte raise SnapshotError {
  let code = byte.to_int()
  if code >= b'0'.to_int() && code <= b'9'.to_int() {
    (code - b'0'.to_int()).to_byte()
  } else if code >= b'a'.to_int() && code <= b'f'.to_int() {
    (10 + code - b'a'.to_int()).to_byte()
  } else {
    fail_snapshot(MalformedSnapshot, path, "invalid lowercase hexadecimal text")
  }
}

///|
fn decode_hex(text : String, path : String) -> Bytes raise SnapshotError {
  let encoded = @utf8.encode(text)
  if encoded.length() % 2 != 0 {
    fail_snapshot(MalformedSnapshot, path, "hexadecimal text has odd length")
  }
  let result : Array[Byte] = []
  for index = 0; index < encoded.length() / 2; index = index + 1 {
    let high = hex_nibble(encoded[index * 2], path).to_int()
    let low = hex_nibble(encoded[index * 2 + 1], path).to_int()
    result.push((high * 16 + low).to_byte())
  }
  Bytes::from_array(result)
}

///|
fn bytes_from_json_hex(
  value : Json,
  path : String,
) -> Bytes raise SnapshotError {
  decode_hex(json_string(value, path), path)
}

///|
fn string_bytes(text : String) -> Bytes {
  @utf8.encode(text)
}

///|
fn source_span(
  value : Json,
  path : String,
) -> @identity.SourceSpan? raise SnapshotError {
  match value {
    Null => None
    _ => {
      let object = json_object(value, path)
      Some(
        @identity.SourceSpan::new(
          bytes_from_json_hex(
            json_field(object, "relativePathHex", path),
            path + ".relativePathHex",
          ),
          json_int(json_field(object, "startByte", path), path + ".startByte"),
          json_int(json_field(object, "endByte", path), path + ".endByte"),
          json_int(json_field(object, "startLine", path), path + ".startLine").to_int64(),
          json_int(
            json_field(object, "startColumn", path),
            path + ".startColumn",
          ).to_int64(),
          json_int(json_field(object, "endLine", path), path + ".endLine").to_int64(),
          json_int(json_field(object, "endColumn", path), path + ".endColumn").to_int64(),
        ),
      )
    }
  }
}

///|
fn byte_attributes(
  value : Json,
  path : String,
) -> Array[Bytes] raise SnapshotError {
  let result : Array[Bytes] = []
  for index, entry in json_array(value, path) {
    result.push(
      bytes_from_json_hex(entry, path + "[" + index.to_string() + "]"),
    )
  }
  result
}

///|
fn semantic_name(
  value : Json,
  path : String,
) -> @theory.SemanticName raise SnapshotError {
  let object = json_object(value, path)
  @theory.SemanticName::new(
    bytes_from_json_hex(json_field(object, "nameHex", path), path + ".nameHex"),
    byte_attributes(
      json_field(object, "attributes", path),
      path + ".attributes",
    ),
    source_span(json_field(object, "sourceSpan", path), path + ".sourceSpan"),
  )
}

///|
fn origin_from_name(
  name : @theory.SemanticName,
  key : @identity.SnapshotSymbolKey,
) -> @identity.Origin {
  let view = name.view()
  @identity.Origin::snapshot_with_span(
    view.name,
    key,
    view.source_span,
    view.attributes,
  )
}

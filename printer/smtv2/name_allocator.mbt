// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn encoded_identifier_head(byte : Byte) -> BytesView {
  match byte {
    b'a'..=b'z' | b'A'..=b'Z' => Bytes::from_array([byte])[:]
    b' ' => b"sp"
    b'_' => b"us"
    b'#' => b"sh"
    b'`' => b"bq"
    b'~' => b"tl"
    b'!' => b"ex"
    b'@' => b"at"
    b'$' => b"dl"
    b'%' => b"pc"
    b'^' => b"cf"
    b'&' => b"et"
    b'*' => b"as"
    b'(' => b"lp"
    b')' => b"rp"
    b'-' => b"mn"
    b'+' => b"pl"
    b'=' => b"eq"
    b'[' => b"lb"
    b']' => b"rb"
    b'{' => b"lc"
    b'}' => b"rc"
    b':' => b"cl"
    b'\'' => b"qt"
    b'"' => b"dq"
    b'<' => b"ls"
    b'>' => b"gt"
    b'/' => b"sl"
    b'?' => b"qu"
    b'\\' => b"bs"
    b'|' => b"br"
    b';' => b"sc"
    b',' => b"cm"
    b'.' => b"dt"
    b'0' => b"zr"
    b'1' => b"un"
    b'2' => b"du"
    b'3' => b"tr"
    b'4' => b"qr"
    b'5' => b"qn"
    b'6' => b"sx"
    b'7' => b"st"
    b'8' => b"oc"
    b'9' => b"nn"
    b'\n' => b"nl"
    _ => b"zz"
  }
}

///|
fn encoded_identifier_rest(byte : Byte) -> BytesView {
  match byte {
    b'0'..=b'9' => Bytes::from_array([byte])[:]
    b'_' | b' ' => b"_"
    _ => encoded_identifier_head(byte)
  }
}

///|
fn sanitize_identifier(name : BytesView) -> Bytes {
  if name.is_empty() {
    return b"zilch"
  }
  let output = @buffer.Buffer(size_hint=name.length())
  for index, byte in name {
    output.write_bytes(
      if index == 0 {
        encoded_identifier_head(byte)
      } else {
        encoded_identifier_rest(byte)
      },
    )
  }
  output.to_bytes()
}

///|
priv struct NameAllocator {
  indices : Map[Bytes, Int]
  values : Map[@identity.SemanticId, Bytes]
}

///|
fn suffixed_name(name : BytesView, index : Int) -> Bytes {
  if index <= 0 {
    return name.to_owned()
  }
  let output = @buffer.Buffer(size_hint=name.length() + 8)
  output.write_bytes(name)
  output.write_string_utf8(index.to_string())
  output.to_bytes()
}

///|
fn NameAllocator::find_unique(self : NameAllocator, name : Bytes) -> Bytes {
  guard self.indices.get(name) is Some(previous) else {
    let result = name
    self.indices[result] = 0
    return result
  }
  let mut index = previous + 1
  while self.indices.contains(suffixed_name(name, index)) {
    index = index + 1
  }
  while index != 1 && !self.indices.contains(suffixed_name(name, index - 1)) {
    index = index - 1
  }
  self.indices[name] = index
  let result = suffixed_name(name, index)
  self.indices[result] = 0
  result
}

///|
fn NameAllocator::new() -> NameAllocator {
  let self = { indices: Map([]), values: Map([]) }
  for reserved in smt_reserved_identifiers() {
    ignore(self.find_unique(reserved))
  }
  self
}

///|
fn NameAllocator::unique(
  self : NameAllocator,
  id : @identity.SemanticId,
  name : BytesView,
) -> Bytes {
  match self.values.get(id) {
    Some(value) => value
    None => {
      let value = self.find_unique(sanitize_identifier(name))
      self.values[id] = value
      value
    }
  }
}

///|
fn NameAllocator::forget(
  self : NameAllocator,
  id : @identity.SemanticId,
) -> Unit {
  guard self.values.get(id) is Some(name) else { return }
  self.indices.remove(name)
  self.values.remove(id)
}

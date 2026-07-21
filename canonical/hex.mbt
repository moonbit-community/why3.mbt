// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
let lowercase_hex_digits : Bytes = b"0123456789abcdef"

///|
/// Encodes arbitrary bytes as lowercase hexadecimal without a prefix.
pub fn bytes_to_lower_hex(bytes : BytesView) -> Bytes {
  let output = @buffer.Buffer(size_hint=bytes.length() * 2)
  for byte in bytes {
    let value = byte.to_int()
    output.write_byte(lowercase_hex_digits[value >> 4])
    output.write_byte(lowercase_hex_digits[value & 0x0f])
  }
  output.to_bytes()
}

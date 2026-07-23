// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_smt_token_stream(
  stream : @smtv2.NormalizedSmtTokens,
) -> CanonicalValue {
  canonical_array([
    canonical_text(b"SmtTokenStreamV1"),
    canonical_array([ for token in stream.tokens() => canonical_hex(token) ]),
  ])
}

///|
pub fn encode_smt_token_stream(
  stream : @smtv2.NormalizedSmtTokens,
) -> CanonicalJson {
  encode_canonical_value(canonical_smt_token_stream(stream))
}

///|
/// Encodes the normalized SMT-LIB token stream for one prepared goal.
pub fn encode_smt_token_record(
  fixture : BytesView,
  source : BytesView,
  unit_name : BytesView,
  goal_name : BytesView,
  goal_ordinal : Int,
  stream : @smtv2.NormalizedSmtTokens,
) -> Bytes {
  if goal_ordinal < 0 {
    abort("goal ordinal cannot be negative")
  }
  let buffer = start_portable_record(
    fixture, source, b"goal", b"theory", unit_name,
  )
  write_record_hex_field(buffer, b"goal_name_hex", goal_name)
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"goal_ordinal")
  buffer.write_string_utf8(goal_ordinal.to_string())
  write_record_text_field(buffer, b"stage", b"smt-token-stream", false)
  write_canonical_field(buffer, encode_smt_token_stream(stream))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}

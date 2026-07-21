// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "semantic map sorts by canonical byte key" {
  let encoded = encode_bytes_text_map([
    (b"b", b"b"),
    (b"aa", b"aa"),
    (b"\x00", b"zero"),
    (b"a", b"a"),
  ])
  assert_eq(
    encoded.bytes(),
    b"[\"map\",[[\"00\",\"zero\"],[\"61\",\"a\"],[\"6161\",\"aa\"],[\"62\",\"b\"]]]\n",
  )
  assert_eq(
    encoded.sha256_hex(),
    b"77061378829763596e121882302a8a2071663f0a24450bee1c7006cb3495b0fe",
  )
}

///|
test "global symbols number at first preorder encounter" {
  let context = @identity.CompilationContext::new()
  let symbol_a = context.fresh_id()
  let symbol_b = context.fresh_id()
  let encoded = encode_symbol_events([
    (b"reference", Logic, symbol_a, b"x"),
    (b"declaration", Logic, symbol_a, b"x"),
    (b"declaration", Logic, symbol_b, b"x"),
  ])
  assert_eq(
    encoded.bytes(),
    b"[\"events\",[[\"reference\",[\"logic\",0],\"78\"],[\"declaration\",[\"logic\",0],\"78\"],[\"declaration\",[\"logic\",1],\"78\"]]]\n",
  )
  assert_eq(
    encoded.sha256_hex(),
    b"da2b3f17e1e491486d984e354cfd79352477e3eb4d503693d531d29562ab0a14",
  )
}

///|
test "equal local ids from different contexts receive distinct canonical ids" {
  let first = @identity.CompilationContext::new().fresh_id()
  let second = @identity.CompilationContext::new().fresh_id()
  assert_eq(first.local_id(), second.local_id())
  let numbering = GlobalSymbolNumbering::new()
  assert_eq(numbering.encounter(Logic, first), 0U)
  assert_eq(numbering.encounter(Logic, first), 0U)
  assert_eq(numbering.encounter(Logic, second), 1U)
  assert_eq(numbering.encounter(Type, first), 0U)
}

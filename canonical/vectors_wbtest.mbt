// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "semantic map utility sorts by canonical byte key" {
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
}

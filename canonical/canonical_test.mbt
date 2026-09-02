// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "canonical schema is v3" {
  assert_eq(@canonical.canonical_schema_version(), 3)
}

///|
test "SHA-256 standard vectors" {
  assert_eq(
    @canonical.sha256_hex(b""),
    b"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  )
  assert_eq(
    @canonical.sha256_hex(b"abc"),
    b"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
  )
  assert_eq(
    @canonical.sha256_hex(
      b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    ),
    b"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
  )
}

///|
test "canonical bytes remain lossless" {
  let encoded = @canonical.encode_bytes([0x00, 0xc3, 0xa9, 0xff])
  assert_eq(encoded.bytes(), b"[\"bytes\",\"00c3a9ff\"]\n")
  assert_eq(
    encoded.sha256_hex(),
    b"9375766da1df1db79ae9d71bfd0be4d65cdb9a37fa406f6cc3499c5decc85d89",
  )
}

///|
test "v3 type symbols retain source locations" {
  let without_span = @logic.TypeSymbol::new_abstract(
    @identity.CompilationContext::new(),
    b"t",
    @identity.Origin::user(b"t", None, []),
    [],
    None,
  )
  let span = @identity.SourceSpan::new(b"demo.mlw", 1, 2, 1L, 1L, 1L, 2L)
  let with_span = @logic.TypeSymbol::new_abstract(
    @identity.CompilationContext::new(),
    b"t",
    @identity.Origin::user(b"t", Some(span), []),
    [],
    None,
  )
  let plain = @canonical.encode_type_symbol(without_span)
  let localized = @canonical.encode_type_symbol(with_span)
  assert_eq(plain.bytes()[:10], b"[\"GraphV3\"")
  assert_true(plain.bytes() != localized.bytes())
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

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
  assert_eq(
    @canonical.sha256_hex(
      b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" +
      b"hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
    ),
    b"cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
  )
}

///|
test "canonical Bytes and option vectors are byte exact" {
  let bytes = @canonical.encode_bytes([0x00, 0xc3, 0xa9, 0xff])
  assert_eq(bytes.bytes(), b"[\"bytes\",\"00c3a9ff\"]\n")
  assert_eq(
    bytes.sha256_hex(),
    b"9375766da1df1db79ae9d71bfd0be4d65cdb9a37fa406f6cc3499c5decc85d89",
  )
  assert_eq(@canonical.encode_none().bytes(), b"[\"none\"]\n")
  assert_eq(
    @canonical.encode_none().sha256_hex(),
    b"58ff281c738cce6bed1f900a49106507450f36beb15857f836836a24589a316f",
  )
  assert_eq(
    @canonical.encode_some_bytes(b"A").bytes(),
    b"[\"some\",[\"bytes\",\"41\"]]\n",
  )
  assert_eq(
    @canonical.encode_some_bytes(b"A").sha256_hex(),
    b"f956418260de4db8ddbf2b167385b212f3e18b62aa1204e3a4500e33fdb3641a",
  )
}

///|
test "generated origin matches the frozen cross-language vector" {
  let context = @identity.CompilationContext::new()
  ignore(context.fresh_id())
  let origin = @identity.Origin::generated(Wp, b"vc", None, [])
  let encoded = @canonical.encode_origin(origin)
  assert_eq(
    encoded.bytes(),
    b"[\"Origin.Generated\",\"wp\",\"7663\",[\"none\"],[]]\n",
  )
  assert_eq(
    encoded.sha256_hex(),
    b"3991f38c6ebf1a1f761cf2ec902730425b984777681e6375753886a3167482ab",
  )
}

///|
test "non-ASCII names remain bytes and never change source offsets" {
  let span = @identity.SourceSpan::new(
    b"fixtures/\xff.mlw", 9, 13, 2L, 4L, 2L, 8L,
  )
  let origin = @identity.Origin::user(b"\xe4\xb8\xad", Some(span), [b"z", b"a"])
  assert_eq(
    @canonical.encode_origin(origin).bytes(),
    b"[\"Origin.User\",\"e4b8ad\",[\"some\",[\"SourceSpan\",\"66697874757265732fff2e6d6c77\",9,13,2,4,2,8]],[\"61\",\"7a\"]]\n",
  )
}

///|
test "snapshot keys have a context-free canonical form" {
  let key = @identity.SnapshotSymbolKey::new(
    b"int.Int",
    7U,
    2U,
    Logic,
    Bytes::make(32, b'\x11'),
  )
  assert_eq(
    @canonical.encode_snapshot_symbol_key(key).bytes(),
    b"[\"SnapshotSymbolKey\",\"696e742e496e74\",7,2,\"logic\",\"1111111111111111111111111111111111111111111111111111111111111111\"]\n",
  )
  let origin = @identity.Origin::snapshot(b"alias", key, [b"z", b"a"])
  assert_eq(
    @canonical.encode_origin(origin).bytes(),
    b"[\"Origin.Snapshot\",\"616c696173\",[\"SnapshotSymbolKey\",\"696e742e496e74\",7,2,\"logic\",\"1111111111111111111111111111111111111111111111111111111111111111\"],[\"61\",\"7a\"]]\n",
  )
}

///|
fn canonical_snapshot_origin(
  display_name : BytesView,
  theory_key : BytesView,
  ordinal : UInt,
) -> @identity.Origin {
  @identity.Origin::snapshot(
    display_name,
    @identity.SnapshotSymbolKey::new(
      theory_key,
      ordinal,
      0U,
      Type,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
test "trusted Range and Float definitions have all-target canonical bytes" {
  let context = @identity.CompilationContext::new()
  let range = @logic.TypeSymbol::trusted_range(
    context,
    b"range8",
    canonical_snapshot_origin(b"range8", b"why3.Range", 3U),
    BigInt::from_string("-999999999999999999999999"),
    BigInt::from_string("999999999999999999999999"),
    None,
  )
  assert_eq(
    @canonical.encode_type_symbol(range).bytes(),
    b"[\"TypeSymbol\",[\"type\",0],\"72616e676538\",[\"Origin.Snapshot\",\"72616e676538\",[\"SnapshotSymbolKey\",\"776879332e52616e6765\",3,0,\"type\",\"0000000000000000000000000000000000000000000000000000000000000000\"],[]],[],[\"TypeDefinition.Range\",-999999999999999999999999,999999999999999999999999]]\n",
  )
  let float = @logic.TypeSymbol::trusted_float(
    context,
    b"float32",
    canonical_snapshot_origin(b"float32", b"why3.Float", 4U),
    8,
    24,
    None,
  )
  assert_eq(
    @canonical.encode_type_symbol(float).bytes(),
    b"[\"TypeSymbol\",[\"type\",0],\"666c6f61743332\",[\"Origin.Snapshot\",\"666c6f61743332\",[\"SnapshotSymbolKey\",\"776879332e466c6f6174\",4,0,\"type\",\"0000000000000000000000000000000000000000000000000000000000000000\"],[]],[],[\"TypeDefinition.Float\",8,24]]\n",
  )
  assert_eq(
    @canonical.encode_ty(@logic.Ty::app(range, [], None)).bytes(),
    b"[\"TyApp\",[\"type\",0],[]]\n",
  )
}

///|
test "type variables share deterministic type-symbol encounter numbering" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let box_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    @identity.Origin::user(b"box", None, []),
    [parameter],
    None,
  )
  let alias_symbol = @logic.TypeSymbol::new_alias(
    context,
    b"alias",
    @identity.Origin::user(b"alias", None, []),
    [parameter],
    @logic.Ty::app(box_symbol, [@logic.Ty::variable(parameter)], None),
    None,
  )
  assert_eq(
    @canonical.encode_type_symbol(alias_symbol).bytes(),
    b"[\"TypeSymbol\",[\"type\",0],\"616c696173\",[\"Origin.User\",\"616c696173\",[\"none\"],[]],[[\"type\",1]],[\"TypeDefinition.Alias\",[\"TyApp\",[\"type\",2],[[\"TyVar\",[\"type\",1]]]]]]\n",
  )
}

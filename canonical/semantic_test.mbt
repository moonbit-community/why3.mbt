// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn semantic_snapshot_origin(
  name : BytesView,
  kind : @identity.SnapshotSymbolKind,
  ordinal : UInt,
) -> @identity.Origin {
  @identity.Origin::snapshot(
    name,
    @identity.SnapshotSymbolKey::new(
      b"why3.CanonicalTest",
      ordinal,
      0U,
      kind,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
fn semantic_user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
fn semantic_builtin_type(
  context : @identity.CompilationContext,
  name : BytesView,
  kind : @logic.BuiltinTypeKind,
  ordinal : UInt,
) -> @logic.Ty raise @logic.TypeError {
  let symbol = @logic.TypeSymbol::trusted_builtin(
    context,
    name,
    semantic_snapshot_origin(name, Type, ordinal),
    kind,
    None,
  )
  @logic.Ty::app(symbol, [], None)
}

///|
test "exact integer real and byte-string canonical constants" {
  assert_eq(
    @canonical.encode_constant(
      @logic.Constant::integer(
        IntegerHexadecimal,
        BigInt::from_string("123456789012345678901234567890"),
      ),
    ).bytes(),
    b"[\"ConstantInt\",\"ILitHex\",123456789012345678901234567890]\n",
  )
  assert_eq(
    @canonical.encode_constant(
      @logic.Constant::real(
        RealDecimal(-2L),
        @parser.RealValue::normalized(
          BigInt::from_int(3),
          BigInt::from_int(0),
          BigInt::from_int(0),
        ),
      ),
    ).bytes(),
    b"[\"ConstantReal\",[\"RLitDec\",-2],3,0,0]\n",
  )
  assert_eq(
    @canonical.encode_constant(@logic.Constant::string(b"a\x00\xff")).bytes(),
    b"[\"ConstantString\",\"6100ff\"]\n",
  )
}

///|
test "quantifier binders canonicalize to de Bruijn indices" {
  let context = @identity.CompilationContext::new()
  let integer = semantic_builtin_type(context, b"int", BuiltinInteger, 0U)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    semantic_user_origin(b"p"),
    [integer],
    None,
  )
  let make_formula = fn(name) -> @logic.Term raise @logic.TypeError {
    let variable = @logic.VSymbol::new(
      context,
      name,
      semantic_user_origin(name),
      integer,
      None,
    )
    @logic.Term::quantify(
      ForallQuantifier,
      [variable],
      [],
      @logic.Term::apply_predicate(
        predicate,
        [@logic.Term::variable(variable)],
        None,
      ),
      None,
    )
  }
  let left = @canonical.encode_term(make_formula(b"x"))
  let right = @canonical.encode_term(make_formula(b"renamed"))
  assert_eq(left.bytes(), right.bytes())
  assert_eq(
    left.bytes(),
    b"[\"Tquant.Forall\",[[\"TyApp\",[\"type\",0],[]]],[],[\"Tapp\",[\"logic\",0],[],[[\"Tvar\",[\"bound\",0]]],[\"none\"]]]\n",
  )
}

///|
test "trusted Ddata has exact schema-v2 canonical bytes" {
  let context = @identity.CompilationContext::new()
  let unit_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"unit",
    semantic_snapshot_origin(b"unit", Type, 0U),
    [],
    None,
  )
  let unit_type = @logic.Ty::app(unit_symbol, [], None)
  let tuple0 = @logic.LSymbol::trusted_constructor(
    context,
    b"Tuple0",
    semantic_snapshot_origin(b"Tuple0", Logic, 1U),
    [],
    unit_type,
    1,
    None,
  )
  let data_constructor = @logic.DataConstructor::trusted_new(tuple0, [], None)
  let data = @logic.DataDeclaration::trusted_new(
    unit_symbol,
    [data_constructor],
    None,
  )
  let declaration = @logic.Decl::trusted_data(
    context,
    semantic_snapshot_origin(b"unit", Type, 0U),
    [data],
    None,
  )
  let zero_digest = b"0000000000000000000000000000000000000000000000000000000000000000"
  let theory = b"776879332e43616e6f6e6963616c54657374"
  let type_origin = b"[\"Origin.Snapshot\",\"756e6974\",[\"SnapshotSymbolKey\",\"" +
    theory +
    b"\",0,0,\"type\",\"" +
    zero_digest +
    b"\"],[]]"
  let constructor_origin = b"[\"Origin.Snapshot\",\"5475706c6530\",[\"SnapshotSymbolKey\",\"" +
    theory +
    b"\",1,0,\"logic\",\"" +
    zero_digest +
    b"\"],[]]"
  let expected = b"[\"Decl\"," +
    type_origin +
    b",[],[\"Ddata\",[[[\"TypeSymbol\",[\"type\",0],\"756e6974\"," +
    type_origin +
    b",[],[\"TypeDefinition.NoDef\"]],[[[\"LSymbol\",[\"logic\",0],\"5475706c6530\"," +
    constructor_origin +
    b",[],[],[\"some\",[\"TyApp\",[\"type\",0],[]]]],[]]]]]]]\n"
  assert_eq(@canonical.encode_decl(declaration).bytes(), expected)
}

///|
fn semantic_polymorphic_goal(
  type_name : BytesView,
  binder_name : BytesView,
) -> @logic.Decl raise @logic.TypeError {
  let context = @identity.CompilationContext::new()
  let type_variable = @logic.TyVarSymbol::new(
    context,
    type_name,
    semantic_user_origin(type_name),
  )
  let ty = @logic.Ty::variable(type_variable)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    semantic_user_origin(b"p"),
    [ty],
    None,
  )
  let binder = @logic.VSymbol::new(
    context,
    binder_name,
    semantic_user_origin(binder_name),
    ty,
    None,
  )
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [binder],
    [],
    @logic.Term::apply_predicate(
      predicate,
      [@logic.Term::variable(binder)],
      None,
    ),
    None,
  )
  @logic.Decl::proposition(
    context,
    semantic_user_origin(b"goal"),
    Pgoal,
    @logic.PrSymbol::new(context, b"goal", semantic_user_origin(b"goal")),
    formula,
    None,
  )
}

///|
test "polymorphic proposition canonicalization ignores binder spelling" {
  let left = @canonical.encode_decl(semantic_polymorphic_goal(b"a", b"x"))
  let right = @canonical.encode_decl(
    semantic_polymorphic_goal(b"renamed_type", b"renamed_value"),
  )
  assert_eq(left.bytes(), right.bytes())
  assert_true(left.bytes().length() > 0)
}

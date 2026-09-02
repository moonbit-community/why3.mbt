// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn semantic_user_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
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
test "v3 constants have exact graph bytes" {
  let encoded = @canonical.encode_constant(
    @logic.Constant::integer(
      ILitHex,
      BigInt::from_string("123456789012345678901234567890"),
    ),
  )
  assert_eq(
    encoded.bytes(),
    b"[\"GraphV3\",[[\"Constant.constant.ConstInt\",[\"Number.int_constant\",[\"Number.int_literal_kind.ILitHex\",[\"Unit\"]],[\"Integer\",\"123456789012345678901234567890\"]]]],[]]\n",
  )
}

///|
test "canonical graph keeps binders alpha-invariant" {
  let left = @canonical.encode_decl(semantic_polymorphic_goal(b"a", b"x"))
  let right = @canonical.encode_decl(
    semantic_polymorphic_goal(b"renamed_type", b"renamed_value"),
  )
  assert_eq(left.bytes(), right.bytes())
  assert_eq(left.bytes()[:10], b"[\"GraphV3\"")
}

///|
test "canonical graph covers coinductive declarations" {
  let context = @identity.CompilationContext::new()
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"stream",
    semantic_user_origin(b"stream"),
    [],
    None,
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"stream_case",
    semantic_user_origin(b"stream_case"),
  )
  let case_ = @logic.InductiveCase::new(
    context,
    proposition,
    @logic.Term::apply_predicate(predicate, [], None),
    None,
  )
  let inductive = @logic.InductiveDeclaration::new(predicate, [case_], None)
  let declaration = @logic.Decl::inductive(
    context,
    semantic_user_origin(b"stream"),
    Coind,
    [inductive],
    None,
  )
  assert_eq(@canonical.encode_decl(declaration).bytes()[:10], b"[\"GraphV3\"")
}

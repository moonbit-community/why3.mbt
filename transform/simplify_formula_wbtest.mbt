// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "simplify_formula removes asymmetric split decoration" {
  let decorated = @logic.Term::true_formula().add_attributes([
    b"asym_split", b"keep",
  ])
  let stripped = remove_term_attribute(decorated, b"asym_split")
  assert_eq(stripped.attributes(), [b"keep"])
}

///|
test "simplify_formula removes asymmetric split from predicate formulas" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"p", None, [])
  let predicate = @logic.LSymbol::new_predicate(context, b"p", origin, [], None)
  let decorated = @logic.Term::apply_predicate(predicate, [], None).add_attributes([
      b"asym_split", b"keep",
    ],
  )
  let simplified = simplify_formula_term(context, decorated)
  assert_eq(simplified.attributes(), [b"keep"])
}

///|
test "simplify_formula preserves nested structure while removing decoration" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"nested", None, [])
  let symbol = @logic.TypeSymbol::new_abstract(context, b"t", origin, [], None)
  let ty = @logic.Ty::app(symbol, [], None)
  let first = @logic.VSymbol::new(context, b"x", origin, ty, None)
  let second = @logic.VSymbol::new(context, b"y", origin, ty, None)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    origin,
    [ty],
    None,
  )
  let decorated = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(first)],
    None,
  ).add_attributes([b"asym_split", b"keep"])
  let other = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(second)],
    None,
  )
  let conjunction = @logic.Term::binary(And, decorated, other, None)
  guard simplify_formula_term(context, conjunction).view()
    is Tbinop(And, direct_left, _) else {
    fail("simplification changed the direct conjunction shape")
  }
  assert_eq(direct_left.attributes(), [b"keep"])
  let inner = @logic.Term::quantify(
    ForallQuantifier,
    [second],
    [],
    conjunction,
    None,
  )
  let nested = @logic.Term::quantify(ForallQuantifier, [first], [], inner, None)
  guard simplify_formula_term(context, nested).view()
    is Tquant(_, _, _, outer_body) &&
    outer_body.view() is Tquant(_, _, _, inner_body) &&
    inner_body.view() is Tbinop(And, left, _) else {
    fail("simplification changed the nested formula shape")
  }
  assert_eq(left.attributes(), [b"keep"])
}

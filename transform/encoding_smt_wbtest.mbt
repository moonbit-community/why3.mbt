// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "guards clone case binders in set order before pattern traversal" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"guards", None, [])
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"item",
    origin,
    [],
    None,
  )
  let ty = @logic.Ty::app(type_symbol, [], None)
  // Allocation order deliberately differs from pattern traversal order.
  let d = @logic.VSymbol::new(context, b"d", origin, ty, None)
  let e = @logic.VSymbol::new(context, b"e", origin, ty, None)
  let a = @logic.VSymbol::new(context, b"a", origin, ty, None)
  let b = @logic.VSymbol::new(context, b"b", origin, ty, None)
  let c = @logic.VSymbol::new(context, b"c", origin, ty, None)
  let pattern = @logic.Pattern::as_pattern(
    @logic.Pattern::as_pattern(
      @logic.Pattern::as_pattern(
        @logic.Pattern::as_pattern(@logic.Pattern::variable(a), b, None),
        c,
        None,
      ),
      d,
      None,
    ),
    e,
    None,
  )
  let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
  let cloned = guard_clone_branch_pattern_identifiers(context, pattern, aliases)
  let traversal = cloned.bound_variables().to_owned()
  assert_eq([ for variable in traversal => variable.view().name ], [
    b"a", b"b", b"c", b"d", b"e",
  ])
  traversal.sort_by((left, right) => {
    guard_compare_semantic_ids(left.semantic_id(), right.semantic_id())
  })
  assert_eq([ for variable in traversal => variable.view().name ], [
    b"d", b"e", b"a", b"b", b"c",
  ])
}

///|
test "twin identifier rebinding respects nested binder shadowing" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"twin-shadowing", None, [])
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"item",
    origin,
    [],
    None,
  )
  let ty = @logic.Ty::app(type_symbol, [], None)
  let shadowed = @logic.VSymbol::new(context, b"x", origin, ty, None)
  let replacement = @logic.VSymbol::new(context, b"x", origin, ty, None)
  let term = @logic.Term::let_in(
    shadowed,
    @logic.Term::variable(shadowed),
    @logic.Term::variable(shadowed),
    None,
  )
  let aliases : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
  aliases[shadowed] = replacement
  let rebound = rebind_term_identifiers(term, aliases, @identity.Twin)
  guard rebound.view() is Tlet(binder, value, body) &&
    value.view() is Tvar(value_variable) &&
    body.view() is Tvar(body_variable) else {
    fail("twin rebinding changed the nested let shape")
  }
  assert_true(binder.identifier_id() == shadowed.identifier_id())
  assert_true(value_variable.identifier_id() == replacement.identifier_id())
  assert_true(body_variable.identifier_id() == shadowed.identifier_id())
}

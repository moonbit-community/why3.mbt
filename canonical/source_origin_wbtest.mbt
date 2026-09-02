// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "portable generated origins expose only the selected source anchor" {
  let selected = @identity.SourceSpan::new(
    b"examples/root.mlw", 1, 2, 1L, 1L, 1L, 2L,
  )
  let imported = @identity.SourceSpan::new(
    b"examples/dependency.mlw", 3, 4, 2L, 1L, 2L, 2L,
  )
  let state = CanonicalV3State::new_for_source(b"examples/root.mlw")
  assert_eq(state.generated_source_span(Some(selected)), Some(selected))
  assert_eq(state.generated_source_span(Some(imported)), None)

  let origin = @identity.Origin::generated_with_identifier_source_span(
    Guards,
    b"t",
    Some(imported),
    Some(imported),
    [],
  )
  assert_eq(origin.identifier_source_span(), Some(imported))
  let imported_origin = encode_canonical_value(v3_origin(state, origin))
  let selected_origin = encode_canonical_value(
    v3_origin(
      CanonicalV3State::new_for_source(b"examples/dependency.mlw"),
      origin,
    ),
  )
  assert_true(imported_origin.bytes() != selected_origin.bytes())
}

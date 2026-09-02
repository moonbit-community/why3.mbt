// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "semantic ids are fresh locally and isolated across contexts" {
  let left = @identity.CompilationContext::new()
  let right = @identity.CompilationContext::new()
  let left_zero = left.fresh_id()
  let left_one = left.fresh_id()
  let right_zero = right.fresh_id()
  assert_eq(left_zero.local_id(), 0L)
  assert_eq(left_one.local_id(), 1L)
  assert_eq(right_zero.local_id(), 0L)
  assert_true(left_zero != left_one)
  assert_true(left_zero != right_zero)
  assert_true(left.contains(left_zero))
  assert_false(left.contains(right_zero))
  let collisions : Map[@identity.SemanticId, Bytes] = Map([])
  collisions[left_zero] = b"left"
  collisions[right_zero] = b"right"
  assert_eq(collisions.length(), 2)
  assert_eq(collisions[left_zero], b"left")
  assert_eq(collisions[right_zero], b"right")
}

///|
test "identifier watermarks delimit compilation-local clone events" {
  let context = @identity.CompilationContext::new()
  let other = @identity.CompilationContext::new()
  let before = context.identifier_watermark()
  let initial = context.fresh_id().identifier_id()
  let first_clone = context.fresh_identifier_clone_id(initial)
  let after_first = context.identifier_watermark()
  let second_clone = context.fresh_identifier_clone_id(first_clone)
  let first_events = context.identifier_clone_events_since(before)
  assert_eq(first_events.length(), 2)
  assert_true(first_events[0].original() == initial)
  assert_true(first_events[0].clone() == first_clone)
  assert_true(first_events[1].original() == first_clone)
  assert_true(first_events[1].clone() == second_clone)
  let second_events = context.identifier_clone_events_since(after_first)
  assert_eq(second_events.length(), 1)
  assert_true(second_events[0].clone() == second_clone)
  assert_true(other.identifier_clone_events_since(before).is_empty())
}

///|
test "same spelling never substitutes for semantic identity" {
  let context = @identity.CompilationContext::new()
  let first = context.fresh_id()
  let second = context.fresh_id()
  let first_origin = @identity.Origin::user(b"same", None, [])
  let second_origin = @identity.Origin::user(b"same", None, [])
  assert_eq(first_origin.display_name(), second_origin.display_name())
  assert_true(first != second)
}

///|
test "cross-context operations fail with ContextMismatch" {
  let left = @identity.CompilationContext::new().fresh_id()
  let right = @identity.CompilationContext::new().fresh_id()
  try left.require_same_context(right, operation="test combine") catch {
    ContextMismatch(operation) => assert_eq(operation, "test combine")
  } noraise {
    _ => fail("expected ContextMismatch")
  }
}

///|
test "source symbol locator includes every stable field" {
  let digest = Bytes::make(32, b'\x11')
  let key = @identity.SourceSymbolKey::new(b"int.Int", 7U, 2U, Logic, digest)
  assert_eq(
    key,
    @identity.SourceSymbolKey::new(b"int.Int", 7U, 2U, Logic, digest),
  )
  assert_true(
    key != @identity.SourceSymbolKey::new(b"int.Int", 8U, 2U, Logic, digest),
  )
  assert_true(
    key != @identity.SourceSymbolKey::new(b"int.Int", 7U, 3U, Logic, digest),
  )
  assert_true(
    key !=
    @identity.SourceSymbolKey::new(b"int.Int", 7U, 2U, Proposition, digest),
  )
  let changed_digest = Bytes::make(32, b'\x12')
  assert_true(
    key !=
    @identity.SourceSymbolKey::new(b"int.Int", 7U, 2U, Logic, changed_digest),
  )
}

///|
test "origins preserve byte metadata and separate normalization eligibility" {
  let span = @identity.SourceSpan::new(
    b"fixtures/\xff.mlw", 9, 13, 2L, 4L, 2L, 8L,
  )
  let user = @identity.Origin::user(b"\xe4\xb8\xad", Some(span), [
    b"z", b"\xff", b"a", b"z",
  ])
  let generated = @identity.Origin::generated(Wp, b"vc", None, [])
  let derived = @identity.Origin::generated_derived(
    EliminateDefinitionConditionally,
    b"const'def",
    Some(span),
    [],
  )
  assert_false(user.allows_generated_name_normalization())
  assert_true(generated.allows_generated_name_normalization())
  assert_eq(user.display_name(), b"\xe4\xb8\xad")
  assert_eq(user.attributes(), [b"a", b"z", b"\xff"])
  assert_eq(derived.source_span(), None)
  assert_eq(derived.identifier_source_span(), Some(span))
  guard user.source_span() is Some(stored_span) else {
    fail("expected source span")
  }
  let view = stored_span.view()
  assert_eq(view.relative_path, b"fixtures/\xff.mlw")
  assert_eq(view.start_byte, 9)
  assert_eq(view.end_byte, 13)
  assert_eq(view.start_line, 2L)
  assert_eq(view.start_column, 4L)
}

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
test "snapshot key excludes export spelling and includes every stable field" {
  let digest = Bytes::make(32, b'\x11')
  let key = @identity.SnapshotSymbolKey::new(b"int.Int", 7U, 2U, Logic, digest)
  let renamed = @identity.Origin::snapshot(b"plus", key, [])
  let aliased = @identity.Origin::snapshot(b"infix +", key, [])
  assert_eq(renamed.snapshot_key(), aliased.snapshot_key())
  assert_true(
    key != @identity.SnapshotSymbolKey::new(b"int.Int", 8U, 2U, Logic, digest),
  )
  assert_true(
    key != @identity.SnapshotSymbolKey::new(b"int.Int", 7U, 3U, Logic, digest),
  )
  assert_true(
    key !=
    @identity.SnapshotSymbolKey::new(b"int.Int", 7U, 2U, Proposition, digest),
  )
  let changed_digest = Bytes::make(32, b'\x12')
  assert_true(
    key !=
    @identity.SnapshotSymbolKey::new(b"int.Int", 7U, 2U, Logic, changed_digest),
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
  let digest = Bytes::make(32, b'\x00')
  let snapshot = @identity.Origin::snapshot(
    b"snapshot",
    @identity.SnapshotSymbolKey::new(b"why3.Unit", 0U, 0U, Type, digest),
    [],
  )
  let generated = @identity.Origin::generated(Wp, b"vc", None, [])
  assert_false(user.allows_generated_name_normalization())
  assert_false(snapshot.allows_generated_name_normalization())
  assert_true(generated.allows_generated_name_normalization())
  assert_eq(user.display_name(), b"\xe4\xb8\xad")
  assert_eq(user.attributes(), [b"a", b"z", b"\xff"])
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

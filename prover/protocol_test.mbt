// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "prover limits freeze default, zero, maximum, and rejection" {
  assert_eq(default_solver_seconds(), 10)
  assert_eq(parent_deadline_seconds(0), None)
  assert_eq(parent_deadline_seconds(10), Some(41))
  assert_eq(parent_deadline_seconds(86400), Some(345601))
  try validate_solver_seconds(86401) catch {
    ConfigError(diagnostic) => assert_eq(diagnostic.kind, InvalidTimeout)
  } noraise {
    _ => fail("expected timeout above maximum to fail")
  }
}

///|
test "command spec is argv data and rejects NUL" {
  let command = CommandSpec::new(
    b"profile",
    StandardInput,
    b"z3",
    [b"-smt2", b"-in"],
    10,
  )
  let view = command.view()
  assert_eq(view.executable_request, b"z3")
  assert_eq(view.arguments, [b"-smt2", b"-in"])
  assert_eq(view.parent_deadline_policy, DeadlineAfterSeconds(41))
  assert_eq(view.stdout_limit_bytes, 2097152)
  assert_eq(view.stderr_limit_bytes, 2097152)
  try
    CommandSpec::new(b"profile", StandardInput, b"z3", [b"bad\x00argument"], 10)
  catch {
    ConfigError(diagnostic) => assert_eq(diagnostic.kind, InvalidCommand)
  } noraise {
    _ => fail("expected NUL argument to fail")
  }
}

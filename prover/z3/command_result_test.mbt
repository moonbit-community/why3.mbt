// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn outcome(
  stdout : BytesView,
  stderr : BytesView,
  status? : @prover.ProcessExitStatus = @prover.Exited(0),
) -> @prover.RawProcessOutcome {
  @prover.RawProcessOutcome::new(stdout, stderr, status)
}

///|
test "z3 argv freezes default, zero, and maximum timeout" {
  let spec = z3_static_spec()
  let default = spec.command_spec().view()
  assert_eq(default.executable_request, b"z3")
  assert_eq(default.arguments, [
    b"-smt2", b"-in", b"-T:10", b"sat.random_seed=42", b"nlsat.randomize=false",
    b"smt.random_seed=42", b"-st",
  ])
  assert_eq(default.parent_deadline_policy, @prover.DeadlineAfterSeconds(41))
  let zero = spec.command_spec(solver_seconds=0).view()
  assert_eq(zero.arguments, [
    b"-smt2", b"-in", b"sat.random_seed=42", b"nlsat.randomize=false", b"smt.random_seed=42",
    b"-st",
  ])
  assert_eq(zero.parent_deadline_policy, @prover.NoAutomaticDeadline)
  let maximum = spec.command_spec(solver_seconds=86400).view()
  assert_eq(maximum.arguments[2], b"-T:86400")
  assert_eq(
    maximum.parent_deadline_policy,
    @prover.DeadlineAfterSeconds(345601),
  )
}

///|
test "z3 result parser follows frozen canned answer precedence" {
  assert_eq(parse_result(outcome(b"unsat\n", b"")), @prover.Valid)
  assert_eq(parse_result(outcome(b"sat\n", b"")), @prover.Unknown(b"sat"))
  assert_eq(
    parse_result(outcome(b"unknown\n(:reason-unknown \"incomplete\")\n", b"")),
    @prover.Unknown(b"incomplete"),
  )
  assert_eq(
    parse_result(
      outcome(b"", b"interrupted by timeout\n", status=@prover.Exited(1)),
    ),
    @prover.Timeout,
  )
  assert_eq(
    parse_result(
      outcome(b"", b"(error \"out of memory\")\n", status=@prover.Exited(1)),
    ),
    @prover.OutOfMemory,
  )
  assert_eq(
    parse_result(
      outcome(
        b"",
        b"Maximal allocation counts 100 have been exceeded\n",
        status=@prover.Exited(1),
      ),
    ),
    @prover.StepLimitExceeded,
  )
  assert_eq(
    parse_result(
      outcome(
        b"unsat\n",
        b"diagnostic after answer\n",
        status=@prover.Exited(17),
      ),
    ),
    @prover.Valid,
  )
}

///|
test "z3 result parser keeps process and malformed errors out of outcomes" {
  try
    parse_result(
      outcome(b"", b"unclassified failure\n", status=@prover.Exited(17)),
    )
  catch {
    @prover.ProcessError(diagnostic) => {
      assert_eq(diagnostic.kind, @prover.UnclassifiedExit)
      assert_eq(diagnostic.exit_code, Some(17))
    }
    _ => fail("expected process error")
  } noraise {
    _ => fail("expected unclassified nonzero exit to fail")
  }
  try parse_result(outcome(b"\xff\n", b"")) catch {
    @prover.MalformedProverOutput(diagnostic) =>
      assert_eq(diagnostic.kind, @prover.InvalidUtf8)
    _ => fail("expected malformed prover output")
  } noraise {
    _ => fail("expected invalid UTF-8 to fail")
  }
  try
    parse_result(outcome(b"", b"", status=@prover.Signaled(b"SIGTERM")))
  catch {
    @prover.ProcessError(diagnostic) => {
      assert_eq(diagnostic.kind, @prover.SignaledProcess)
      assert_eq(diagnostic.signal, Some(b"SIGTERM"))
    }
    _ => fail("expected signaled process error")
  } noraise {
    _ => fail("expected signal without answer to fail")
  }
  try parse_result(outcome(b"", b"")) catch {
    @prover.MalformedProverOutput(diagnostic) =>
      assert_eq(diagnostic.kind, @prover.UnrecognizedOutput)
    _ => fail("expected empty prover output to be malformed")
  } noraise {
    _ => fail("expected empty output to fail")
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_command(
  script : BytesView,
  solver_seconds? : Int = 0,
) -> @prover.CommandSpec raise {
  @prover.CommandSpec::new(
    b"runner-test",
    @prover.StandardInput,
    b"/bin/sh",
    [b"-c", script.to_owned()],
    solver_seconds,
  )
}

///|
async fn test_runner(command : @prover.CommandSpec) -> NativeRunner {
  NativeRunner::new(command) catch {
    @prover.ProcessError(diagnostic) => abort(@debug.to_string(diagnostic))
    err => abort(@debug.to_string(err))
  }
}

///|
async fn test_capture() -> Unit {
  let command = test_command(
    b"input=$(cat); printf '%s' \"$input\"; printf 'diagnostic:%s' \"$LC_ALL\" >&2",
  )
  let runner = test_runner(command)
  assert_true(!runner.resolved_executable().is_empty())
  guard runner.run(b"query-bytes") is Completed(raw)
  let outcome = raw.view()
  assert_eq(outcome.stderr, b"diagnostic:C")
  assert_eq(outcome.stdout, b"query-bytes")
  assert_eq(outcome.status, @prover.Exited(0))
}

///|
async fn test_signal_status() -> Unit {
  let runner = test_runner(test_command(b"kill -KILL $$"))
  guard runner.run(b"") is Completed(raw)
  assert_eq(raw.view().status, @prover.Signaled(b"SIGKILL"))
}

///|
async fn test_stdout_cap() -> Unit {
  let runner = test_runner(test_command(b"head -c 2097153 /dev/zero"))
  try runner.run(b"") catch {
    @prover.OutputLimitExceeded(diagnostic) => {
      assert_eq(diagnostic.stream, @prover.StandardOutput)
      assert_eq(diagnostic.limit_bytes, 2097152)
    }
    err => fail("expected stdout cap, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("expected stdout cap to fail")
  }
}

///|
async fn test_stderr_cap() -> Unit {
  let runner = test_runner(test_command(b"head -c 2097153 /dev/zero >&2"))
  try runner.run(b"") catch {
    @prover.OutputLimitExceeded(diagnostic) => {
      assert_eq(diagnostic.stream, @prover.StandardError)
      assert_eq(diagnostic.limit_bytes, 2097152)
    }
    err => fail("expected stderr cap, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("expected stderr cap to fail")
  }
}

///|
async fn test_answer_then_cap() -> Unit {
  let runner = test_runner(
    test_command(b"printf 'unsat\\n'; head -c 2097153 /dev/zero"),
  )
  try runner.run(b"") catch {
    @prover.OutputLimitExceeded(diagnostic) =>
      assert_eq(diagnostic.stream, @prover.StandardOutput)
    err => fail("expected answer-then-cap, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("recognized answer must not hide an output overflow")
  }
}

///|
async fn test_broken_pipe() -> Unit {
  let runner = test_runner(test_command(b"exit 0"))
  let query = Bytes::make(4 * 1024 * 1024, b'x')
  try runner.run(query) catch {
    @prover.ProcessError(diagnostic) =>
      assert_eq(diagnostic.kind, @prover.BrokenPipe)
    err => fail("expected broken pipe, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("expected an early stdin close to fail")
  }
}

///|
async fn test_missing_executable() -> Unit {
  let command = @prover.CommandSpec::new(
    b"runner-test",
    @prover.StandardInput,
    b"/definitely/missing/why3mbt-z3",
    [],
    0,
  )
  try NativeRunner::new(command) catch {
    @prover.ProcessError(diagnostic) =>
      assert_eq(diagnostic.kind, @prover.ExecutableNotFound)
    err => fail("expected missing executable, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("expected missing executable to fail")
  }
}

///|
async fn test_parent_deadline() -> Unit {
  let runner = test_runner(test_command(b"sleep 30", solver_seconds=1))
  guard runner.run(b"") is ParentDeadlineExceeded else {
    fail("expected parent deadline")
  }
}

///|
async fn assert_descendant_reaped(pid_file : String) -> Unit {
  assert_true(@fs.exists(pid_file))
  let descendant = @utf8.decode(@fs.read_file(pid_file).binary()) catch {
    _ => fail("descendant pid is not UTF-8")
  }
  let process_path = "/proc/" + descendant
  let mut descendant_gone = false
  for attempt = 0; attempt < 100; attempt = attempt + 1 {
    if !@fs.exists(process_path) {
      descendant_gone = true
      break
    }
    @async.sleep(10)
  }
  @fs.remove(pid_file)
  assert_true(descendant_gone)
}

///|
async fn test_root_exit_reaps_descendant() -> Unit {
  let pid_file = "_build/why3_native_runner_root_exit_descendant.pid"
  if @fs.exists(pid_file) {
    @fs.remove(pid_file)
  }
  let runner = test_runner(
    test_command(
      b"sleep 30 & child=$!; printf '%s' \"$child\" > _build/why3_native_runner_root_exit_descendant.pid; exit 0",
    ),
  )
  guard runner.run(b"") is Completed(raw)
  assert_eq(raw.view().status, @prover.Exited(0))
  assert_descendant_reaped(pid_file)
}

///|
async fn test_cancellation() -> Unit {
  let pid_file = "_build/why3_native_runner_cancelled_descendant.pid"
  if @fs.exists(pid_file) {
    @fs.remove(pid_file)
  }
  let runner = test_runner(
    test_command(
      b"sleep 30 & child=$!; printf '%s' \"$child\" > _build/why3_native_runner_cancelled_descendant.pid; wait",
    ),
  )
  try @async.with_timeout(200, () => runner.run(b"")) catch {
    @prover.ProcessError(diagnostic) =>
      assert_eq(diagnostic.kind, @prover.Cancelled)
    err => fail("expected cancellation, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("expected cancellation to fail")
  }
  assert_descendant_reaped(pid_file)
}

///|
async test "native runner integration cases run sequentially" {
  // The native debug test executable is a TCC response file. Re-entering the
  // same response file concurrently is not supported by the test launcher, so
  // keep the independent process-level cases serialized here.
  test_capture()
  test_signal_status()
  test_stdout_cap()
  test_stderr_cap()
  test_answer_then_cap()
  test_broken_pipe()
  test_missing_executable()
  test_root_exit_reaps_descendant()
  test_parent_deadline()
  test_cancellation()
}

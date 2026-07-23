// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
async test "CLI emits deterministic files" {
  let fixture = "tools/why3_reference/fixtures/solver-outcomes.mlw"
  let directory = "_build/why3_cli_integration_output"
  if @fs.exists(directory) {
    @fs.rmdir(directory, recursive=true)
  }
  let emit_code = run_cli([
    "why3mbt", "emit-smt", fixture, "-T", "SolverOutcomes", "-o", directory, "--json",
  ])
  assert_eq(emit_code, 0)
  assert_true(@fs.exists(directory + "/000000-756e7361745f76616c6964.smt2"))
  assert_true(@fs.exists(directory + "/000001-7361745f756e6b6e6f776e.smt2"))
  assert_true(
    @fs.exists(directory + "/000002-736f6c7665725f756e6b6e6f776e.smt2"),
  )
  assert_eq(run_cli(["why3mbt", "emit-smt", fixture, "--goal-index", "0"]), 0)
  try run_cli(["why3mbt", "emit-smt", fixture]) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, OutputError)
    err => fail("expected output selection error, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("multiple SMT goals without -o must fail")
  }
  @fs.rmdir(directory, recursive=true)
}

///|
async test "CLI uses three-valued exits and closes program verification conditions" {
  let fixture = "tools/why3_reference/fixtures/solver-outcomes.mlw"
  assert_eq(
    run_cli(["why3mbt", "prove", fixture, "--goal-index", "0", "--json"]),
    0,
  )
  assert_eq(
    run_cli(["why3mbt", "prove", fixture, "--goal-index", "1", "--json"]),
    2,
  )
  let mvp = "tools/why3_reference/fixtures/mvp.mlw"
  assert_eq(run_cli(["why3mbt", "prove", mvp, "-T", "Abs", "--json"]), 0)
  assert_eq(
    run_cli(["why3mbt", "prove", mvp, "-T", "RoutineCall", "--json"]),
    0,
  )
  assert_eq(
    run_cli([
      "why3mbt", "prove", "tests/vc/false-post.mlw", "-T", "FalsePost", "--json",
    ]),
    2,
  )
}

///|
async test "CLI refuses colliding multi-unit SMT filenames" {
  let source = b"theory First\n  goal Same : true\nend\n\ntheory Second\n  goal Same : true\nend\n"
  let calls = @pipeline.prepare_proof(
    @pipeline.check(source, filename=b"colliding-goals.mlw"),
  )
  assert_eq(calls.length(), 2)
  let directory = "_build/why3_cli_collision_output"
  if @fs.exists(directory) {
    @fs.rmdir(directory, recursive=true)
  }
  try write_smt_files(calls, [0, 1], directory) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, OutputError)
    err => fail("expected filename collision, got \{@debug.to_string(err)}")
  } noraise {
    _ => fail("colliding selected goal filenames must fail")
  }
  assert_true(!@fs.exists(directory))
}

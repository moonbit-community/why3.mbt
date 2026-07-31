// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
async fn test_cli_deterministic_files() -> Unit {
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
async fn test_cli_exit_codes_and_program_vcs() -> Unit {
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
async fn test_cli_filename_collisions() -> Unit {
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

///|
async fn test_cli_native_loadpath() -> Unit {
  assert_eq(
    run_cli([
      "why3mbt", "check", "tools/why3_reference/fixtures/mvp.mlw", "-L", "fixtures/why3-1.7.2/stdlib",
      "--no-stdlib",
    ]),
    0,
  )
}

///|
async fn test_cli_user_transforms_and_metas() -> Unit {
  assert_eq(
    run_cli([
      "why3mbt", "emit-smt", "tools/why3_reference/fixtures/solver-outcomes.mlw",
      "-T", "SolverOutcomes", "-G", "unsat_valid", "-a", "simplify_formula", "-M",
      "encoding:monomorphic_only", "--json",
    ]),
    0,
  )
}

///|
async fn test_cli_native_model_output() -> Unit {
  let source = b"theory ModelValues\n  use int.Int\n  constant x : int\n  goal model_x : x = 0\nend\n"
  let calls = @pipeline.prepare_proof(
    @pipeline.check(source, filename=b"model-values.mlw"),
    request_model=true,
  )
  assert_eq(calls.length(), 1)
  let call = calls[0]
  let runner = @native.NativeRunner::new(call.command())
  guard runner.run(call.query().bytes()) is Completed(raw) else {
    fail("native Z3 model request exceeded its parent deadline")
  }
  assert_eq(@z3.parse_result(raw), @prover.Unknown(b"sat"))
  let values = @z3.parse_smtv2_model_for_query(call.query(), raw.view().stdout)
  assert_true(!values.is_empty())
  let mut matched_x = false
  for value in values {
    match value.origin {
      Some(origin) if value.semantic_id is Some(_) &&
        origin.display_name() == b"x" => matched_x = true
      _ => ()
    }
  }
  assert_true(matched_x)
  assert_true(
    model_values_json(values).contains("\"matched_source_symbol\":true"),
  )
}

///|
async fn test_cli_multi_file_output() -> Unit {
  let fixture = "tools/why3_reference/fixtures/solver-outcomes.mlw"
  let directory = "_build/why3_cli_multi_output"
  if @fs.exists(directory) {
    @fs.rmdir(directory, recursive=true)
  }
  assert_eq(
    run_cli([
      "why3mbt", "prove", fixture, "-T", "SolverOutcomes", "-G", "unsat_valid", fixture,
      "-T", "SolverOutcomes", "-G", "sat_unknown", "-P", "z3", "--z3", "/prover/must/not/be/started",
      "-o", directory,
    ]),
    0,
  )
  assert_true(
    @fs.exists(directory + "/000000-000000-756e7361745f76616c6964.smt2"),
  )
  assert_true(
    @fs.exists(directory + "/000001-000001-7361745f756e6b6e6f776e.smt2"),
  )
  @fs.rmdir(directory, recursive=true)
}

///|
async test "CLI native integration cases run sequentially" {
  // Every case constructs a full semantic/VC/SMT environment. Running these
  // process-level cases concurrently can exceed the native test process's
  // allocation envelope, so keep their complete assertions serialized.
  test_cli_configuration_defaults()
  test_cli_deterministic_files()
  test_cli_exit_codes_and_program_vcs()
  test_cli_filename_collisions()
  test_cli_native_loadpath()
  test_cli_user_transforms_and_metas()
  test_cli_native_model_output()
  test_cli_multi_file_output()
}

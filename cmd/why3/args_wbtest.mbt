// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "CLI defaults and selectors are parsed deterministically" {
  let defaults = parse_arguments(["why3mbt", "prove", "input.mlw"])
  assert_eq(defaults.command, ProveCommand)
  assert_eq(defaults.loadpaths, [])
  assert_true(defaults.use_stdlib)
  assert_eq(defaults.solver_seconds, 10)
  assert_eq(defaults.prover, "z3")
  assert_eq(defaults.output_mode, HumanOutput)
  let selected = parse_arguments([
    "why3mbt", "prove", "input.mlw", "-T", "T", "--goal-index", "2", "--z3", "/opt/z3",
    "-t", "0.25", "--json",
  ])
  guard selected.inputs is [{ file: "input.mlw", theories: [theory] }] else {
    fail("CLI input/theory ordering was not retained")
  }
  assert_eq(theory.name, b"T")
  assert_eq(selected.goal_index, Some(2))
  assert_eq(selected.z3, Some(b"/opt/z3"))
  assert_eq(selected.requested_solver_seconds, 0.25)
  assert_eq(selected.solver_seconds, 1)
  assert_eq(selected.output_mode, JsonOutput)
  assert_eq(
    parse_arguments(["why3mbt", "prove", "input.mlw", "--json-model-values"]).output_mode,
    JsonModelValuesOutput,
  )
}

///|
test "CLI accepts ordered loadpaths and rejects invalid timeout" {
  let external = parse_arguments([
    "why3mbt", "task", "input.mlw", "-L", "first", "--loadpath", "second", "--no-stdlib",
  ])
  assert_eq(external.loadpaths, ["first", "second"])
  assert_true(!external.use_stdlib)
  try parse_arguments(["why3mbt", "prove", "input.mlw", "-t", "86401"]) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, InvalidTimeout)
  } noraise {
    _ => fail("expected invalid timeout rejection")
  }
}

///|
test "CLI preserves multi-file selector order and accepts standard input" {
  let options = parse_arguments([
    "why3mbt", "prove", "first.mlw", "-T", "First", "-G", "G1", "-G", "G2", "-",
    "-T", "Second", "-G", "G3", "--parse-only",
  ])
  guard options.inputs
    is [
      {
        file: "first.mlw",
        theories: [{ name: b"First", goals: [b"G1", b"G2"] }],
      },
      { file: "-", theories: [{ name: b"Second", goals: [b"G3"] }] },
    ] else {
    fail("multi-file selector order was not retained")
  }
  assert_eq(options.stop_stage, ParseOnly)
}

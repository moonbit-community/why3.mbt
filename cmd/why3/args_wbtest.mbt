// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "CLI defaults and selectors are parsed deterministically" {
  let defaults = parse_arguments(["why3mbt", "prove", "input.mlw"])
  assert_eq(defaults.command, ProveCommand)
  assert_eq(defaults.solver_seconds, 10)
  assert_eq(defaults.prover, "z3")
  assert_eq(defaults.output_mode, HumanOutput)
  let selected = parse_arguments([
    "why3mbt", "prove", "input.mlw", "-T", "T", "--goal-index", "2", "--z3", "/opt/z3",
    "-t", "0", "--json",
  ])
  assert_eq(selected.theory, Some(b"T"))
  assert_eq(selected.goal_index, Some(2))
  assert_eq(selected.z3, Some(b"/opt/z3"))
  assert_eq(selected.solver_seconds, 0)
  assert_eq(selected.output_mode, JsonOutput)
}

///|
test "CLI rejects external loadpaths and invalid timeout" {
  try parse_arguments(["why3mbt", "task", "input.mlw", "-L", "other"]) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, ExternalLoadpath)
  } noraise {
    _ => fail("expected external loadpath rejection")
  }
  try parse_arguments(["why3mbt", "prove", "input.mlw", "-t", "86401"]) catch {
    CliError(diagnostic) => assert_eq(diagnostic.kind, InvalidTimeout)
  } noraise {
    _ => fail("expected invalid timeout rejection")
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
enum CliCommand {
  CheckCommand
  TaskCommand
  EmitSmtCommand
  ProveCommand
} derive(Eq, Debug)

///|
enum CliOutputMode {
  HumanOutput
  JsonOutput
  CanonicalJsonOutput
} derive(Eq, Debug)

///|
struct CliOptions {
  command : CliCommand
  file : String
  theory : Bytes?
  goal : Bytes?
  goal_index : Int?
  output_directory : String?
  prover : String
  z3 : Bytes?
  solver_seconds : Int
  output_mode : CliOutputMode
}

///|
fn fail_cli(kind : CliErrorKind, message : String) -> Unit raise CliError {
  raise CliError({ kind, message })
}

///|
fn parse_nonnegative_integer(
  text : StringView,
  option : String,
) -> Int raise CliError {
  let bytes = @utf8.encode(text)
  if bytes.is_empty() {
    fail_cli(InvalidArgument, option + " requires a decimal integer")
  }
  let mut value = 0
  for byte in bytes {
    if byte < b'0' || byte > b'9' {
      fail_cli(InvalidArgument, option + " requires a decimal integer")
    }
    let digit = byte.to_int() - b'0'.to_int()
    if value > 100000000 {
      fail_cli(InvalidArgument, option + " integer is too large")
    }
    value = value * 10 + digit
  }
  value
}

///|
fn command_from_string(value : String) -> CliCommand raise CliError {
  match value {
    "check" => CheckCommand
    "task" => TaskCommand
    "emit-smt" => EmitSmtCommand
    "prove" => ProveCommand
    _ => {
      fail_cli(
        UsageError,
        "expected subcommand check, task, emit-smt, or prove",
      )
      CheckCommand
    }
  }
}

///|
fn option_value(
  arguments : ArrayView[String],
  index : Int,
  option : String,
) -> String raise CliError {
  if index + 1 >= arguments.length() {
    fail_cli(InvalidArgument, option + " requires a value")
  }
  arguments[index + 1]
}

///|
fn parse_arguments(arguments : ArrayView[String]) -> CliOptions raise CliError {
  if arguments.length() < 3 {
    fail_cli(
      UsageError,
      "usage: why3mbt check|task|emit-smt|prove file.mlw [options]",
    )
  }
  let command = command_from_string(arguments[1])
  let file = arguments[2]
  if file.has_prefix("-") {
    fail_cli(InvalidArgument, "the input file must precede all selectors")
  }
  let mut theory : Bytes? = None
  let mut goal : Bytes? = None
  let mut goal_index : Int? = None
  let mut output_directory : String? = None
  let mut prover = "z3"
  let mut z3 : Bytes? = None
  let mut solver_seconds = @prover.default_solver_seconds()
  let mut output_mode = HumanOutput
  let mut index = 3
  while index < arguments.length() {
    let argument = arguments[index]
    match argument {
      "-L" | "--loadpath" =>
        fail_cli(ExternalLoadpath, "UnsupportedFeature(ExternalLoadpath)")
      "-T" => {
        theory = Some(@utf8.encode(option_value(arguments, index, "-T")))
        index = index + 2
      }
      "-G" => {
        goal = Some(@utf8.encode(option_value(arguments, index, "-G")))
        index = index + 2
      }
      "--goal-index" => {
        goal_index = Some(
          parse_nonnegative_integer(
            option_value(arguments, index, "--goal-index"),
            "--goal-index",
          ),
        )
        index = index + 2
      }
      "-o" => {
        output_directory = Some(option_value(arguments, index, "-o"))
        index = index + 2
      }
      "-P" => {
        prover = option_value(arguments, index, "-P")
        index = index + 2
      }
      "--z3" => {
        z3 = Some(@utf8.encode(option_value(arguments, index, "--z3")))
        index = index + 2
      }
      "-t" => {
        solver_seconds = parse_nonnegative_integer(
          option_value(arguments, index, "-t"),
          "-t",
        )
        if solver_seconds > @prover.maximum_solver_seconds() {
          fail_cli(
            InvalidTimeout,
            "ConfigError(InvalidTimeout): timeout must be in 0..86400",
          )
        }
        index = index + 2
      }
      "--json" => {
        if output_mode != HumanOutput {
          fail_cli(InvalidArgument, "choose only one JSON output mode")
        }
        output_mode = JsonOutput
        index = index + 1
      }
      "--canonical-json" => {
        if output_mode != HumanOutput {
          fail_cli(InvalidArgument, "choose only one JSON output mode")
        }
        output_mode = CanonicalJsonOutput
        index = index + 1
      }
      _ => fail_cli(InvalidArgument, "unknown option: " + argument)
    }
  }
  if goal is Some(_) && goal_index is Some(_) {
    fail_cli(InvalidArgument, "-G and --goal-index are mutually exclusive")
  }
  match command {
    CheckCommand =>
      if theory is Some(_) ||
        goal is Some(_) ||
        goal_index is Some(_) ||
        output_directory is Some(_) ||
        z3 is Some(_) ||
        solver_seconds != @prover.default_solver_seconds() ||
        prover != "z3" {
        fail_cli(InvalidArgument, "check accepts only the input and JSON mode")
      }
    TaskCommand =>
      if output_directory is Some(_) ||
        z3 is Some(_) ||
        solver_seconds != @prover.default_solver_seconds() ||
        prover != "z3" {
        fail_cli(InvalidArgument, "task does not accept prover/output options")
      }
    EmitSmtCommand =>
      if z3 is Some(_) ||
        solver_seconds != @prover.default_solver_seconds() ||
        prover != "z3" {
        fail_cli(InvalidArgument, "emit-smt does not accept prover options")
      }
    ProveCommand => {
      if output_directory is Some(_) {
        fail_cli(InvalidArgument, "prove does not accept -o")
      }
      if prover != "z3" {
        fail_cli(InvalidArgument, "only the static z3 profile is supported")
      }
    }
  }
  {
    command,
    file,
    theory,
    goal,
    goal_index,
    output_directory,
    prover,
    z3,
    solver_seconds,
    output_mode,
  }
}

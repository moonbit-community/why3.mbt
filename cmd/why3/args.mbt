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
  JsonModelValuesOutput
  CanonicalJsonOutput
} derive(Eq, Debug)

///|
enum CliStopStage {
  RunPipeline
  ParseOnly
  TypeOnly
} derive(Eq, Debug)

///|
struct CliTheorySelection {
  name : Bytes
  goals : Array[Bytes]
}

///|
struct CliInput {
  file : String
  theories : Array[CliTheorySelection]
}

///|
struct CliSubGoal {
  file : String?
  line : Int64?
  explanation : Bytes?
}

///|
struct CliOptions {
  command : CliCommand
  inputs : Array[CliInput]
  loadpaths : Array[String]
  use_stdlib : Bool
  format : String?
  stop_stage : CliStopStage
  sub_goals : Array[CliSubGoal]
  goal_index : Int?
  output_directory : String?
  prover : String
  prover_explicit : Bool
  driver : String?
  transforms : Array[String]
  metas : Array[String]
  z3 : Bytes?
  solver_seconds : Int
  requested_solver_seconds : Double
  solver_limit_explicit : Bool
  steps_limit : Int
  memory_limit_mib : Int
  memory_limit_explicit : Bool
  config : String?
  extra_configs : Array[String]
  load_default_plugins : Bool
  print_theory : Bool
  print_namespace : Bool
  output_mode : CliOutputMode
}

///|
fn[A] fail_cli(kind : CliErrorKind, message : String) -> A raise CliError {
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
fn parse_nonnegative_seconds(
  text : StringView,
  option : String,
) -> (Double, Int) raise CliError {
  let value : Double = @string.from_str(text) catch {
    _ => fail_cli(InvalidArgument, option + " requires a number of seconds")
  }
  if value.is_nan() ||
    value.is_inf() ||
    value < 0.0 ||
    value > @prover.maximum_solver_seconds().to_double() {
    fail_cli(
      InvalidTimeout,
      "ConfigError(InvalidTimeout): timeout must be in 0..86400",
    )
  }
  (value, value.ceil().to_int())
}

///|
fn command_from_string(value : String) -> CliCommand raise CliError {
  match value {
    "check" => CheckCommand
    "task" => TaskCommand
    "emit-smt" => EmitSmtCommand
    "prove" => ProveCommand
    _ =>
      fail_cli(
        UsageError,
        "expected subcommand check, task, emit-smt, or prove",
      )
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
fn require_current_input(
  inputs : ArrayView[CliInput],
  option : String,
) -> Int raise CliError {
  if inputs.is_empty() {
    fail_cli(InvalidArgument, option + " requires a preceding input file")
  }
  inputs.length() - 1
}

///|
fn add_theory_selection(
  inputs : Array[CliInput],
  value : String,
) -> Unit raise CliError {
  let input = require_current_input(inputs, "-T/--theory")
  inputs[input].theories.push({ name: @utf8.encode(value), goals: [] })
}

///|
fn add_goal_selection(
  inputs : Array[CliInput],
  value : String,
) -> Unit raise CliError {
  let input = require_current_input(inputs, "-G/--goal")
  if inputs[input].theories.is_empty() {
    inputs[input].theories.push({ name: b"Top", goals: [] })
  }
  let theory = inputs[input].theories.length() - 1
  inputs[input].theories[theory].goals.push(@utf8.encode(value))
}

///|
fn parse_optional_line(text : StringView) -> Int64 raise CliError {
  let value = parse_nonnegative_integer(text, "-g/--sub-goal")
  if value == 0 {
    fail_cli(InvalidArgument, "-g/--sub-goal line numbers start at one")
  }
  value.to_int64()
}

///|
fn parse_sub_goal(value : String) -> CliSubGoal raise CliError {
  let bytes = @utf8.encode(value)
  let mut expl_start = bytes.length()
  for index, byte in bytes {
    if byte == b'@' {
      expl_start = index
      break
    }
  }
  let location = bytes[:expl_start]
  let explanation = if expl_start == bytes.length() {
    None
  } else if expl_start + 1 == bytes.length() {
    fail_cli(InvalidArgument, "-g/--sub-goal requires text after @")
  } else {
    Some(bytes[expl_start + 1:].to_owned())
  }
  let mut colon : Int? = None
  for index = location.length() - 1; index >= 0; index = index - 1 {
    if location[index] == b':' {
      colon = Some(index)
      break
    }
  }
  let (file, line) = match colon {
    Some(index) => {
      let line = @utf8.decode(location[index + 1:]) catch {
        _ => fail_cli(InvalidArgument, "-g/--sub-goal line number is not UTF-8")
      }
      let file = if index == 0 {
        None
      } else {
        Some(
          @utf8.decode(location[:index]) catch {
            _ => fail_cli(InvalidArgument, "-g/--sub-goal file is not UTF-8")
          },
        )
      }
      (file, Some(parse_optional_line(line)))
    }
    None =>
      if location.is_empty() {
        (None, None)
      } else {
        (
          Some(
            @utf8.decode(location) catch {
              _ => fail_cli(InvalidArgument, "-g/--sub-goal file is not UTF-8")
            },
          ),
          None,
        )
      }
  }
  if file is None && line is None && explanation is None {
    fail_cli(InvalidArgument, "-g/--sub-goal selector is empty")
  }
  { file, line, explanation }
}

///|
fn set_output_mode(
  current : CliOutputMode,
  requested : CliOutputMode,
) -> CliOutputMode raise CliError {
  if current != HumanOutput {
    fail_cli(InvalidArgument, "choose only one JSON output mode")
  }
  requested
}

///|
fn known_z3_prover(value : StringView) -> Bool {
  value == "z3" ||
  value == "Z3" ||
  value == "Z3,4.8.12" ||
  value == "Z3,4.8.12,"
}

///|
fn validate_cli_options(options : CliOptions) -> Unit raise CliError {
  if options.inputs.is_empty() {
    fail_cli(UsageError, "at least one input file or - is required")
  }
  let mut stdin_count = 0
  for input in options.inputs {
    if input.file == "-" {
      stdin_count = stdin_count + 1
    }
  }
  if stdin_count > 1 {
    fail_cli(InvalidArgument, "standard input may be selected only once")
  }
  if options.prover_explicit && options.driver is Some(_) {
    fail_cli(
      InvalidArgument,
      "-P/--prover and -D/--driver cannot be used together",
    )
  }
  if !known_z3_prover(options.prover) {
    fail_cli(
      UnsupportedCliFeature,
      "only the pinned Z3 4.8.12 profile is supported",
    )
  }
  if options.print_theory && options.print_namespace {
    fail_cli(
      InvalidArgument,
      "--print-theory and --print-namespace are mutually exclusive",
    )
  }
  if options.goal_index is Some(_) {
    for input in options.inputs {
      for theory in input.theories {
        if !theory.goals.is_empty() {
          fail_cli(
            InvalidArgument,
            "-G/--goal and --goal-index are mutually exclusive",
          )
        }
      }
    }
  }
  match options.command {
    CheckCommand =>
      if options.output_directory is Some(_) ||
        options.prover_explicit ||
        options.driver is Some(_) ||
        !options.transforms.is_empty() ||
        !options.metas.is_empty() ||
        options.steps_limit != 0 ||
        options.memory_limit_mib != 0 {
        fail_cli(
          InvalidArgument,
          "check does not accept prover, driver, transform, meta, or output options",
        )
      }
    TaskCommand =>
      if options.output_directory is Some(_) ||
        options.prover_explicit ||
        options.driver is Some(_) ||
        options.z3 is Some(_) ||
        !options.transforms.is_empty() ||
        !options.metas.is_empty() ||
        options.steps_limit != 0 ||
        options.memory_limit_mib != 0 {
        fail_cli(
          InvalidArgument,
          "task does not accept prover, driver, or output options",
        )
      }
    EmitSmtCommand =>
      if options.prover_explicit ||
        options.driver is Some(_) ||
        options.z3 is Some(_) ||
        options.steps_limit != 0 ||
        options.memory_limit_mib != 0 {
        fail_cli(
          InvalidArgument,
          "emit-smt does not accept prover or driver options",
        )
      }
    ProveCommand => ()
  }
}

///|
fn parse_arguments(arguments : ArrayView[String]) -> CliOptions raise CliError {
  if arguments.length() < 3 {
    fail_cli(
      UsageError,
      "usage: why3mbt check|task|emit-smt|prove [options] file.mlw ...",
    )
  }
  let command = command_from_string(arguments[1])
  let inputs : Array[CliInput] = []
  let loadpaths : Array[String] = []
  let mut use_stdlib = true
  let mut format : String? = None
  let mut stop_stage = RunPipeline
  let sub_goals : Array[CliSubGoal] = []
  let mut goal_index : Int? = None
  let mut output_directory : String? = None
  let mut prover = "z3"
  let mut prover_explicit = false
  let mut driver : String? = None
  let transforms : Array[String] = []
  let metas : Array[String] = []
  let mut z3 : Bytes? = None
  let mut solver_seconds = @prover.default_solver_seconds()
  let mut requested_solver_seconds = solver_seconds.to_double()
  let mut solver_limit_explicit = false
  let mut steps_limit = 0
  let mut memory_limit_mib = 0
  let mut memory_limit_explicit = false
  let mut config : String? = None
  let extra_configs : Array[String] = []
  let mut load_default_plugins = true
  let mut print_theory = false
  let mut print_namespace = false
  let mut output_mode = HumanOutput
  let mut positional_only = false
  let mut index = 2
  while index < arguments.length() {
    let argument = arguments[index]
    if positional_only {
      inputs.push({ file: argument, theories: [] })
      index = index + 1
      continue
    }
    match argument {
      "--" => {
        positional_only = true
        index = index + 1
      }
      "-L" | "--library" | "--loadpath" => {
        loadpaths.push(option_value(arguments, index, argument))
        index = index + 2
      }
      "--no-stdlib" => {
        use_stdlib = false
        index = index + 1
      }
      "-F" | "--format" => {
        format = Some(option_value(arguments, index, argument))
        index = index + 2
      }
      "--parse-only" => {
        if stop_stage == TypeOnly {
          fail_cli(
            InvalidArgument,
            "--parse-only and --type-only are mutually exclusive",
          )
        }
        stop_stage = ParseOnly
        index = index + 1
      }
      "--type-only" => {
        if stop_stage == ParseOnly {
          fail_cli(
            InvalidArgument,
            "--parse-only and --type-only are mutually exclusive",
          )
        }
        stop_stage = TypeOnly
        index = index + 1
      }
      "-T" | "--theory" => {
        add_theory_selection(inputs, option_value(arguments, index, argument))
        index = index + 2
      }
      "-G" | "--goal" => {
        add_goal_selection(inputs, option_value(arguments, index, argument))
        index = index + 2
      }
      "-g" | "--sub-goal" => {
        sub_goals.push(parse_sub_goal(option_value(arguments, index, argument)))
        index = index + 2
      }
      "--goal-index" => {
        goal_index = Some(
          parse_nonnegative_integer(
            option_value(arguments, index, argument),
            "--goal-index",
          ),
        )
        index = index + 2
      }
      "-o" | "--output" => {
        output_directory = Some(option_value(arguments, index, argument))
        index = index + 2
      }
      "-P" | "--prover" => {
        prover = option_value(arguments, index, argument)
        prover_explicit = true
        index = index + 2
      }
      "-D" | "--driver" => {
        if driver is Some(_) {
          fail_cli(
            UnsupportedCliFeature,
            "extra driver layering is outside the pinned Z3 closure",
          )
        }
        driver = Some(option_value(arguments, index, argument))
        index = index + 2
      }
      "-a" | "--apply-transform" => {
        transforms.push(option_value(arguments, index, argument))
        index = index + 2
      }
      "-M" | "--meta" => {
        metas.push(option_value(arguments, index, argument))
        index = index + 2
      }
      "--z3" => {
        z3 = Some(@utf8.encode(option_value(arguments, index, argument)))
        index = index + 2
      }
      "-t" | "--timelimit" => {
        let parsed = parse_nonnegative_seconds(
          option_value(arguments, index, argument),
          argument,
        )
        requested_solver_seconds = parsed.0
        solver_seconds = parsed.1
        solver_limit_explicit = true
        index = index + 2
      }
      "-s" | "--stepslimit" => {
        steps_limit = parse_nonnegative_integer(
          option_value(arguments, index, argument),
          argument,
        )
        index = index + 2
      }
      "-m" | "--memlimit" => {
        memory_limit_mib = parse_nonnegative_integer(
          option_value(arguments, index, argument),
          argument,
        )
        memory_limit_explicit = true
        index = index + 2
      }
      "-C" | "--config" => {
        config = Some(option_value(arguments, index, argument))
        index = index + 2
      }
      "--extra-config" => {
        extra_configs.push(option_value(arguments, index, argument))
        index = index + 2
      }
      "--no-load-default-plugins" => {
        load_default_plugins = false
        index = index + 1
      }
      "--print-theory" => {
        print_theory = true
        index = index + 1
      }
      "--print-namespace" => {
        print_namespace = true
        index = index + 1
      }
      "--json" => {
        output_mode = set_output_mode(output_mode, JsonOutput)
        index = index + 1
      }
      "--json-model-values" => {
        output_mode = set_output_mode(output_mode, JsonModelValuesOutput)
        index = index + 1
      }
      "--canonical-json" => {
        output_mode = set_output_mode(output_mode, CanonicalJsonOutput)
        index = index + 1
      }
      "--check-ce"
      | "--rac-prover"
      | "--rac-timelimit"
      | "--rac-steplimit"
      | "--ce-log-verbosity" =>
        fail_cli(
          UnsupportedCliFeature,
          "RAC and counterexample execution are outside the supported CLI",
        )
      _ =>
        if argument == "-" || !argument.has_prefix("-") {
          inputs.push({ file: argument, theories: [] })
          index = index + 1
        } else {
          fail_cli(InvalidArgument, "unknown option: " + argument)
        }
    }
  }
  if format is Some(format) && format != "why" && format != "mlw" {
    fail_cli(UnsupportedCliFeature, "only the WhyML input format is supported")
  }
  let options = {
    command,
    inputs,
    loadpaths,
    use_stdlib,
    format,
    stop_stage,
    sub_goals,
    goal_index,
    output_directory,
    prover,
    prover_explicit,
    driver,
    transforms,
    metas,
    z3,
    solver_seconds,
    requested_solver_seconds,
    solver_limit_explicit,
    steps_limit,
    memory_limit_mib,
    memory_limit_explicit,
    config,
    extra_configs,
    load_default_plugins,
    print_theory,
    print_namespace,
    output_mode,
  }
  validate_cli_options(options)
  options
}

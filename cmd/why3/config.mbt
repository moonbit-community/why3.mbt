// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct ParsedConfiguration {
  loadpaths : Array[String]
  solver_seconds : Double?
  memory_limit_mib : Int?
  use_stdlib : Bool?
  z3_executable : Bytes?
  plugins : Array[String]
  load_default_plugins : Bool?
}

///|
fn empty_parsed_configuration() -> ParsedConfiguration {
  {
    loadpaths: [],
    solver_seconds: None,
    memory_limit_mib: None,
    use_stdlib: None,
    z3_executable: None,
    plugins: [],
    load_default_plugins: None,
  }
}

///|
fn config_path_is_absolute(path : StringView) -> Bool {
  if path.is_empty() {
    return false
  }
  path[0] == '/' ||
  path[0] == '\\' ||
  (path.length() >= 3 && path[1] == ':' && (path[2] == '/' || path[2] == '\\'))
}

///|
fn config_directory(path : StringView) -> String {
  let mut separator = -1
  for index, character in path {
    if character == '/' || character == '\\' {
      separator = index
    }
  }
  if separator < 0 {
    "."
  } else if separator == 0 {
    path[:1].to_owned()
  } else {
    path[:separator].to_owned()
  }
}

///|
fn absolute_config_path(path : StringView) -> String {
  if config_path_is_absolute(path) {
    return path.to_owned()
  }
  match @env.current_dir() {
    Some(directory) => directory + "/" + path.to_owned()
    None => path.to_owned()
  }
}

///|
fn config_relative_path(
  configuration_path : StringView,
  value : StringView,
) -> String {
  if config_path_is_absolute(value) {
    value.to_owned()
  } else {
    config_directory(absolute_config_path(configuration_path)) +
    "/" +
    value.to_owned()
  }
}

///|
fn config_unquote(value : StringView) -> String {
  let value = value.trim()
  if value.length() >= 2 &&
    (
      (value[0] == '"' && value[value.length() - 1] == '"') ||
      (value[0] == '\'' && value[value.length() - 1] == '\'')
    ) {
    value[1:value.length() - 1].to_owned()
  } else {
    value.to_owned()
  }
}

///|
fn config_assignment(line : StringView) -> (String, String)? {
  for index, character in line {
    if character == '=' {
      let key = line[:index].trim()
      if key.is_empty() {
        return None
      }
      return Some((key.to_owned(), config_unquote(line[index + 1:])))
    }
  }
  None
}

///|
fn prover_field(
  fields : ArrayView[(String, String)],
  name : StringView,
) -> String? {
  let mut result : String? = None
  for field in fields {
    if field.0[:] == name {
      result = Some(field.1)
    }
  }
  result
}

///|
fn command_executable(command : StringView) -> Bytes? {
  let command = command.trim()
  if command.is_empty() {
    return None
  }
  let (start, quoted) = if command[0] == '\'' {
    (1, true)
  } else if command[0] == '"' {
    (1, true)
  } else {
    (0, false)
  }
  let quote = command[0]
  let mut end = command.length()
  for index = start; index < command.length(); index = index + 1 {
    let character = command[index]
    if quoted {
      if character == quote {
        end = index
        break
      }
    } else if character == ' ' || character == '\t' {
      end = index
      break
    }
  }
  if end == start {
    None
  } else {
    Some(@utf8.encode(command[start:end]))
  }
}

///|
fn parsed_configuration(
  contents : StringView,
  path : String,
) -> ParsedConfiguration raise CliError {
  let loadpaths : Array[String] = []
  let mut solver_seconds : Double? = None
  let mut memory_limit_mib : Int? = None
  let mut use_stdlib : Bool? = None
  let plugins : Array[String] = []
  let mut load_default_plugins : Bool? = None
  let prover_groups : Array[Array[(String, String)]] = []
  let mut section = ""
  let mut prover_index : Int? = None
  for raw_line in contents.split("\n") {
    let line = raw_line.trim()
    if line.is_empty() || line.has_prefix("#") {
      continue
    }
    if line.has_prefix("[") && line.has_suffix("]") {
      section = line[1:line.length() - 1].trim().to_owned()
      if section == "prover" {
        prover_groups.push([])
        prover_index = Some(prover_groups.length() - 1)
      } else {
        prover_index = None
      }
      continue
    }
    guard config_assignment(line) is Some((key, value)) else {
      fail_cli(ConfigurationError, "invalid configuration line in " + path)
    }
    if section == "main" {
      match key {
        "loadpath" => loadpaths.push(config_relative_path(path, value))
        "timelimit" => {
          let parsed = parse_nonnegative_seconds(value, "timelimit")
          solver_seconds = Some(parsed.0)
        }
        "memlimit" =>
          memory_limit_mib = Some(parse_nonnegative_integer(value, "memlimit"))
        "stdlib" =>
          match value {
            "true" => use_stdlib = Some(true)
            "false" => use_stdlib = Some(false)
            _ =>
              fail_cli(
                ConfigurationError,
                "main.stdlib must be true or false in " + path,
              )
          }
        "plugin" => plugins.push(value)
        "load_default_plugins" =>
          match value {
            "true" => load_default_plugins = Some(true)
            "false" => load_default_plugins = Some(false)
            _ =>
              fail_cli(
                ConfigurationError,
                "main.load_default_plugins must be true or false in " + path,
              )
          }
        _ => ()
      }
    } else if prover_index is Some(index) {
      prover_groups[index].push((key, value))
    }
  }
  let mut z3_executable : Bytes? = None
  for fields in prover_groups {
    let name = prover_field(fields, "name")
    let version = prover_field(fields, "version")
    let driver = prover_field(fields, "driver")
    if name is Some("Z3") &&
      version is Some("4.8.12") &&
      driver is Some(driver) &&
      driver_basename(driver) is ("z3_487" | "z3_487.drv") &&
      prover_field(fields, "command") is Some(command) {
      z3_executable = command_executable(command)
    }
  }
  {
    loadpaths,
    solver_seconds,
    memory_limit_mib,
    use_stdlib,
    z3_executable,
    plugins,
    load_default_plugins,
  }
}

///|
fn merge_main_configuration(
  base : ParsedConfiguration,
  main : ParsedConfiguration,
) -> ParsedConfiguration {
  let loadpaths = base.loadpaths.copy()
  loadpaths.push_iter(main.loadpaths.iter())
  let plugins = base.plugins.copy()
  plugins.push_iter(main.plugins.iter())
  {
    loadpaths,
    solver_seconds: match main.solver_seconds {
      Some(value) => Some(value)
      None => base.solver_seconds
    },
    memory_limit_mib: match main.memory_limit_mib {
      Some(value) => Some(value)
      None => base.memory_limit_mib
    },
    use_stdlib: match main.use_stdlib {
      Some(value) => Some(value)
      None => base.use_stdlib
    },
    z3_executable: match main.z3_executable {
      Some(value) => Some(value)
      None => base.z3_executable
    },
    plugins,
    load_default_plugins: match main.load_default_plugins {
      Some(value) => Some(value)
      None => base.load_default_plugins
    },
  }
}

///|
/// Why3 extra configurations prepend their load paths and may add or replace
/// prover declarations. Other `[main]` defaults continue to come from the
/// primary configuration.
fn merge_extra_configuration(
  base : ParsedConfiguration,
  extra : ParsedConfiguration,
) -> ParsedConfiguration {
  let loadpaths = extra.loadpaths.copy()
  loadpaths.push_iter(base.loadpaths.iter())
  let plugins = extra.plugins.copy()
  plugins.push_iter(base.plugins.iter())
  {
    ..base,
    loadpaths,
    z3_executable: match extra.z3_executable {
      Some(value) => Some(value)
      None => base.z3_executable
    },
    plugins,
  }
}

///|
priv struct MainConfigurationSelection {
  path : String?
  required : Bool
}

///|
fn select_main_configuration(
  explicit : String?,
  environment : String?,
  home : String?,
) -> MainConfigurationSelection {
  match explicit {
    Some("") => { path: None, required: false }
    Some(path) => { path: Some(path), required: true }
    None =>
      match environment {
        Some("") => { path: None, required: false }
        Some(path) => { path: Some(path), required: true }
        None =>
          match home {
            Some(home) => { path: Some(home + "/.why3.conf"), required: false }
            None => { path: None, required: false }
          }
      }
  }
}

///|
async fn read_configuration_file(
  path : String,
) -> ParsedConfiguration raise CliError {
  let raw = @fs.read_file(path).binary() catch {
    error =>
      fail_cli(
        ConfigurationError,
        "cannot read Why3 configuration " + path + ": \{error}",
      )
  }
  let text = @utf8.decode(raw) catch {
    _ =>
      fail_cli(
        ConfigurationError,
        "Why3 configuration is not valid UTF-8: " + path,
      )
  }
  parsed_configuration(text, path)
}

///|
async fn read_main_configuration(
  explicit : String?,
) -> ParsedConfiguration raise CliError {
  let home = match @env.get_env_var("HOME") {
    Some(value) => Some(value)
    None => @env.get_env_var("USERPROFILE")
  }
  let selected = select_main_configuration(
    explicit,
    @env.get_env_var("WHY3CONFIG"),
    home,
  )
  match selected.path {
    None => empty_parsed_configuration()
    Some(path) => {
      let exists = if selected.required {
        true
      } else {
        @fs.exists(path) catch {
          error =>
            fail_cli(
              ConfigurationError,
              "cannot inspect Why3 configuration " + path + ": \{error}",
            )
        }
      }
      if exists {
        read_configuration_file(path)
      } else {
        empty_parsed_configuration()
      }
    }
  }
}

///|
fn validate_configuration_plugins(
  configuration : ParsedConfiguration,
  load_default_plugins : Bool,
) -> Unit raise CliError {
  if !configuration.plugins.is_empty() ||
    (load_default_plugins && configuration.load_default_plugins is Some(true)) {
    fail_cli(
      UnsupportedCliFeature,
      "configuration-requested plugins are outside the static Z3 closure",
    )
  }
}

///|
async fn resolve_cli_configuration(
  options : CliOptions,
) -> CliOptions raise CliError {
  let mut parsed = merge_main_configuration(
    empty_parsed_configuration(),
    read_main_configuration(options.config),
  )
  for path in options.extra_configs {
    parsed = merge_extra_configuration(parsed, read_configuration_file(path))
  }
  validate_configuration_plugins(parsed, options.load_default_plugins)
  let loadpaths = options.loadpaths.copy()
  loadpaths.push_iter(parsed.loadpaths.iter())
  let requested_solver_seconds = if options.solver_limit_explicit {
    options.requested_solver_seconds
  } else {
    parsed.solver_seconds.unwrap_or(options.requested_solver_seconds)
  }
  let solver_seconds = requested_solver_seconds.ceil().to_int()
  let memory_limit_mib = if options.memory_limit_explicit {
    options.memory_limit_mib
  } else {
    parsed.memory_limit_mib.unwrap_or(options.memory_limit_mib)
  }
  let z3 = match options.z3 {
    Some(value) => Some(value)
    None => parsed.z3_executable
  }
  ignore(options.format)
  {
    ..options,
    loadpaths,
    use_stdlib: options.use_stdlib && parsed.use_stdlib.unwrap_or(true),
    load_default_plugins: options.load_default_plugins &&
    parsed.load_default_plugins.unwrap_or(true),
    requested_solver_seconds,
    solver_seconds,
    memory_limit_mib,
    z3,
  }
}

///|
fn driver_basename(path : StringView) -> StringView {
  let mut start = 0
  for index, character in path {
    if character == '/' || character == '\\' {
      start = index + 1
    }
  }
  path[start:]
}

///|
fn transform_name(value : StringView) -> StringView {
  for index, character in value {
    if character == ' ' || character == '\t' {
      return value[:index]
    }
  }
  value
}

///|
fn known_transform(value : StringView) -> Bool {
  match transform_name(value) {
    "counterexamples_dependent_intros"
    | "inline_trivial"
    | "eliminate_builtin"
    | "remove_unused_keep_constants"
    | "detect_polymorphism"
    | "eliminate_definition_conditionally"
    | "eliminate_inductive"
    | "eliminate_epsilon"
    | "eliminate_literal"
    | "simplify_formula"
    | "prepare_for_counterexmp"
    | "eliminate_projections_sums"
    | "discriminate_if_poly"
    | "eliminate_algebraic_if_poly"
    | "encoding_smt_if_poly" => true
    _ => false
  }
}

///|
fn cli_transform_names(options : CliOptions) -> Array[Bytes] {
  [
    for transform in options.transforms => {
      @utf8.encode(transform_name(transform))
    }
  ]
}

///|
fn meta_parts(value : String) -> (StringView, StringView?) {
  for index, character in value {
    if character == '=' {
      return (value[:index], Some(value[index + 1:]))
    }
  }
  (value[:], None)
}

///|
fn string_meta_name(name : StringView) -> Bool {
  match name {
    "printer_option"
    | "select_inst"
    | "select_lskept"
    | "select_lsinst"
    | "select_alginst"
    | "select_inst_default"
    | "select_lskept_default"
    | "select_lsinst_default"
    | "select_alginst_default"
    | "select_kept"
    | "select_kept_default"
    | "enco_kept"
    | "enco_poly"
    | "vc_location"
    | "lift_epsilon"
    | "eliminate_algebraic" => true
    _ => false
  }
}

///|
fn nonexclusive_string_meta(name : StringView) -> Bool {
  name == "printer_option" || name == "eliminate_algebraic"
}

///|
fn no_argument_meta_name(name : StringView) -> Bool {
  match name {
    "get_counterexmp"
    | "counterexample_need_smtlib_push"
    | "meta_incremental"
    | "supports_smtlib_minimize"
    | "supports_smt_get_info_unknown_reason"
    | "encoding:monomorphic_only"
    | "begin_compute_context" => true
    _ => false
  }
}

///|
fn cli_metas(options : CliOptions) -> Array[@theory.Meta] raise CliError {
  let result : Array[@theory.Meta] = []
  for value in options.metas {
    let (name, argument) = meta_parts(value)
    if name.is_empty() {
      fail_cli(InvalidArgument, "-M/--meta name is empty")
    }
    let encoded_name = @utf8.encode(name)
    match argument {
      None =>
        if no_argument_meta_name(name) {
          result.push(@theory.Meta::exclusive(encoded_name, []))
        } else {
          fail_cli(
            InvalidArgument,
            "meta requires an argument or is unknown: " + name.to_owned(),
          )
        }
      Some(argument) =>
        if name == "compute_max_domain_size" {
          result.push(
            @theory.Meta::exclusive(encoded_name, [
              @theory.MetaInteger(
                parse_nonnegative_integer(argument, "-M/--meta").to_int64(),
              ),
            ]),
          )
        } else if string_meta_name(name) {
          let arguments = [@theory.MetaString(@utf8.encode(argument))]
          result.push(
            if nonexclusive_string_meta(name) {
              @theory.Meta::new(encoded_name, arguments)
            } else {
              @theory.Meta::exclusive(encoded_name, arguments)
            },
          )
        } else {
          fail_cli(
            UnsupportedCliFeature,
            "unknown or non-CLI meta: " + name.to_owned(),
          )
        }
    }
  }
  result
}

///|
fn validate_driver_and_task_options(
  options : CliOptions,
) -> Unit raise CliError {
  if options.driver is Some(path) {
    let basename = driver_basename(path)
    if basename != "z3_487" && basename != "z3_487.drv" {
      fail_cli(
        UnsupportedCliFeature,
        "only the pinned z3_487 driver closure is supported",
      )
    }
  }
  for transform in options.transforms {
    if !known_transform(transform) {
      fail_cli(
        UnsupportedCliFeature,
        "unknown or unsupported transform: " + transform,
      )
    }
    if transform_name(transform).length() != transform.length() {
      fail_cli(
        UnsupportedCliFeature,
        "arguments for this transform are not supported: " + transform,
      )
    }
  }
  ignore(cli_metas(options))
}

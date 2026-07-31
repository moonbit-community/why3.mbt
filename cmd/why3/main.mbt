// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
extern "C" fn exit_process(code : Int) -> Unit = "exit"

///|
fn final_qualified_segment(value : BytesView) -> BytesView {
  let mut start = 0
  for index, byte in value {
    if byte == b'.' {
      start = index + 1
    }
  }
  value[start:]
}

///|
fn selected_name_matches(actual : BytesView, requested : BytesView) -> Bool {
  actual == requested || actual == final_qualified_segment(requested)
}

///|
fn ascii_equal_ignoring_case(left : BytesView, right : BytesView) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for index = 0; index < left.length(); index = index + 1 {
    let left = if left[index] >= b'A' && left[index] <= b'Z' {
      left[index] + 32
    } else {
      left[index]
    }
    let right = if right[index] >= b'A' && right[index] <= b'Z' {
      right[index] + 32
    } else {
      right[index]
    }
    if left != right {
      return false
    }
  }
  true
}

///|
fn diagnostic_location(span : @identity.SourceSpan?) -> String {
  match span {
    None => ""
    Some(span) => {
      let view = span.view()
      display_bytes(view.relative_path) +
      ":" +
      view.start_line.to_string() +
      ":" +
      view.start_column.to_string() +
      ": "
    }
  }
}

///|
fn matches_sub_goal(
  info : @z3.GoalInfoView,
  selector : CliSubGoal,
  default_file : String,
) -> Bool {
  let span = info.origin.source_span()
  if selector.file is Some(requested_file) {
    let requested_file = if requested_file.is_empty() {
      default_file
    } else {
      requested_file
    }
    guard span is Some(span) else { return false }
    if span.view().relative_path != @utf8.encode(requested_file) {
      return false
    }
  }
  if selector.line is Some(requested_line) {
    guard span is Some(span) else { return false }
    let view = span.view()
    if requested_line < view.start_line || requested_line > view.end_line {
      return false
    }
  }
  if selector.explanation is Some(requested) {
    let mut found = false
    for attribute in info.expl_attributes {
      let explanation = if attribute.has_prefix(b"expl:") {
        attribute[5:]
      } else {
        attribute[:]
      }
      if ascii_equal_ignoring_case(explanation, requested) {
        found = true
        break
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
fn selected_goal_indices(
  infos : ArrayView[@z3.GoalInfo],
  input : CliInput,
  options : CliOptions,
) -> Array[Int] raise CliError {
  let candidates : Array[Int] = []
  for index, info in infos {
    let view = info.view()
    let mut selected_by_name = input.theories.is_empty()
    for theory in input.theories {
      if selected_name_matches(view.unit_name, theory.name) &&
        (
          theory.goals.is_empty() ||
          theory.goals.any(goal => {
            selected_name_matches(view.goal.view().name, goal)
          })
        ) {
        selected_by_name = true
        break
      }
    }
    if !selected_by_name {
      continue
    }
    if !options.sub_goals.is_empty() &&
      !options.sub_goals.any(selector => {
        matches_sub_goal(view, selector, input.file)
      }) {
      continue
    }
    candidates.push(index)
  }
  let selected = match options.goal_index {
    None => candidates
    Some(index) => {
      if index < 0 || index >= candidates.length() {
        fail_cli(SelectionError, "--goal-index does not select a source goal")
      }
      [candidates[index]]
    }
  }
  if selected.is_empty() {
    fail_cli(SelectionError, "goal selector matched no source goal")
  }
  selected
}

///|
async fn run_check(
  checked : @pipeline.CheckedFile,
  options : CliOptions,
  input : CliInput,
  fixture : BytesView,
  source : BytesView,
) -> Int {
  match options.output_mode {
    HumanOutput =>
      @stdio.stdout.write(
        input.file +
        ": checked " +
        checked.typed_units().length().to_string() +
        " unit(s)\n",
      )
    CanonicalJsonOutput =>
      for unit in checked.typed_units() {
        match unit {
          Theory(theory) =>
            write_bytes_stdout(
              @canonical.encode_typed_theory_record(fixture, source, theory),
            )
          Module(pmodule) =>
            write_bytes_stdout(
              @canonical.encode_typed_module_record(fixture, source, pmodule),
            )
        }
      }
    JsonOutput | JsonModelValuesOutput =>
      for unit in checked.typed_units() {
        let (kind, unit_name, items) = match unit {
          Theory(theory) =>
            ("theory", theory.view().name.view().name, theory.view().items)
          Module(pmodule) =>
            (
              "module",
              pmodule.pure_theory().view().name.view().name,
              pmodule.pure_theory().view().items,
            )
        }
        let mut ordinal = 0
        for item in items {
          if item is TheoryDecl(declaration) &&
            declaration.view() is Dprop(kind_, proposition, _) &&
            (kind_ == Plemma || kind_ == Pgoal) {
            @stdio.stdout.write(
              "{\"schema\":1,\"stage\":\"check\",\"unit_kind\":\"" +
              kind +
              "\",\"unit_name_hex\":\"" +
              bytes_hex_string(unit_name) +
              "\",\"goal_name_hex\":\"" +
              bytes_hex_string(proposition.view().name) +
              "\",\"goal_ordinal\":" +
              ordinal.to_string() +
              ",\"status\":\"checked\"}\n",
            )
            ordinal = ordinal + 1
          }
        }
      }
  }
  0
}

///|
async fn run_task(
  checked : @pipeline.CheckedFile,
  options : CliOptions,
  input : CliInput,
  fixture : BytesView,
  source : BytesView,
) -> Int {
  let tasked = @pipeline.tasks(checked)
  let infos = tasked.goal_infos()
  let selected = selected_goal_indices(infos, input, options)
  for index in selected {
    let info = infos[index].view()
    match options.output_mode {
      HumanOutput =>
        @stdio.stdout.write(
          display_bytes(info.unit_name) +
          "." +
          display_bytes(info.goal.view().name) +
          ": task ready\n",
        )
      JsonOutput | JsonModelValuesOutput =>
        @stdio.stdout.write(
          goal_json_prefix(info, "task") + ",\"status\":\"ready\"}\n",
        )
      CanonicalJsonOutput =>
        write_bytes_stdout(
          @canonical.encode_raw_task_record(
            fixture,
            source,
            info.unit_name,
            info.ordinal,
            tasked.raw_goals()[index],
          ),
        )
    }
  }
  0
}

///|
async fn write_smt_files(
  calls : ArrayView[@z3.PreparedCall],
  selected : ArrayView[Int],
  directory : String,
  filename_prefix? : String = "",
) -> Unit {
  let outputs : Array[(Int, String)] = []
  for index in selected {
    let info = calls[index].goal_info().view()
    let filename = filename_prefix +
      six_digit_ordinal(info.ordinal) +
      "-" +
      bytes_hex_string(info.goal.view().name) +
      ".smt2"
    for output in outputs {
      if output.1 == filename {
        fail_cli(
          OutputError,
          "selected goals map to the same SMT output filename: " + filename,
        )
      }
    }
    outputs.push((index, filename))
  }
  if !@fs.exists(directory) {
    @fs.mkdir(directory, recursive=true) catch {
      err => fail_cli(OutputError, "cannot create SMT output directory: \{err}")
    }
  }
  for output in outputs {
    let index = output.0
    let call = calls[index]
    @fs.write_file(
      directory + "/" + output.1,
      call.query().bytes(),
      create_mode=CreateOrTruncate,
    ) catch {
      err => fail_cli(OutputError, "cannot write SMT output: \{err}")
    }
  }
}

///|
async fn run_emit_smt(
  checked : @pipeline.CheckedFile,
  options : CliOptions,
  input : CliInput,
  input_index : Int,
  fixture : BytesView,
  source : BytesView,
) -> Int {
  let calls = @pipeline.prepare_proof(
    checked,
    transforms=cli_transform_names(options),
    metas=cli_metas(options),
  )
  let infos = [ for call in calls => call.goal_info() ]
  let selected = selected_goal_indices(infos, input, options)
  if selected.length() > 1 && options.output_directory is None {
    fail_cli(
      OutputError,
      "emit-smt requires -o DIR when more than one goal is selected",
    )
  }
  if options.output_directory is Some(directory) {
    write_smt_files(
      calls,
      selected,
      directory,
      filename_prefix=if options.inputs.length() > 1 {
        six_digit_ordinal(input_index) + "-"
      } else {
        ""
      },
    )
  }
  for index in selected {
    let call = calls[index]
    let info = call.goal_info().view()
    match options.output_mode {
      HumanOutput =>
        match options.output_directory {
          None => write_bytes_stdout(call.query().bytes())
          Some(_) =>
            @stdio.stdout.write(
              display_bytes(info.unit_name) +
              "." +
              display_bytes(info.goal.view().name) +
              ": SMT emitted\n",
            )
        }
      JsonOutput | JsonModelValuesOutput =>
        @stdio.stdout.write(
          goal_json_prefix(info, "emit-smt") +
          ",\"smt_hex\":\"" +
          bytes_hex_string(call.query().bytes()) +
          "\"}\n",
        )
      CanonicalJsonOutput =>
        write_bytes_stdout(
          @canonical.encode_prepared_call_record(fixture, source, call),
        )
    }
  }
  0
}

///|
async fn run_prove(
  checked : @pipeline.CheckedFile,
  options : CliOptions,
  input : CliInput,
  input_index : Int,
  fixture : BytesView,
  source : BytesView,
) -> Int {
  ignore(options.prover)
  let request_model = options.output_mode == JsonModelValuesOutput ||
    options.metas.any(value => meta_parts(value).0 == "get_counterexmp")
  let calls = @pipeline.prepare_proof(
    checked,
    solver_seconds=options.solver_seconds,
    steps_limit=options.steps_limit,
    memory_limit_mib=options.memory_limit_mib,
    executable_request=options.z3.map(value => value[:]),
    transforms=cli_transform_names(options),
    metas=cli_metas(options),
    request_model~,
  )
  let infos = [ for call in calls => call.goal_info() ]
  let selected = selected_goal_indices(infos, input, options)
  if options.output_directory is Some(directory) {
    write_smt_files(
      calls,
      selected,
      directory,
      filename_prefix=if options.inputs.length() > 1 {
        six_digit_ordinal(input_index) + "-"
      } else {
        ""
      },
    )
    return 0
  }
  if options.driver is Some(_) {
    for index in selected {
      write_bytes_stdout(calls[index].query().bytes())
    }
    return 0
  }
  let runner = @native.NativeRunner::new(calls[selected[0]].command())
  let mut classified_nonvalid = false
  for index in selected {
    let call = calls[index]
    let (result, model_values) = match runner.run(call.query().bytes()) {
      ParentDeadlineExceeded => (@prover.Timeout, [])
      Completed(raw) => {
        let result = @z3.parse_result(raw)
        let model_values = if request_model && result != @prover.Valid {
          @z3.parse_smtv2_model_for_query(call.query(), raw.view().stdout)
        } else {
          []
        }
        (result, model_values)
      }
    }
    if result != @prover.Valid {
      classified_nonvalid = true
    }
    let info = call.goal_info().view()
    match options.output_mode {
      HumanOutput =>
        @stdio.stdout.write(
          display_bytes(info.unit_name) +
          "." +
          display_bytes(info.goal.view().name) +
          ": " +
          prover_result_human(result) +
          "\n",
        )
      JsonOutput | JsonModelValuesOutput =>
        @stdio.stdout.write(
          goal_json_prefix(info, "prove") +
          ",\"result\":" +
          prover_result_json(result) +
          (if request_model {
            ",\"model_values\":" + model_values_json(model_values)
          } else {
            ""
          }) +
          "}\n",
        )
      CanonicalJsonOutput =>
        write_bytes_stdout(
          @canonical.encode_prover_result_record(
            fixture,
            source,
            call.goal_info(),
            result,
          ),
        )
    }
  }
  if classified_nonvalid {
    2
  } else {
    0
  }
}

///|
async fn read_cli_input(input : CliInput) -> (Bytes, Bytes) {
  if input.file == "-" {
    (@stdio.stdin.read_all().binary(), b"stdin")
  } else {
    (@fs.read_file(input.file).binary(), @utf8.encode(input.file))
  }
}

///|
async fn print_typed_units(
  checked : @pipeline.CheckedFile,
  input : CliInput,
  options : CliOptions,
) -> Unit {
  if !options.print_theory && !options.print_namespace {
    return
  }
  for unit in checked.typed_units() {
    let (kind, theory) = match unit {
      Theory(theory) => ("theory", theory)
      Module(pmodule) => ("module", pmodule.pure_theory())
    }
    let name = theory.view().name.view().name
    let mut selected = input.theories.is_empty()
    for selection in input.theories {
      if selected_name_matches(name, selection.name) {
        selected = true
        break
      }
    }
    if selected {
      if options.print_theory {
        @stdio.stdout.write(
          kind +
          " " +
          display_bytes(name) +
          " (" +
          theory.view().items.length().to_string() +
          " items)\n",
        )
      } else {
        let namespace_view = theory.export_namespace().view()
        @stdio.stdout.write(
          kind +
          " " +
          display_bytes(name) +
          ": " +
          namespace_view.types.length().to_string() +
          " type(s), " +
          namespace_view.logic.length().to_string() +
          " logic symbol(s), " +
          namespace_view.propositions.length().to_string() +
          " proposition(s)\n",
        )
      }
    }
  }
}

///|
async fn run_cli(arguments : ArrayView[String]) -> Int {
  let options = resolve_cli_configuration(parse_arguments(arguments))
  validate_driver_and_task_options(options)
  let providers : Array[@source_env.SourceProvider] = []
  for loadpath in options.loadpaths {
    providers.push(loadpath_source_provider(loadpath))
  }
  if options.use_stdlib {
    providers.push(@stdlib.embedded_source_provider())
  }
  let environment = @environment.Environment::with_source(
    @source_env.SourceProvider::combine(providers),
  )
  let loaded_paths : Array[String] = []
  let loaded_sources : Array[Bytes] = []
  let loaded_fixtures : Array[Bytes] = []
  let loaded_checked : Array[@pipeline.CheckedFile] = []
  let mut exit_code = 0
  for input_index, input in options.inputs {
    if options.stop_stage == ParseOnly {
      let (source, fixture) = read_cli_input(input)
      ignore(@parser.parse_mlw_file(source, filename=fixture))
      continue
    }
    let mut cached_index = -1
    if input.file != "-" {
      for index, path in loaded_paths {
        if path == input.file {
          cached_index = index
          break
        }
      }
    }
    let (source, fixture, checked) = if cached_index >= 0 {
      (
        loaded_sources[cached_index],
        loaded_fixtures[cached_index],
        loaded_checked[cached_index],
      )
    } else {
      let (source, fixture) = read_cli_input(input)
      let checked = @pipeline.check_with_environment(
        source,
        environment,
        filename=fixture,
      )
      if input.file != "-" {
        loaded_paths.push(input.file)
        loaded_sources.push(source)
        loaded_fixtures.push(fixture)
        loaded_checked.push(checked)
      }
      (source, fixture, checked)
    }
    print_typed_units(checked, input, options)
    if options.stop_stage == TypeOnly ||
      options.print_theory ||
      options.print_namespace {
      continue
    }
    let code = match options.command {
      CheckCommand => run_check(checked, options, input, fixture, source)
      TaskCommand => run_task(checked, options, input, fixture, source)
      EmitSmtCommand =>
        run_emit_smt(checked, options, input, input_index, fixture, source)
      ProveCommand =>
        run_prove(checked, options, input, input_index, fixture, source)
    }
    if code == 2 {
      exit_code = 2
    } else if code != 0 && exit_code == 0 {
      exit_code = code
    }
  }
  exit_code
}

///|
async fn main {
  let code = try {
    validate_file_argument_utf8()
    run_cli(@env.args())
  } catch {
    CliError(diagnostic) => {
      @stdio.stderr.write("why3mbt: " + diagnostic.message + "\n")
      1
    }
    @prover.ConfigError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: ConfigError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @parser.ParseError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: ParseError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @elab.ElabError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: " +
        diagnostic_location(diagnostic.span) +
        "ElabError(" +
        @debug.to_string(diagnostic.stage) +
        "," +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @vc.VcError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: VcError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @z3.BindError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: BindError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @transform.TransformError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: TransformError(" +
        @debug.to_string(diagnostic.stage) +
        "," +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @smtv2.PrinterError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: PrinterError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @prover.ProcessError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: ProcessError(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @prover.MalformedProverOutput(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: MalformedProverOutput(" +
        @debug.to_string(diagnostic.kind) +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @z3.ModelParseError(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: ModelParseError(" +
        @debug.to_string(diagnostic.kind) +
        "," +
        diagnostic.byte_offset.to_string() +
        "): " +
        diagnostic.message +
        "\n",
      )
      1
    }
    @prover.OutputLimitExceeded(diagnostic) => {
      @stdio.stderr.write(
        "why3mbt: OutputLimitExceeded(" +
        @debug.to_string(diagnostic.stream) +
        "," +
        diagnostic.limit_bytes.to_string() +
        ")\n",
      )
      1
    }
    err => {
      @stdio.stderr.write("why3mbt: " + @debug.to_string(err) + "\n")
      1
    }
  }
  exit_process(code)
}

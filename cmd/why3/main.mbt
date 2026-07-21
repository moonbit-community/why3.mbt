// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
extern "C" fn exit_process(code : Int) -> Unit = "exit"

///|
fn selected_goal_indices(
  infos : ArrayView[@z3.GoalInfo],
  options : CliOptions,
) -> Array[Int] raise CliError {
  let candidates : Array[Int] = []
  for index, info in infos {
    let view = info.view()
    if options.theory is Some(theory) && view.unit_name != theory {
      continue
    }
    if options.goal is Some(goal) && view.goal.view().name != goal {
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
  fixture : BytesView,
  source : BytesView,
) -> Int {
  match options.output_mode {
    HumanOutput =>
      @stdio.stdout.write(
        options.file +
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
    JsonOutput =>
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
  fixture : BytesView,
  source : BytesView,
) -> Int {
  let tasked = @pipeline.tasks(checked)
  let infos = tasked.goal_infos()
  let selected = selected_goal_indices(infos, options)
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
      JsonOutput =>
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
) -> Unit {
  let outputs : Array[(Int, String)] = []
  for index in selected {
    let info = calls[index].goal_info().view()
    let filename = six_digit_ordinal(info.ordinal) +
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
  fixture : BytesView,
  source : BytesView,
) -> Int {
  let calls = @pipeline.prepare_proof(checked)
  let infos = [ for call in calls => call.goal_info() ]
  let selected = selected_goal_indices(infos, options)
  if selected.length() > 1 && options.output_directory is None {
    fail_cli(
      OutputError,
      "emit-smt requires -o DIR when more than one goal is selected",
    )
  }
  if options.output_directory is Some(directory) {
    write_smt_files(calls, selected, directory)
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
      JsonOutput =>
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
  fixture : BytesView,
  source : BytesView,
) -> Int {
  ignore(options.prover)
  let calls = @pipeline.prepare_proof(
    checked,
    solver_seconds=options.solver_seconds,
    executable_request=options.z3.map(value => value[:]),
  )
  let infos = [ for call in calls => call.goal_info() ]
  let selected = selected_goal_indices(infos, options)
  let runner = @native.NativeRunner::new(calls[selected[0]].command())
  let mut classified_nonvalid = false
  for index in selected {
    let call = calls[index]
    let result = match runner.run(call.query().bytes()) {
      ParentDeadlineExceeded => @prover.Timeout
      Completed(raw) => @z3.parse_result(raw)
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
      JsonOutput =>
        @stdio.stdout.write(
          goal_json_prefix(info, "prove") +
          ",\"result\":" +
          prover_result_json(result) +
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
async fn run_cli(arguments : ArrayView[String]) -> Int {
  let options = parse_arguments(arguments)
  let source = @fs.read_file(options.file).binary()
  let fixture = @utf8.encode(options.file)
  let checked = @pipeline.check(source, filename=fixture)
  match options.command {
    CheckCommand => run_check(checked, options, fixture, source)
    TaskCommand => run_task(checked, options, fixture, source)
    EmitSmtCommand => run_emit_smt(checked, options, fixture, source)
    ProveCommand => run_prove(checked, options, fixture, source)
  }
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
        "why3mbt: ElabError(" +
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

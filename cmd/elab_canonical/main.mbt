// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
extern "C" fn exit_process(code : Int) -> Unit = "exit"

///|
async fn fail_command(message : String) -> Unit {
  @stdio.stderr.write("elab_canonical: " + message + "\n")
  exit_process(1)
}

///|
fn valid_fixture_path(path : StringView) -> Bool {
  if path.is_empty() || path[0] == '/' || path.contains("\\") {
    return false
  }
  let segments = path.split("/")
  !segments.any(segment => segment == "" || segment == "..")
}

///|
fn source_file_parts(name : BytesView) -> (Bytes, Bytes)? {
  if name.length() > 4 && name.has_suffix(b".mlw") {
    Some((name[0:name.length() - 4].to_owned(), b"mlw"))
  } else if name.length() > 4 && name.has_suffix(b".why") {
    Some((name[0:name.length() - 4].to_owned(), b"why"))
  } else {
    None
  }
}

///|
fn relative_directory_segments(
  root : BytesView,
  directory : BytesView,
) -> Array[Bytes] {
  if !directory.has_prefix(root) {
    abort("filesystem traversal escaped its loadpath root")
  }
  let mut start = root.length()
  while start < directory.length() &&
        (directory[start] == b'/' || directory[start] == b'\\') {
    start = start + 1
  }
  let segments : Array[Bytes] = []
  let mut segment_start = start
  for index = start; index < directory.length(); index = index + 1 {
    if directory[index] == b'/' || directory[index] == b'\\' {
      if index > segment_start {
        segments.push(directory[segment_start:index].to_owned())
      }
      segment_start = index + 1
    }
  }
  if segment_start < directory.length() {
    segments.push(directory[segment_start:].to_owned())
  }
  segments
}

///|
fn canonical_path_directory(path : StringView) -> String {
  let mut separator = -1
  for index, character in path {
    if character == '/' || character == '\\' {
      separator = index
    }
  }
  if separator < 0 {
    ""
  } else if separator == 0 {
    path[:1].to_owned()
  } else {
    path[:separator].to_owned()
  }
}

///|
async fn loadpath_source_provider(
  requested_root : String,
  canonical_root : Bytes?,
) -> @source_env.SourceProvider {
  let root = @fs.realpath(requested_root)
  let physical_root = @utf8.encode(root)
  let provider_root = match canonical_root {
    Some(root) => root
    None => physical_root
  }
  let sources : Array[@source_env.MemorySource] = []
  @fs.walk(root, max_concurrency=1, (directory, entries) => {
    let directory_bytes = @utf8.encode(directory)
    let prefix = relative_directory_segments(physical_root, directory_bytes)
    for entry in entries {
      let entry_bytes = @utf8.encode(entry)
      if source_file_parts(entry_bytes) is Some((stem, extension)) {
        let path_segments = prefix.copy()
        path_segments.push(stem)
        let library_path = @source_env.LibraryPath::new(path_segments)
        let separator = if directory.has_suffix("/") { "" } else { "/" }
        let filename = directory + separator + entry
        let contents = @fs.read_file(filename).binary()
        sources.push(
          @source_env.MemorySource::new(library_path, extension, contents),
        )
      }
    }
  })
  @source_env.SourceProvider::memory(provider_root, sources)
}

///|
async fn write_record(record : BytesView) -> Unit {
  let text = @utf8.decode(record) catch {
    _ => abort("portable canonical record is not valid UTF-8")
  }
  @stdio.stdout.write(text)
}

///|
async fn write_checkpoint_record(
  fixture : BytesView,
  source : BytesView,
  unit_name : BytesView,
  goal_name : BytesView,
  ordinal : Int,
  stage : BytesView,
  task : @theory.Task,
) -> Unit {
  write_record(
    @canonical.encode_task_checkpoint_record(
      fixture, source, unit_name, goal_name, ordinal, stage, task,
    ),
  )
}

///|
async fn write_smt_record(
  fixture : BytesView,
  source : BytesView,
  unit_name : BytesView,
  goal_name : BytesView,
  ordinal : Int,
  stream : @smtv2.NormalizedSmtTokens,
) -> Unit {
  write_record(
    @canonical.encode_smt_token_record(
      fixture, source, unit_name, goal_name, ordinal, stream,
    ),
  )
}

///|
async fn write_smt_query(
  unit_name : BytesView,
  goal_name : BytesView,
  ordinal : Int,
  query : @smtv2.SmtQuery,
) -> Unit {
  @stdio.stdout.write(
    "{\"unit_name_hex\":\"" +
    bytes_hex_string(unit_name) +
    "\",\"goal_name_hex\":\"" +
    bytes_hex_string(goal_name) +
    "\",\"goal_ordinal\":" +
    ordinal.to_string() +
    ",\"smt_hex\":\"" +
    bytes_hex_string(query.bytes()) +
    "\"}\n",
  )
}

///|
fn bytes_hex_string(bytes : BytesView) -> String {
  @utf8.decode(@canonical.bytes_to_lower_hex(bytes)) catch {
    _ => abort("hex output is not valid UTF-8")
  }
}

///|
fn diagnostic_stage_name(stage : @elab.ElabStage) -> String {
  match stage {
    DeclarationElaboration => "declaration-elaboration"
    PureTyping => "typing"
    ProgramTyping => "program-typing"
    FileRegistration => "file-registration"
  }
}

///|
fn input_error_name(kind : @elab.ElabInputErrorKind) -> String {
  match kind {
    InvalidBinder => "InvalidBinder"
    InvalidDeclaration => "InvalidDeclaration"
    InvalidPattern => "InvalidPattern"
    InvalidSpecification => "InvalidSpecification"
    InvalidTypeDeclaration => "InvalidTypeDeclaration"
    InvalidUnit => "InvalidUnit"
  }
}

///|
fn diagnostic_kind_name(kind : @elab.ElabErrorKind) -> String {
  match kind {
    TypeFailure(ArityMismatch) => "TypeError(ArityMismatch)"
    TypeFailure(TypeMismatch) => "TypeError(TypeMismatch)"
    TypeFailure(OccursCheck) => "TypeError(OccursCheck)"
    TypeFailure(PolymorphicProgramRoutine) =>
      "TypeError(PolymorphicProgramRoutine)"
    InvalidInput(input) => "InputError(" + input_error_name(input) + ")"
    TypeFailure(_) => "TypeError(Other)"
    TheoryFailure(_) => "TheoryError(Other)"
    EnvironmentFailure(ResolveError) => "EnvironmentError(ResolveError)"
    EnvironmentFailure(_) => "EnvironmentError(Other)"
    SourceFailure(_) => "SourceError(Other)"
    ProgramFailure(_) => "ProgramError(Other)"
  }
}

///|
fn optional_hex(value : Bytes?) -> String {
  match value {
    None => "null"
    Some(bytes) => "\"" + bytes_hex_string(bytes) + "\""
  }
}

///|
async fn write_diagnostic(diagnostic : @elab.ElabDiagnostic) -> Unit {
  let location = match diagnostic.span {
    None =>
      "\"relative_path_hex\":null,\"start_byte\":null,\"end_byte\":null," +
      "\"start_line\":null,\"start_column\":null,\"end_line\":null," +
      "\"end_column\":null"
    Some(span) => {
      let view = span.view()
      "\"relative_path_hex\":\"" +
      bytes_hex_string(view.relative_path) +
      "\",\"start_byte\":" +
      view.start_byte.to_string() +
      ",\"end_byte\":" +
      view.end_byte.to_string() +
      ",\"start_line\":" +
      view.start_line.to_string() +
      ",\"start_column\":" +
      view.start_column.to_string() +
      ",\"end_line\":" +
      view.end_line.to_string() +
      ",\"end_column\":" +
      view.end_column.to_string()
    }
  }
  @stdio.stdout.write(
    "{\"accepted\":false,\"stage\":\"" +
    diagnostic_stage_name(diagnostic.stage) +
    "\",\"kind\":\"" +
    diagnostic_kind_name(diagnostic.kind) +
    "\"," +
    location +
    ",\"actual_type_hex\":" +
    optional_hex(diagnostic.actual_type) +
    ",\"expected_type_hex\":" +
    optional_hex(diagnostic.expected_type) +
    "}\n",
  )
}

///|
fn transform_stage_rank(stage : String) -> Int {
  match stage {
    "driver-update" => 0
    "counterexamples_dependent_intros" => 1
    "inline_trivial" => 2
    "eliminate_builtin" => 3
    "remove_unused_keep_constants" => 4
    "detect_polymorphism" => 5
    "eliminate_definition_conditionally" => 6
    "eliminate_inductive" => 7
    "eliminate_epsilon" => 8
    "eliminate_literal" => 9
    "simplify_formula" => 10
    "prepare_for_counterexmp" => 11
    "eliminate_projections_sums" => 12
    "discriminate_if_poly:monomorphise_goal" => 13
    "discriminate_if_poly" => 14
    "eliminate_algebraic_if_poly" => 15
    "encoding_smt_if_poly:monomorphise_goal" => 16
    "encoding_smt_if_poly:select_kept" => 17
    "encoding_smt_if_poly:keep_field_types" => 18
    "encoding_smt_if_poly:twin" => 19
    "encoding_smt_if_poly:guards" => 20
    "encoding_smt_if_poly" => 21
    "prepared-task" => 21
    "smt-tokens" => 22
    "smt-query" => 22
    _ => -1
  }
}

///|
fn transform_stage_bytes(stage : String) -> BytesView {
  match stage {
    "driver-update" => b"driver-update"
    "counterexamples_dependent_intros" => b"counterexamples_dependent_intros"
    "inline_trivial" => b"inline_trivial"
    "eliminate_builtin" => b"eliminate_builtin"
    "remove_unused_keep_constants" => b"remove_unused_keep_constants"
    "detect_polymorphism" => b"detect_polymorphism"
    "eliminate_definition_conditionally" =>
      b"eliminate_definition_conditionally"
    "eliminate_inductive" => b"eliminate_inductive"
    "eliminate_epsilon" => b"eliminate_epsilon"
    "eliminate_literal" => b"eliminate_literal"
    "simplify_formula" => b"simplify_formula"
    "prepare_for_counterexmp" => b"prepare_for_counterexmp"
    "eliminate_projections_sums" => b"eliminate_projections_sums"
    "discriminate_if_poly:monomorphise_goal" =>
      b"discriminate_if_poly:monomorphise_goal"
    "discriminate_if_poly" => b"discriminate_if_poly"
    "eliminate_algebraic_if_poly" => b"eliminate_algebraic_if_poly"
    "encoding_smt_if_poly:monomorphise_goal" =>
      b"encoding_smt_if_poly:monomorphise_goal"
    "encoding_smt_if_poly:select_kept" => b"encoding_smt_if_poly:select_kept"
    "encoding_smt_if_poly:keep_field_types" =>
      b"encoding_smt_if_poly:keep_field_types"
    "encoding_smt_if_poly:twin" => b"encoding_smt_if_poly:twin"
    "encoding_smt_if_poly:guards" => b"encoding_smt_if_poly:guards"
    "encoding_smt_if_poly" => b"encoding_smt_if_poly"
    "prepared-task" => b"prepared-task"
    _ => abort("not a transform checkpoint stage")
  }
}

///|
async fn main {
  let arguments = @env.args()
  if arguments.length() < 4 || arguments[1] != "--stage" {
    fail_command(
      "usage: elab_canonical --stage STAGE FIXTURE | --stage STAGE --fixture LABEL --file PATH [-L PATH] [--no-stdlib]",
    )
    return
  }
  let stage = arguments[2]
  let all_semantics = stage == "upstream-semantics"
  let all_checkpoints = stage == "transform-checkpoints" || all_semantics
  let stage_rank = if all_checkpoints {
    21
  } else {
    transform_stage_rank(stage)
  }
  if stage_rank < 0 &&
    stage != "typed-semantic" &&
    stage != "raw-task" &&
    stage != "canonical-v3" &&
    stage != "diagnostic" &&
    !all_semantics {
    fail_command(
      "stage must be canonical-v3, typed-semantic, raw-task, a registered transform checkpoint, or diagnostic",
    )
    return
  }
  let mut fixture : String? = None
  let mut file : String? = None
  let loadpaths : Array[String] = []
  let mut use_stdlib = true
  let mut index = 3
  while index < arguments.length() {
    match arguments[index] {
      "--fixture" => {
        if index + 1 >= arguments.length() {
          fail_command("--fixture requires a value")
          return
        }
        fixture = Some(arguments[index + 1])
        index = index + 2
      }
      "--file" => {
        if index + 1 >= arguments.length() {
          fail_command("--file requires a value")
          return
        }
        file = Some(arguments[index + 1])
        index = index + 2
      }
      "-L" | "--loadpath" => {
        if index + 1 >= arguments.length() {
          fail_command(arguments[index] + " requires a value")
          return
        }
        loadpaths.push(arguments[index + 1])
        index = index + 2
      }
      "--no-stdlib" => {
        use_stdlib = false
        index = index + 1
      }
      positional => {
        if fixture is Some(_) || file is Some(_) {
          fail_command("unexpected positional argument " + positional)
          return
        }
        fixture = Some(positional)
        file = Some(positional)
        index = index + 1
      }
    }
  }
  guard fixture is Some(fixture) && file is Some(file) else {
    fail_command("both --fixture and --file are required")
    return
  }
  if !valid_fixture_path(fixture[:]) {
    fail_command("fixture label must be a repository-relative POSIX path")
    return
  }
  let display_file = @fs.realpath(file) catch {
    _ => {
      fail_command("cannot resolve source file")
      return
    }
  }
  let source = @fs.read_file(file).binary() catch {
    _ => {
      fail_command("cannot read source file")
      return
    }
  }
  let fixture_bytes = @utf8.encode(fixture)
  let parsed = @parser.parse_mlw_file(source, filename=fixture_bytes) catch {
    ParseError(_) => {
      fail_command("fixture has a parse error")
      return
    }
  }
  let context = @identity.CompilationContext::new()
  context.register_source_display_path(
    fixture_bytes,
    @utf8.encode(display_file),
  )
  let providers : Array[@source_env.SourceProvider] = []
  let fixture_directory = canonical_path_directory(fixture)
  let display_directory = canonical_path_directory(display_file)
  for loadpath in loadpaths {
    let resolved_loadpath = @fs.realpath(loadpath) catch {
      _ => {
        fail_command("cannot load source path " + loadpath)
        return
      }
    }
    let canonical_root = if resolved_loadpath == display_directory {
      Some(@utf8.encode(fixture_directory))
    } else {
      None
    }
    let provider = loadpath_source_provider(loadpath, canonical_root) catch {
      _ => {
        fail_command("cannot load source path " + loadpath)
        return
      }
    }
    providers.push(provider)
  }
  if use_stdlib {
    let provider = @stdlib.embedded_source_provider() catch {
      _ => {
        fail_command("cannot load the embedded standard-library sources")
        return
      }
    }
    providers.push(provider)
  }
  let environment = @environment.Environment::with_source_in_context(
    context,
    @source_env.SourceProvider::combine(providers),
  ) catch {
    _ => {
      fail_command("cannot construct the source environment")
      return
    }
  }
  let elaborated = @elab.elaborate_file(context, environment, parsed) catch {
    ElabError(diagnostic) => {
      if stage == "diagnostic" {
        write_diagnostic(diagnostic)
      } else {
        fail_command("elaboration failed: " + diagnostic.message)
      }
      return
    }
  }
  if stage == "diagnostic" {
    @stdio.stdout.write("{\"accepted\":true}\n")
    return
  }
  let profile = if stage_rank >= 0 {
    Some(@pipeline.bind_z3_profile(environment, context)) catch {
      _ => {
        fail_command("cannot bind the Z3 driver profile")
        return
      }
    }
  } else {
    None
  }
  for unit in elaborated.units() {
    if all_semantics {
      match unit {
        ElaboratedTheory(theory) =>
          write_record(
            @canonical.encode_typed_theory_record(fixture_bytes, source, theory),
          )
        ElaboratedModule(pmodule) =>
          write_record(
            @canonical.encode_typed_module_record(
              fixture_bytes, source, pmodule,
            ),
          )
      }
    }
    if stage == "canonical-v3" {
      match unit {
        ElaboratedTheory(theory) =>
          write_record(@canonical.encode_theory(theory).bytes())
        ElaboratedModule(pmodule) =>
          write_record(@canonical.encode_pmodule(pmodule).bytes())
      }
    } else if stage == "typed-semantic" {
      match unit {
        ElaboratedTheory(theory) =>
          write_record(
            @canonical.encode_typed_theory_record(fixture_bytes, source, theory),
          )
        ElaboratedModule(pmodule) =>
          write_record(
            @canonical.encode_typed_module_record(
              fixture_bytes, source, pmodule,
            ),
          )
      }
    } else {
      let theory = match unit {
        ElaboratedTheory(theory) => theory
        ElaboratedModule(pmodule) =>
          @pipeline.generate_vc_module(context, environment, pmodule).pure_theory() catch {
            @logic.TypeError(diagnostic) => {
              fail_command(
                "VC generation for " +
                bytes_hex_string(pmodule.pure_theory().view().name.view().name) +
                " failed: " +
                diagnostic.message,
              )
              return
            }
            _ => {
              fail_command("VC generation failed")
              return
            }
          }
      }
      let unit_name = theory.view().name.view().name
      let tasks = @theory.split_theory(context, theory, None) catch {
        @logic.TypeError(diagnostic) => {
          fail_command("task splitting failed: " + diagnostic.message)
          return
        }
        @theory.TheoryError(diagnostic) => {
          fail_command("task splitting failed: " + diagnostic.message)
          return
        }
        _ => {
          fail_command("task splitting failed")
          return
        }
      }
      for ordinal, task in tasks {
        if stage == "raw-task" {
          write_record(
            @canonical.encode_raw_task_record(
              fixture_bytes, source, unit_name, ordinal, task,
            ),
          )
        } else {
          let smt_provenance = @smtv2.SmtProvenance::new(context)
          smt_provenance.observe_task(task, None)
          if all_semantics {
            write_record(
              @canonical.encode_raw_task_record(
                fixture_bytes, source, unit_name, ordinal, task,
              ),
            )
          }
          guard profile is Some(profile) else {
            abort("driver-update stage has no bound profile")
          }
          let items = task.view().items
          guard !items.is_empty() &&
            items[items.length() - 1] is TheoryDecl(goal) &&
            goal.view() is Dprop(Pgoal, proposition, _) else {
            abort("validated raw task has no final goal")
          }
          let updated = @pipeline.update_z3_task(profile, task) catch {
            _ => {
              fail_command("driver update failed")
              return
            }
          }
          smt_provenance.observe_task(updated, Some(@identity.DriverUpdate))
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"driver-update",
              updated,
            )
          }
          let after_counterexamples = if stage_rank >= 1 {
            @pipeline.counterexamples_dependent_intros(context, updated) catch {
              _ => {
                fail_command("counterexamples_dependent_intros failed")
                return
              }
            }
          } else {
            updated
          }
          if stage_rank >= 1 {
            smt_provenance.observe_task(
              after_counterexamples,
              Some(@identity.CounterexamplesDependentIntros),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"counterexamples_dependent_intros",
              after_counterexamples,
            )
          }
          let after_inline = if stage_rank >= 2 {
            @pipeline.inline_trivial(context, after_counterexamples) catch {
              _ => {
                fail_command("inline_trivial failed")
                return
              }
            }
          } else {
            after_counterexamples
          }
          if stage_rank >= 2 {
            smt_provenance.observe_task(
              after_inline,
              Some(@identity.InlineTrivial),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"inline_trivial",
              after_inline,
            )
          }
          let after_eliminate_builtin = if stage_rank >= 3 {
            @pipeline.eliminate_builtin(context, after_inline) catch {
              _ => {
                fail_command("eliminate_builtin failed")
                return
              }
            }
          } else {
            after_inline
          }
          if stage_rank >= 3 {
            smt_provenance.observe_task(
              after_eliminate_builtin,
              Some(@identity.EliminateBuiltin),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_builtin",
              after_eliminate_builtin,
            )
          }
          let after_remove_unused = if stage_rank >= 4 {
            @pipeline.remove_unused_keep_constants(
              context, after_eliminate_builtin,
            ) catch {
              _ => {
                fail_command("remove_unused_keep_constants failed")
                return
              }
            }
          } else {
            after_eliminate_builtin
          }
          if stage_rank >= 4 {
            smt_provenance.observe_task(
              after_remove_unused,
              Some(@identity.RemoveUnusedKeepConstants),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"remove_unused_keep_constants",
              after_remove_unused,
            )
          }
          let after_detect = if stage_rank >= 5 {
            @pipeline.detect_polymorphism(context, after_remove_unused) catch {
              _ => {
                fail_command("detect_polymorphism failed")
                return
              }
            }
          } else {
            after_remove_unused
          }
          if stage_rank >= 5 {
            smt_provenance.observe_task(
              after_detect,
              Some(@identity.DetectPolymorphism),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"detect_polymorphism",
              after_detect,
            )
          }
          let polymorphic = all_checkpoints &&
            !after_detect.view().items.any(item => {
              match item {
                TheoryMeta(meta) =>
                  meta.view().name == b"encoding:monomorphic_only"
                TheoryDecl(_) | TheoryUse(_) | TheoryClone(_) => false
              }
            })
          let after_eliminate_definition = if stage_rank >= 6 {
            @pipeline.eliminate_definition_conditionally(context, after_detect) catch {
              _ => {
                fail_command("eliminate_definition_conditionally failed")
                return
              }
            }
          } else {
            after_detect
          }
          if stage_rank >= 6 {
            smt_provenance.observe_task(
              after_eliminate_definition,
              Some(@identity.EliminateDefinitionConditionally),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_definition_conditionally",
              after_eliminate_definition,
            )
          }
          let after_eliminate_inductive = if stage_rank >= 7 {
            @pipeline.eliminate_inductive(context, after_eliminate_definition) catch {
              _ => {
                fail_command("eliminate_inductive failed")
                return
              }
            }
          } else {
            after_eliminate_definition
          }
          if stage_rank >= 7 {
            smt_provenance.observe_task(
              after_eliminate_inductive,
              Some(@identity.EliminateInductive),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_inductive",
              after_eliminate_inductive,
            )
          }
          let after_eliminate_epsilon = if stage_rank >= 8 {
            @pipeline.eliminate_epsilon(context, after_eliminate_inductive) catch {
              _ => {
                fail_command("eliminate_epsilon failed")
                return
              }
            }
          } else {
            after_eliminate_inductive
          }
          if stage_rank >= 8 {
            smt_provenance.observe_task(
              after_eliminate_epsilon,
              Some(@identity.EliminateEpsilon),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_epsilon",
              after_eliminate_epsilon,
            )
          }
          let after_eliminate_literal = if stage_rank >= 9 {
            @pipeline.eliminate_literal(context, after_eliminate_epsilon) catch {
              _ => {
                fail_command("eliminate_literal failed")
                return
              }
            }
          } else {
            after_eliminate_epsilon
          }
          if stage_rank >= 9 {
            smt_provenance.observe_task(
              after_eliminate_literal,
              Some(@identity.EliminateLiteral),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_literal",
              after_eliminate_literal,
            )
          }
          let after_simplify = if stage_rank >= 10 {
            @pipeline.simplify_formula(context, after_eliminate_literal) catch {
              _ => {
                fail_command("simplify_formula failed")
                return
              }
            }
          } else {
            after_eliminate_literal
          }
          if stage_rank >= 10 {
            smt_provenance.observe_task(
              after_simplify,
              Some(@identity.SimplifyFormula),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"simplify_formula",
              after_simplify,
            )
          }
          let after_prepare_counterexample = if stage_rank >= 11 {
            @pipeline.prepare_for_counterexmp(context, after_simplify) catch {
              _ => {
                fail_command("prepare_for_counterexmp failed")
                return
              }
            }
          } else {
            after_simplify
          }
          if stage_rank >= 11 {
            smt_provenance.observe_task(
              after_prepare_counterexample,
              Some(@identity.PrepareForCounterexmp),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"prepare_for_counterexmp",
              after_prepare_counterexample,
            )
          }
          let after_eliminate_projections = if stage_rank >= 12 {
            @pipeline.eliminate_projections_sums(
              context, after_prepare_counterexample,
            ) catch {
              _ => {
                fail_command("eliminate_projections_sums failed")
                return
              }
            }
          } else {
            after_prepare_counterexample
          }
          if stage_rank >= 12 {
            smt_provenance.observe_task(
              after_eliminate_projections,
              Some(@identity.EliminateProjectionsSums),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_projections_sums",
              after_eliminate_projections,
            )
          }
          let after_discriminate_goal = if stage_rank >= 13 {
            @pipeline.discriminate_monomorphise_goal(
              context, after_eliminate_projections,
            ) catch {
              _ => {
                fail_command("discriminate_if_poly:monomorphise_goal failed")
                return
              }
            }
          } else {
            after_eliminate_projections
          }
          if stage_rank >= 13 {
            smt_provenance.observe_task(
              after_discriminate_goal,
              Some(@identity.DiscriminateMonomorphiseGoal),
            )
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"discriminate_if_poly:monomorphise_goal",
              after_discriminate_goal,
            )
          }
          let after_discriminate = if stage_rank >= 14 {
            @pipeline.discriminate_if_poly(context, after_discriminate_goal) catch {
              @transform.TransformError(diagnostic) => {
                fail_command(
                  "discriminate_if_poly failed: " + diagnostic.message,
                )
                return
              }
            }
          } else {
            after_discriminate_goal
          }
          if stage_rank >= 14 {
            smt_provenance.observe_task(
              after_discriminate,
              Some(@identity.DiscriminateIfPoly),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"discriminate_if_poly",
              after_discriminate,
            )
          }
          let after_eliminate_algebraic = if stage_rank >= 15 {
            @pipeline.eliminate_algebraic_if_poly(
              profile, context, after_discriminate,
            ) catch {
              @transform.TransformError(diagnostic) => {
                fail_command(
                  "eliminate_algebraic_if_poly failed: " + diagnostic.message,
                )
                return
              }
            }
          } else {
            after_discriminate
          }
          if stage_rank >= 15 {
            smt_provenance.observe_task(
              after_eliminate_algebraic,
              Some(@identity.EliminateAlgebraicIfPoly),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"eliminate_algebraic_if_poly",
              after_eliminate_algebraic,
            )
          }
          let after_encoding_goal = if stage_rank >= 16 {
            @pipeline.encoding_monomorphise_goal(
              context, after_eliminate_algebraic,
            ) catch {
              _ => {
                fail_command("encoding_smt_if_poly:monomorphise_goal failed")
                return
              }
            }
          } else {
            after_eliminate_algebraic
          }
          if stage_rank >= 16 {
            smt_provenance.observe_task(
              after_encoding_goal,
              Some(@identity.EncodingMonomorphiseGoal),
            )
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly:monomorphise_goal",
              after_encoding_goal,
            )
          }
          let after_select_kept = if stage_rank >= 17 {
            @pipeline.encoding_select_kept(context, after_encoding_goal) catch {
              _ => {
                fail_command("encoding_smt_if_poly:select_kept failed")
                return
              }
            }
          } else {
            after_encoding_goal
          }
          if stage_rank >= 17 {
            smt_provenance.observe_task(
              after_select_kept,
              Some(@identity.SelectKept),
            )
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly:select_kept",
              after_select_kept,
            )
          }
          let after_keep_field_types = if stage_rank >= 18 {
            @pipeline.encoding_keep_field_types(context, after_select_kept) catch {
              _ => {
                fail_command("encoding_smt_if_poly:keep_field_types failed")
                return
              }
            }
          } else {
            after_select_kept
          }
          if stage_rank >= 18 {
            smt_provenance.observe_task(
              after_keep_field_types,
              Some(@identity.KeepFieldTypes),
            )
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly:keep_field_types",
              after_keep_field_types,
            )
          }
          let after_twin = if stage_rank >= 19 {
            @pipeline.encoding_twin(context, after_keep_field_types) catch {
              _ => {
                fail_command("encoding_smt_if_poly:twin failed")
                return
              }
            }
          } else {
            after_keep_field_types
          }
          if stage_rank >= 19 {
            smt_provenance.observe_task(after_twin, Some(@identity.Twin))
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly:twin",
              after_twin,
            )
          }
          let after_guards = if stage_rank >= 20 {
            @pipeline.encoding_guards(context, after_twin) catch {
              @transform.TransformError(diagnostic) => {
                fail_command(
                  "encoding_smt_if_poly:guards failed: " + diagnostic.message,
                )
                return
              }
            }
          } else {
            after_twin
          }
          if stage_rank >= 20 {
            smt_provenance.observe_task(after_guards, Some(@identity.Guards))
          }
          if polymorphic {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly:guards",
              after_guards,
            )
          }
          let checkpoint = if stage_rank >= 21 {
            @pipeline.encoding_smt_if_poly(context, after_guards) catch {
              _ => {
                fail_command("encoding_smt_if_poly failed")
                return
              }
            }
          } else {
            after_guards
          }
          if stage_rank >= 21 {
            smt_provenance.observe_task(
              checkpoint,
              Some(@identity.EncodingSmtIfPoly),
            )
          }
          if all_checkpoints {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              b"encoding_smt_if_poly",
              checkpoint,
            )
            if all_semantics {
              write_checkpoint_record(
                fixture_bytes,
                source,
                unit_name,
                proposition.view().name,
                ordinal,
                b"prepared-task",
                checkpoint,
              )
              let query = @pipeline.print_prepared_z3_task(profile, checkpoint) catch {
                @smtv2.PrinterError(diagnostic) => {
                  fail_command("SMT printing failed: " + diagnostic.message)
                  return
                }
                _ => {
                  fail_command("SMT profile binding failed")
                  return
                }
              }
              let stream = @smtv2.normalize_smt_query_with_provenance(
                query, smt_provenance,
              ) catch {
                @smtv2.PrinterError(diagnostic) => {
                  fail_command(
                    "SMT normalization failed: " + diagnostic.message,
                  )
                  return
                }
              }
              write_smt_record(
                fixture_bytes,
                source,
                unit_name,
                proposition.view().name,
                ordinal,
                stream,
              )
            }
          } else if stage == "smt-tokens" || stage == "smt-query" {
            let query = @pipeline.print_prepared_z3_task(profile, checkpoint) catch {
              @smtv2.PrinterError(diagnostic) => {
                fail_command("SMT printing failed: " + diagnostic.message)
                return
              }
              _ => {
                fail_command("SMT profile binding failed")
                return
              }
            }
            if stage == "smt-query" {
              write_smt_query(
                unit_name,
                proposition.view().name,
                ordinal,
                query,
              )
            } else {
              let stream = @smtv2.normalize_smt_query_with_provenance(
                query, smt_provenance,
              ) catch {
                @smtv2.PrinterError(diagnostic) => {
                  fail_command(
                    "SMT normalization failed: " + diagnostic.message,
                  )
                  return
                }
              }
              write_smt_record(
                fixture_bytes,
                source,
                unit_name,
                proposition.view().name,
                ordinal,
                stream,
              )
            }
          } else {
            write_checkpoint_record(
              fixture_bytes,
              source,
              unit_name,
              proposition.view().name,
              ordinal,
              transform_stage_bytes(stage),
              checkpoint,
            )
          }
        }
      }
    }
  }
}

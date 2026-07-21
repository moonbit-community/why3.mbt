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
    FeatureClassification => "feature-classification"
    DeclarationElaboration => "declaration-elaboration"
    PureTyping => "typing"
    ProgramTyping => "program-typing"
    FileRegistration => "file-registration"
  }
}

///|
fn unsupported_feature_name(feature : @elab.UnsupportedFeature) -> String {
  match feature {
    AbstractRoutineShape => "AbstractRoutineShape"
    AlgebraicData => "AlgebraicData"
    CheckAssertion => "CheckAssertion"
    Clone => "Clone"
    ControlAttribute => "ControlAttribute"
    Datatype => "Datatype"
    DestructuringPattern => "DestructuringPattern"
    DriverOnlyTheory => "DriverOnlyTheory"
    DriverOnlyType => "DriverOnlyType"
    Epsilon => "Epsilon"
    Exception => "Exception"
    ExternalOrDriverOnlyImport => "ExternalOrDriverOnlyImport"
    Ghost => "Ghost"
    HigherOrder => "HigherOrder"
    HigherOrderApplication => "HigherOrderApplication"
    Inductive => "Inductive"
    Lambda => "Lambda"
    LocalRoutine => "LocalRoutine"
    Loop => "Loop"
    NestedUnsupportedExpression => "NestedUnsupportedExpression"
    NestedUnsupportedTerm => "NestedUnsupportedTerm"
    OldAt => "OldAt"
    PrivateType => "PrivateType"
    ProgramExpression => "ProgramExpression"
    ProgramRoutineShape => "ProgramRoutineShape"
    ProofControlConnective => "ProofControlConnective"
    RecordOrInvariant => "RecordOrInvariant"
    Recursion => "Recursion"
    RecursiveOrHigherOrderLogic => "RecursiveOrHigherOrderLogic"
    Reference => "Reference"
    RoutineKind => "RoutineKind"
    StringLiteral => "StringLiteral"
    TupleExpression => "TupleExpression"
    TupleTerm => "TupleTerm"
    TupleType => "TupleType"
    TypeDeclarationShape => "TypeDeclarationShape"
    TypePurification => "TypePurification"
    TypeVisibilityShape => "TypeVisibilityShape"
    UserMeta => "UserMeta"
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
    Unsupported(feature) =>
      "UnsupportedFeature(" + unsupported_feature_name(feature) + ")"
    TypeFailure(_) => "TypeError(Other)"
    TheoryFailure(_) => "TheoryError(Other)"
    EnvironmentFailure(ResolveError) => "EnvironmentError(ResolveError)"
    EnvironmentFailure(_) => "EnvironmentError(Other)"
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
    "smt-token-stream" => 22
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
  if arguments.length() != 4 || arguments[1] != "--stage" {
    fail_command(
      "usage: elab_canonical --stage typed-semantic|raw-task|transform-checkpoints|driver-update|counterexamples_dependent_intros|inline_trivial|eliminate_builtin|remove_unused_keep_constants|detect_polymorphism|eliminate_definition_conditionally|eliminate_inductive|eliminate_epsilon|eliminate_literal|simplify_formula|prepare_for_counterexmp|eliminate_projections_sums|discriminate_if_poly:monomorphise_goal|discriminate_if_poly|eliminate_algebraic_if_poly|encoding_smt_if_poly:monomorphise_goal|encoding_smt_if_poly:select_kept|encoding_smt_if_poly:keep_field_types|encoding_smt_if_poly:twin|encoding_smt_if_poly:guards|encoding_smt_if_poly|prepared-task|smt-token-stream|smt-query|diagnostic FIXTURE",
    )
    return
  }
  let stage = arguments[2]
  let all_checkpoints = stage == "transform-checkpoints"
  let stage_rank = if all_checkpoints {
    21
  } else {
    transform_stage_rank(stage)
  }
  if stage_rank < 0 &&
    stage != "typed-semantic" &&
    stage != "raw-task" &&
    stage != "diagnostic" {
    fail_command(
      "stage must be typed-semantic, raw-task, a registered transform checkpoint, or diagnostic",
    )
    return
  }
  let fixture = arguments[3]
  if !valid_fixture_path(fixture[:]) {
    fail_command("fixture must be a repository-relative POSIX path")
    return
  }
  let source = @fs.read_file(fixture).binary() catch {
    _ => {
      fail_command("cannot read fixture")
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
  let frozen = @stdlib.minimal_env(context) catch {
    _ => {
      fail_command("cannot load the frozen semantic environment")
      return
    }
  }
  let environment = frozen.semantic_environment()
  // The frozen WellFounded theory is deliberately driver-only in production.
  // This repository-owned reference fixture exposes only that exact key so the
  // required trusted Dind elimination path can be compared with upstream.
  if fixture == "tools/why3_reference/fixtures/transform-inductive.mlw" {
    try {
      let keys = [
        @theory.TheoryKey::new([b"why3", b"WellFounded"], b"WellFounded"),
        @theory.TheoryKey::new([b"map"], b"Map"),
        @theory.TheoryKey::new([b"map"], b"Const"),
      ]
      for key in keys {
        environment.add_theory_alias(key, key, None)
      }
    } catch {
      _ => {
        fail_command("cannot expose the trusted inductive reference fixture")
        return
      }
    }
  }
  guard parsed is Modules(_) else {
    fail_command("fixture must contain named units")
    return
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
    Some(@pipeline.bind_z3_profile(frozen, context)) catch {
      _ => {
        fail_command("cannot bind the static Z3 profile")
        return
      }
    }
  } else {
    None
  }
  for unit in elaborated.units() {
    if stage == "typed-semantic" {
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
          @vc.generate_module(context, pmodule).pure_theory()
      }
      let unit_name = theory.view().name.view().name
      for ordinal, task in @theory.split_theory(context, theory, None) {
        if stage == "raw-task" {
          write_record(
            @canonical.encode_raw_task_record(
              fixture_bytes, source, unit_name, ordinal, task,
            ),
          )
        } else {
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
              _ => {
                fail_command("discriminate_if_poly failed")
                return
              }
            }
          } else {
            after_discriminate_goal
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
          } else if stage == "smt-token-stream" || stage == "smt-query" {
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
              let stream = @smtv2.normalize_smt_query(query) catch {
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

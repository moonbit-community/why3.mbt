// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum Z3Printer {
  SmtV26
} derive(Eq, Debug)

///|
pub(all) enum TransformId {
  CounterexamplesDependentIntros
  InlineTrivial
  EliminateBuiltin
  RemoveUnusedKeepConstants
  DetectPolymorphism
  EliminateDefinitionConditionally
  EliminateInductive
  EliminateEpsilon
  EliminateLiteral
  SimplifyFormula
  PrepareForCounterexmp
  EliminateProjectionsSums
  DiscriminateIfPoly
  EliminateAlgebraicIfPoly
  EncodingSmtIfPoly
} derive(Eq, Debug)

///|
pub fn TransformId::canonical_name(self : TransformId) -> BytesView {
  match self {
    CounterexamplesDependentIntros => b"counterexamples_dependent_intros"
    InlineTrivial => b"inline_trivial"
    EliminateBuiltin => b"eliminate_builtin"
    RemoveUnusedKeepConstants => b"remove_unused_keep_constants"
    DetectPolymorphism => b"detect_polymorphism"
    EliminateDefinitionConditionally => b"eliminate_definition_conditionally"
    EliminateInductive => b"eliminate_inductive"
    EliminateEpsilon => b"eliminate_epsilon"
    EliminateLiteral => b"eliminate_literal"
    SimplifyFormula => b"simplify_formula"
    PrepareForCounterexmp => b"prepare_for_counterexmp"
    EliminateProjectionsSums => b"eliminate_projections_sums"
    DiscriminateIfPoly => b"discriminate_if_poly"
    EliminateAlgebraicIfPoly => b"eliminate_algebraic_if_poly"
    EncodingSmtIfPoly => b"encoding_smt_if_poly"
  }
}

///|
priv enum UnboundTy {
  UnboundTyVariable(Bytes)
  UnboundTyApplication(@identity.SnapshotSymbolKey, Array[UnboundTy])
}

///|
priv enum UnboundMetaArgument {
  UnboundMetaType(UnboundTy)
  UnboundMetaTypeSymbol(@identity.SnapshotSymbolKey)
  UnboundMetaLogicSymbol(@identity.SnapshotSymbolKey)
  UnboundMetaPropositionSymbol(@identity.SnapshotSymbolKey)
  UnboundMetaString(Bytes)
  UnboundMetaInteger(Int64)
  UnboundMetaIdentifier(Bytes)
}

///|
priv struct UnboundDriverMeta {
  name : Bytes
  arguments : Array[UnboundMetaArgument]
}

///|
priv struct UnboundMetaGroup {
  theory_key : @theory.TheoryKey
  entries : Array[UnboundDriverMeta]
}

///|
priv struct TheoryPrelude {
  theory_key : @theory.TheoryKey
  values : Array[Bytes]
}

///|
pub(all) enum SyntaxKind {
  TypeSyntax
  LogicSyntax
  LiteralSyntax
} derive(Eq, Debug)

///|
priv struct UnboundSyntaxEntry {
  kind : SyntaxKind
  symbol : @identity.SnapshotSymbolKey
  template : Bytes
  overriding : Bool
}

///|
pub(all) enum ProverAnswerRule {
  RuleValid
  RuleInvalid
  RuleTimeout
  RuleOutOfMemory
  RuleStepLimitExceeded
  RuleUnknown(Bytes)
  RuleFailure(Bytes)
  RuleHighFailure
} derive(Eq, Debug)

///|
priv struct ResultRegexp {
  pattern : Bytes
  answer : ProverAnswerRule
}

///|
priv struct ResultExitCode {
  code : Int
  answer : ProverAnswerRule
}

///|
pub(all) struct ResultRegexpView {
  pattern : Bytes
  answer : ProverAnswerRule
}

///|
pub(all) struct ResultExitCodeView {
  code : Int
  answer : ProverAnswerRule
}

///|
struct Z3CommandTemplate {
  executable : Bytes
  common_arguments : Array[Bytes]
  time_limit_argument : Bytes
  step_limit_argument : Bytes
}

///|
pub(all) struct Z3CommandTemplateView {
  executable : Bytes
  common_arguments : ArrayView[Bytes]
  time_limit_argument : Bytes
  step_limit_argument : Bytes
}

///|
pub fn Z3CommandTemplate::view(
  self : Z3CommandTemplate,
) -> Z3CommandTemplateView {
  {
    executable: self.executable,
    common_arguments: self.common_arguments[:],
    time_limit_argument: self.time_limit_argument,
    step_limit_argument: self.step_limit_argument,
  }
}

///|
struct Z3StaticSpec {
  printer : Z3Printer
  transforms : Array[TransformId]
  meta_groups : Array[UnboundMetaGroup]
  snapshot_meta_groups : Array[UnboundMetaGroup]
  syntax : Array[UnboundSyntaxEntry]
  remove : Array[@identity.SnapshotSymbolKey]
  preludes : Array[Bytes]
  theory_preludes : Array[TheoryPrelude]
  result_regexps : Array[ResultRegexp]
  result_exit_codes : Array[ResultExitCode]
  command : Z3CommandTemplate
  monomorphic_checkpoints : Array[Bytes]
  polymorphic_checkpoints : Array[Bytes]
}

///|
pub(all) struct Z3StaticSpecView {
  printer : Z3Printer
  transforms : ArrayView[TransformId]
  driver_meta_group_count : Int
  driver_meta_count : Int
  snapshot_meta_group_count : Int
  snapshot_meta_count : Int
  syntax_count : Int
  remove_count : Int
  preludes : ArrayView[Bytes]
  theory_prelude_count : Int
  result_regexp_count : Int
  result_exit_code_count : Int
  command : Z3CommandTemplate
  monomorphic_checkpoints : ArrayView[Bytes]
  polymorphic_checkpoints : ArrayView[Bytes]
}

///|
fn ResultRegexp::view(self : ResultRegexp) -> ResultRegexpView {
  { pattern: self.pattern, answer: self.answer }
}

///|
fn ResultExitCode::view(self : ResultExitCode) -> ResultExitCodeView {
  { code: self.code, answer: self.answer }
}

///|
fn meta_count(groups : ArrayView[UnboundMetaGroup]) -> Int {
  let mut count = 0
  for group in groups {
    count = count + group.entries.length()
  }
  count
}

///|
pub fn Z3StaticSpec::view(self : Z3StaticSpec) -> Z3StaticSpecView {
  {
    printer: self.printer,
    transforms: self.transforms[:],
    driver_meta_group_count: self.meta_groups.length(),
    driver_meta_count: meta_count(self.meta_groups),
    snapshot_meta_group_count: self.snapshot_meta_groups.length(),
    snapshot_meta_count: meta_count(self.snapshot_meta_groups),
    syntax_count: self.syntax.length(),
    remove_count: self.remove.length(),
    preludes: self.preludes[:],
    theory_prelude_count: self.theory_preludes.length(),
    result_regexp_count: self.result_regexps.length(),
    result_exit_code_count: self.result_exit_codes.length(),
    command: self.command,
    monomorphic_checkpoints: self.monomorphic_checkpoints[:],
    polymorphic_checkpoints: self.polymorphic_checkpoints[:],
  }
}

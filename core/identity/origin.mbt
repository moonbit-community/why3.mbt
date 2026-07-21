// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// Stable stages that may introduce generated identifiers. New stages are
/// added deliberately alongside canonical vectors.
pub(all) enum GeneratedStage {
  DriverUpdate
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
  DiscriminateMonomorphiseGoal
  DiscriminateIfPoly
  EliminateAlgebraicIfPoly
  EncodingMonomorphiseGoal
  SelectKept
  KeepFieldTypes
  Twin
  Guards
  EncodingSmtIfPoly
  Wp
} derive(Eq, Debug)

///|
pub fn GeneratedStage::canonical_name(self : GeneratedStage) -> BytesView {
  match self {
    DriverUpdate => b"driver-update"
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
    DiscriminateMonomorphiseGoal => b"discriminate_if_poly:monomorphise_goal"
    DiscriminateIfPoly => b"discriminate_if_poly"
    EliminateAlgebraicIfPoly => b"eliminate_algebraic_if_poly"
    EncodingMonomorphiseGoal => b"encoding_smt_if_poly:monomorphise_goal"
    SelectKept => b"encoding_smt_if_poly:select_kept"
    KeepFieldTypes => b"encoding_smt_if_poly:keep_field_types"
    Twin => b"encoding_smt_if_poly:twin"
    Guards => b"encoding_smt_if_poly:guards"
    EncodingSmtIfPoly => b"encoding_smt_if_poly"
    Wp => b"wp"
  }
}

///|
/// Source metadata independent of the parser package. Paths remain raw bytes;
/// byte offsets and logical line/column positions are stored separately.
struct SourceSpan {
  relative_path : Bytes
  start_byte : Int
  end_byte : Int
  start_line : Int64
  start_column : Int64
  end_line : Int64
  end_column : Int64
} derive(Eq, Debug)

///|
pub(all) struct SourceSpanView {
  relative_path : Bytes
  start_byte : Int
  end_byte : Int
  start_line : Int64
  start_column : Int64
  end_line : Int64
  end_column : Int64
} derive(Eq, Debug)

///|
pub fn SourceSpan::new(
  relative_path : BytesView,
  start_byte : Int,
  end_byte : Int,
  start_line : Int64,
  start_column : Int64,
  end_line : Int64,
  end_column : Int64,
) -> SourceSpan {
  {
    relative_path: relative_path.to_owned(),
    start_byte,
    end_byte,
    start_line,
    start_column,
    end_line,
    end_column,
  }
}

///|
pub fn SourceSpan::view(self : SourceSpan) -> SourceSpanView {
  {
    relative_path: self.relative_path,
    start_byte: self.start_byte,
    end_byte: self.end_byte,
    start_line: self.start_line,
    start_column: self.start_column,
    end_line: self.end_line,
    end_column: self.end_column,
  }
}

///|
/// Provenance, display name, location/snapshot identity, and attributes for a
/// semantic object. Only the generated variant is eligible for SMT alpha
/// normalization.
struct Origin {
  kind : OriginKind
  display_name : Bytes
  source_span : SourceSpan?
  snapshot_key : SnapshotSymbolKey?
  attributes : SemanticAttributes
} derive(Eq, Debug)

///|
/// Opaque origin classification.
struct OriginKind {
  tag : Int
  generated_stage : GeneratedStage?
} derive(Eq, Debug)

///|
pub(all) enum OriginKindView {
  UserKind
  SnapshotKind
  GeneratedKind(GeneratedStage)
} derive(Eq, Debug)

///|
pub(all) enum OriginView {
  UserOrigin(Bytes, SourceSpan?, ArrayView[Bytes])
  SnapshotOrigin(Bytes, SnapshotSymbolKey, ArrayView[Bytes])
  GeneratedOrigin(GeneratedStage, Bytes, SourceSpan?, ArrayView[Bytes])
} derive(Eq, Debug)

///|
fn user_origin_kind() -> OriginKind {
  { tag: 0, generated_stage: None }
}

///|
fn snapshot_origin_kind() -> OriginKind {
  { tag: 1, generated_stage: None }
}

///|
fn generated_origin_kind(stage : GeneratedStage) -> OriginKind {
  { tag: 2, generated_stage: Some(stage) }
}

///|
pub fn Origin::user(
  display_name : BytesView,
  source_span : SourceSpan?,
  attributes : ArrayView[Bytes],
) -> Origin {
  {
    kind: user_origin_kind(),
    display_name: display_name.to_owned(),
    source_span,
    snapshot_key: None,
    attributes: SemanticAttributes::from_array(attributes),
  }
}

///|
pub fn Origin::snapshot(
  display_name : BytesView,
  snapshot_key : SnapshotSymbolKey,
  attributes : ArrayView[Bytes],
) -> Origin {
  {
    kind: snapshot_origin_kind(),
    display_name: display_name.to_owned(),
    source_span: None,
    snapshot_key: Some(snapshot_key),
    attributes: SemanticAttributes::from_array(attributes),
  }
}

///|
/// Snapshot decoder constructor that also preserves the upstream source span.
/// The location is metadata and remains outside `SnapshotSymbolKey`, so moving
/// a source file does not silently change semantic symbol identity.
pub fn Origin::snapshot_with_span(
  display_name : BytesView,
  snapshot_key : SnapshotSymbolKey,
  source_span : SourceSpan?,
  attributes : ArrayView[Bytes],
) -> Origin {
  {
    kind: snapshot_origin_kind(),
    display_name: display_name.to_owned(),
    source_span,
    snapshot_key: Some(snapshot_key),
    attributes: SemanticAttributes::from_array(attributes),
  }
}

///|
pub fn Origin::generated(
  stage : GeneratedStage,
  display_name : BytesView,
  source_span : SourceSpan?,
  attributes : ArrayView[Bytes],
) -> Origin {
  {
    kind: generated_origin_kind(stage),
    display_name: display_name.to_owned(),
    source_span,
    snapshot_key: None,
    attributes: SemanticAttributes::from_array(attributes),
  }
}

///|
pub fn Origin::kind(self : Origin) -> OriginKind {
  self.kind
}

///|
pub fn OriginKind::view(self : OriginKind) -> OriginKindView {
  match (self.tag, self.generated_stage) {
    (0, None) => UserKind
    (1, None) => SnapshotKind
    (2, Some(stage)) => GeneratedKind(stage)
    _ => abort("invalid opaque OriginKind")
  }
}

///|
pub fn Origin::view(self : Origin) -> OriginView {
  match self.kind.view() {
    UserKind =>
      UserOrigin(self.display_name, self.source_span, self.attributes.items())
    SnapshotKind => {
      guard self.snapshot_key is Some(key) else {
        abort("snapshot origin is missing its key")
      }
      SnapshotOrigin(self.display_name, key, self.attributes.items())
    }
    GeneratedKind(stage) =>
      GeneratedOrigin(
        stage,
        self.display_name,
        self.source_span,
        self.attributes.items(),
      )
  }
}

///|
pub fn Origin::display_name(self : Origin) -> BytesView {
  self.display_name[:]
}

///|
pub fn Origin::attributes(self : Origin) -> ArrayView[Bytes] {
  self.attributes.items()
}

///|
pub fn Origin::source_span(self : Origin) -> SourceSpan? {
  self.source_span
}

///|
pub fn Origin::snapshot_key(self : Origin) -> SnapshotSymbolKey? {
  self.snapshot_key
}

///|
pub fn Origin::allows_generated_name_normalization(self : Origin) -> Bool {
  self.kind().view() is GeneratedKind(_)
}

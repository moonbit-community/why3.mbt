// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum MetaArgument {
  MetaType(@logic.Ty)
  MetaTypeSymbol(@logic.TypeSymbol)
  MetaLogicSymbol(@logic.LSymbol)
  MetaPropositionSymbol(@logic.PrSymbol)
  MetaString(Bytes)
  MetaInteger(Int64)
  MetaIdentifier(SemanticName)
}

///|
struct Meta {
  name : Bytes
  arguments : Array[MetaArgument]
}

///|
pub(all) struct MetaView {
  name : Bytes
  arguments : ArrayView[MetaArgument]
}

///|
pub fn Meta::new(name : BytesView, arguments : ArrayView[MetaArgument]) -> Meta {
  { name: name.to_owned(), arguments: arguments.to_owned() }
}

///|
pub fn Meta::view(self : Meta) -> MetaView {
  { name: self.name, arguments: self.arguments[:] }
}

///|
pub fn Meta::validate_context(
  self : Meta,
  anchor : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  for argument in self.arguments {
    match argument {
      MetaType(value) => require_same_id(anchor, value.context_anchor(), span)
      MetaTypeSymbol(value) =>
        require_same_id(anchor, value.semantic_id(), span)
      MetaLogicSymbol(value) =>
        require_same_id(anchor, value.semantic_id(), span)
      MetaPropositionSymbol(value) =>
        require_same_id(anchor, value.semantic_id(), span)
      MetaString(_) | MetaInteger(_) | MetaIdentifier(_) => ()
    }
  }
}

///|
pub(all) enum CloneTypeInstantiation {
  CloneType(@logic.TypeSymbol, @logic.Ty)
  CloneTypeSymbol(@logic.TypeSymbol, @logic.TypeSymbol)
}

///|
struct CloneWitness {
  anchor : @identity.SemanticId
  source : TheoryKey
  source_item_identity : UInt
  type_instantiations : Array[CloneTypeInstantiation]
  logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)]
  proposition_instantiations : Array[(@logic.PrSymbol, @logic.PrSymbol)]
}

///|
pub(all) struct CloneWitnessView {
  source : TheoryKey
  source_item_identity : UInt
  type_instantiations : ArrayView[CloneTypeInstantiation]
  logic_instantiations : ArrayView[(@logic.LSymbol, @logic.LSymbol)]
  proposition_instantiations : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)]
}

///|
fn require_same_id(
  anchor : @identity.SemanticId,
  id : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  if !anchor.same_context(id) {
    fail_theory(
      ContextMismatch,
      span,
      "semantic objects belong to different contexts",
    )
  }
}

///|
pub fn CloneWitness::trusted_new(
  context_anchor : @identity.SemanticId,
  source : TheoryKey,
  source_item_identity : UInt,
  type_instantiations : ArrayView[CloneTypeInstantiation],
  logic_instantiations : ArrayView[(@logic.LSymbol, @logic.LSymbol)],
  proposition_instantiations : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)],
  span : @identity.SourceSpan?,
) -> CloneWitness raise TheoryError {
  let types = type_instantiations.to_owned()
  for instantiation in types {
    match instantiation {
      CloneType(symbol, ty) => {
        require_same_id(context_anchor, symbol.semantic_id(), span)
        require_same_id(context_anchor, ty.context_anchor(), span)
      }
      CloneTypeSymbol(source_symbol, target_symbol) => {
        require_same_id(context_anchor, source_symbol.semantic_id(), span)
        require_same_id(context_anchor, target_symbol.semantic_id(), span)
      }
    }
  }
  let logic = logic_instantiations.to_owned()
  for entry in logic {
    let (source_symbol, target_symbol) = entry
    require_same_id(context_anchor, source_symbol.semantic_id(), span)
    require_same_id(context_anchor, target_symbol.semantic_id(), span)
  }
  let propositions = proposition_instantiations.to_owned()
  for entry in propositions {
    let (source_symbol, target_symbol) = entry
    require_same_id(context_anchor, source_symbol.semantic_id(), span)
    require_same_id(context_anchor, target_symbol.semantic_id(), span)
  }
  {
    anchor: context_anchor,
    source,
    source_item_identity,
    type_instantiations: types,
    logic_instantiations: logic,
    proposition_instantiations: propositions,
  }
}

///|
pub fn CloneWitness::context_anchor(
  self : CloneWitness,
) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn CloneWitness::view(self : CloneWitness) -> CloneWitnessView {
  {
    source: self.source,
    source_item_identity: self.source_item_identity,
    type_instantiations: self.type_instantiations[:],
    logic_instantiations: self.logic_instantiations[:],
    proposition_instantiations: self.proposition_instantiations[:],
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

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
pub(all) enum MetaArgumentType {
  MetaTypeArgument
  MetaTypeSymbolArgument
  MetaLogicSymbolArgument
  MetaPropositionSymbolArgument
  MetaStringArgument
  MetaIntegerArgument
  MetaIdentifierArgument
} derive(Eq, Debug)

///|
struct MetaDescriptor {
  name : Bytes
  argument_types : Array[MetaArgumentType]
  exclusive : Bool
  description : Bytes
}

///|
pub(all) struct MetaDescriptorView {
  name : Bytes
  argument_types : ArrayView[MetaArgumentType]
  exclusive : Bool
  description : Bytes
}

///|
struct Meta {
  name : Bytes
  argument_types : Array[MetaArgumentType]
  exclusive : Bool
  arguments : Array[MetaArgument]
}

///|
pub(all) struct MetaView {
  name : Bytes
  argument_types : ArrayView[MetaArgumentType]
  exclusive : Bool
  arguments : ArrayView[MetaArgument]
}

///|
fn meta_argument_type(argument : MetaArgument) -> MetaArgumentType {
  match argument {
    MetaType(_) => MetaTypeArgument
    MetaTypeSymbol(_) => MetaTypeSymbolArgument
    MetaLogicSymbol(_) => MetaLogicSymbolArgument
    MetaPropositionSymbol(_) => MetaPropositionSymbolArgument
    MetaString(_) => MetaStringArgument
    MetaInteger(_) => MetaIntegerArgument
    MetaIdentifier(_) => MetaIdentifierArgument
  }
}

///|
pub fn MetaDescriptor::new(
  name : BytesView,
  argument_types : ArrayView[MetaArgumentType],
  exclusive : Bool,
  description : BytesView,
  span : @identity.SourceSpan?,
) -> MetaDescriptor raise TheoryError {
  if name.is_empty() {
    fail_theory(InvalidQualifiedName, span, "meta name is empty")
  }
  {
    name: name.to_owned(),
    argument_types: argument_types.to_owned(),
    exclusive,
    description: description.to_owned(),
  }
}

///|
pub fn MetaDescriptor::view(self : MetaDescriptor) -> MetaDescriptorView {
  {
    name: self.name,
    argument_types: self.argument_types[:],
    exclusive: self.exclusive,
    description: self.description,
  }
}

///|
fn convert_meta_argument(
  expected : MetaArgumentType,
  argument : MetaArgument,
  span : @identity.SourceSpan?,
) -> MetaArgument raise TheoryError {
  match (expected, argument) {
    (MetaTypeSymbolArgument, MetaType(ty)) =>
      match ty.view() {
        TyApp(symbol, []) => MetaTypeSymbol(symbol)
        _ =>
          fail_theory(
            MetaTypeMismatch,
            span,
            "meta argument has the wrong type",
          )
      }
    (MetaTypeArgument, MetaTypeSymbol(symbol)) if symbol.arity() == 0 =>
      MetaType(
        @logic.Ty::app(symbol, [], span) catch {
          _ =>
            fail_theory(
              MetaTypeMismatch,
              span,
              "meta type symbol cannot be converted to a type",
            )
        },
      )
    _ =>
      if meta_argument_type(argument) == expected {
        argument
      } else {
        fail_theory(MetaTypeMismatch, span, "meta argument has the wrong type")
      }
  }
}

///|
pub fn MetaDescriptor::apply(
  self : MetaDescriptor,
  arguments : ArrayView[MetaArgument],
  span : @identity.SourceSpan?,
) -> Meta raise TheoryError {
  if arguments.length() != self.argument_types.length() {
    fail_theory(BadMetaArity, span, "meta has the wrong number of arguments")
  }
  let converted : Array[MetaArgument] = []
  for index, argument in arguments {
    converted.push(
      convert_meta_argument(self.argument_types[index], argument, span),
    )
  }
  {
    name: self.name,
    argument_types: self.argument_types.copy(),
    exclusive: self.exclusive,
    arguments: converted,
  }
}

///|
pub fn Meta::new(name : BytesView, arguments : ArrayView[MetaArgument]) -> Meta {
  {
    name: name.to_owned(),
    argument_types: arguments.map(meta_argument_type),
    exclusive: false,
    arguments: arguments.to_owned(),
  }
}

///|
pub fn Meta::exclusive(
  name : BytesView,
  arguments : ArrayView[MetaArgument],
) -> Meta {
  {
    name: name.to_owned(),
    argument_types: arguments.map(meta_argument_type),
    exclusive: true,
    arguments: arguments.to_owned(),
  }
}

///|
pub fn Meta::view(self : Meta) -> MetaView {
  {
    name: self.name,
    argument_types: self.argument_types[:],
    exclusive: self.exclusive,
    arguments: self.arguments[:],
  }
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
fn known_meta_type(
  known : @logic.KnownMap,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  match ty.view() {
    TyVar(_) => ()
    TyApp(symbol, arguments) => {
      if !known.contains(TypeDependency(symbol)) {
        fail_theory(
          UnboundMetaArgument,
          span,
          "meta references an unknown type",
        )
      }
      for argument in arguments {
        known_meta_type(known, argument, span)
      }
    }
  }
}

///|
fn Meta::validate_known(
  self : Meta,
  known : @logic.KnownMap,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  for argument in self.arguments {
    let is_known = match argument {
      MetaType(ty) => {
        known_meta_type(known, ty, span)
        true
      }
      MetaTypeSymbol(symbol) => known.contains(TypeDependency(symbol))
      MetaLogicSymbol(symbol) => known.contains(LogicDependency(symbol))
      MetaPropositionSymbol(symbol) =>
        known.contains(PropositionDependency(symbol))
      MetaString(_) | MetaInteger(_) | MetaIdentifier(_) => true
    }
    if !is_known {
      fail_theory(
        UnboundMetaArgument,
        span,
        "meta references an unknown symbol",
      )
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

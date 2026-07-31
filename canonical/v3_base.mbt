// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv enum CanonicalV3DefinitionKind {
  V3Attribute
  V3Identifier
  V3TypeVariable
  V3TypeSymbol
  V3Type
  V3LogicVariable
  V3LogicSymbol
  V3PropositionSymbol
  V3Pattern
  V3Term
  V3Declaration
  V3Theory
  V3TheoryDeclaration
  V3Task
  V3ProgramTypeSymbol
  V3Region
  V3ProgramVariable
  V3ExceptionSymbol
  V3ComputationType
  V3RoutineSymbol
  V3ProgramPattern
  V3Expression
  V3ComputationExpression
  V3ProgramDeclaration
  V3Module
}

///|
fn CanonicalV3DefinitionKind::tag(self : CanonicalV3DefinitionKind) -> Int {
  match self {
    V3Attribute => 0
    V3Identifier => 1
    V3TypeVariable => 2
    V3TypeSymbol => 3
    V3Type => 4
    V3LogicVariable => 5
    V3LogicSymbol => 6
    V3PropositionSymbol => 7
    V3Pattern => 8
    V3Term => 9
    V3Declaration => 10
    V3Theory => 11
    V3TheoryDeclaration => 12
    V3Task => 13
    V3ProgramTypeSymbol => 14
    V3Region => 15
    V3ProgramVariable => 16
    V3ExceptionSymbol => 17
    V3ComputationType => 18
    V3RoutineSymbol => 19
    V3ProgramPattern => 20
    V3Expression => 21
    V3ComputationExpression => 22
    V3ProgramDeclaration => 23
    V3Module => 24
  }
}

///|
fn CanonicalV3DefinitionKind::name(
  self : CanonicalV3DefinitionKind,
) -> BytesView {
  match self {
    V3Attribute => b"attribute"
    V3Identifier => b"identifier"
    V3TypeVariable => b"type-variable"
    V3TypeSymbol => b"type-symbol"
    V3Type => b"type"
    V3LogicVariable => b"logic-variable"
    V3LogicSymbol => b"logic-symbol"
    V3PropositionSymbol => b"proposition-symbol"
    V3Pattern => b"pattern"
    V3Term => b"term"
    V3Declaration => b"declaration"
    V3Theory => b"theory"
    V3TheoryDeclaration => b"theory-declaration"
    V3Task => b"task"
    V3ProgramTypeSymbol => b"program-type-symbol"
    V3Region => b"region"
    V3ProgramVariable => b"program-variable"
    V3ExceptionSymbol => b"exception-symbol"
    V3ComputationType => b"computation-type"
    V3RoutineSymbol => b"routine-symbol"
    V3ProgramPattern => b"program-pattern"
    V3Expression => b"expression"
    V3ComputationExpression => b"computation-expression"
    V3ProgramDeclaration => b"program-declaration"
    V3Module => b"module"
  }
}

///|
priv struct CanonicalV3State {
  omit_generated_vcs : Bool
  retain_generated_type_vcs : Bool
  generated_type_vcs : Map[@logic.PrSymbol, Unit]
  selected_source_path : Bytes?
  definitions : Array[CanonicalValue]
  next_indices : FixedArray[UInt]
  semantic_indices : Map[(Int, @identity.SemanticId), UInt]
  identifier_indices : Map[@identity.SemanticId, UInt]
  attribute_indices : Map[Bytes, UInt]
  type_indices : Map[@logic.Ty, UInt]
  ity_indices : Map[@mlw.Ity, UInt]
  theory_indices : Map[@theory.TheoryKey, UInt]
  module_indices : Map[@theory.TheoryKey, UInt]
}

///|
fn CanonicalV3State::new() -> CanonicalV3State {
  CanonicalV3State::new_with_options(false, false, None)
}

///|
fn CanonicalV3State::new_omitting_generated_vcs() -> CanonicalV3State {
  CanonicalV3State::new_with_options(true, false, None)
}

///|
fn CanonicalV3State::new_omitting_generated_routine_vcs() -> CanonicalV3State {
  CanonicalV3State::new_with_options(true, true, None)
}

///|
fn CanonicalV3State::new_for_source(
  selected_source_path : BytesView,
) -> CanonicalV3State {
  CanonicalV3State::new_with_options(
    false,
    false,
    Some(selected_source_path.to_owned()),
  )
}

///|
fn CanonicalV3State::new_omitting_generated_vcs_for_source(
  selected_source_path : BytesView,
) -> CanonicalV3State {
  CanonicalV3State::new_with_options(
    true,
    false,
    Some(selected_source_path.to_owned()),
  )
}

///|
fn CanonicalV3State::new_omitting_generated_routine_vcs_for_source(
  selected_source_path : BytesView,
) -> CanonicalV3State {
  CanonicalV3State::new_with_options(
    true,
    true,
    Some(selected_source_path.to_owned()),
  )
}

///|
fn CanonicalV3State::new_with_options(
  omit_generated_vcs : Bool,
  retain_generated_type_vcs : Bool,
  selected_source_path : Bytes?,
) -> CanonicalV3State {
  {
    omit_generated_vcs,
    retain_generated_type_vcs,
    generated_type_vcs: Map([]),
    selected_source_path,
    definitions: [],
    next_indices: FixedArray::make(25, 0U),
    semantic_indices: Map([]),
    identifier_indices: Map([]),
    attribute_indices: Map([]),
    type_indices: Map([]),
    ity_indices: Map([]),
    theory_indices: Map([]),
    module_indices: Map([]),
  }
}

///|
fn CanonicalV3State::generated_source_span(
  self : CanonicalV3State,
  span : @identity.SourceSpan?,
) -> @identity.SourceSpan? {
  match (self.selected_source_path, span) {
    (Some(selected), Some(value)) =>
      if value.view().relative_path == selected {
        Some(value)
      } else {
        None
      }
    (_, value) => value
  }
}

///|
fn v3_bytes_have_prefix(value : BytesView, prefix : BytesView) -> Bool {
  value.length() >= prefix.length() && value[:prefix.length()] == prefix
}

///|
fn v3_is_generated_vc_proposition(symbol : @logic.PrSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => v3_bytes_have_prefix(attribute, b"expl:VC for "))
}

///|
fn v3_is_generated_vc_declaration(declaration : @logic.Decl) -> Bool {
  declaration.view() is Dprop(Pgoal, proposition, _) &&
  v3_is_generated_vc_proposition(proposition)
}

///|
fn v3_is_generated_vc_program_declaration(
  declaration : @mlw.ProgramDeclaration,
) -> Bool {
  guard declaration is PDpure(pure, _) else { return false }
  !pure.is_empty() && pure.all(v3_is_generated_vc_declaration)
}

///|
fn v3_node(tag : BytesView, fields : Array[CanonicalValue]) -> CanonicalValue {
  let values = [canonical_text(tag)]
  values.push_iter(fields.iter())
  canonical_array(values)
}

///|
fn v3_unit() -> CanonicalValue {
  v3_node(b"Unit", [])
}

///|
fn v3_bytes(value : BytesView) -> CanonicalValue {
  v3_node(b"Bytes", [canonical_hex(value)])
}

///|
fn v3_bool(value : Bool) -> CanonicalValue {
  v3_node(b"Boolean", [canonical_bool(value)])
}

///|
fn v3_integer_string(value : String) -> CanonicalValue {
  let bytes = @buffer.Buffer()
  bytes.write_string_utf8(value)
  v3_node(b"Integer", [canonical_text(bytes.to_bytes())])
}

///|
fn v3_int(value : Int) -> CanonicalValue {
  v3_integer_string(value.to_string())
}

///|
fn v3_int64(value : Int64) -> CanonicalValue {
  v3_integer_string(value.to_string())
}

///|
fn v3_bigint_text(value : String) -> CanonicalValue {
  v3_integer_string(value)
}

///|
fn v3_none() -> CanonicalValue {
  v3_node(b"Option.None", [])
}

///|
fn v3_some(value : CanonicalValue) -> CanonicalValue {
  v3_node(b"Option.Some", [value])
}

///|
fn v3_sequence(values : Array[CanonicalValue]) -> CanonicalValue {
  v3_node(b"Sequence", [canonical_array(values)])
}

///|
fn v3_product(values : Array[CanonicalValue]) -> CanonicalValue {
  v3_node(b"Product", [canonical_array(values)])
}

///|
fn v3_set(values : Array[CanonicalValue]) -> CanonicalValue {
  values.sort_by((left, right) => {
    encode_canonical_value_without_lf(left).lexical_compare(
      encode_canonical_value_without_lf(right),
    )
  })
  v3_node(b"Set", [canonical_array(values)])
}

///|
fn v3_map(entries : Array[(CanonicalValue, CanonicalValue)]) -> CanonicalValue {
  v3_node(b"Map", [canonical_semantic_map(entries)])
}

///|
fn v3_source_span(span : @identity.SourceSpan) -> CanonicalValue {
  let view = span.view()
  v3_node(b"SourceSpan", [
    canonical_hex(view.relative_path),
    Signed(view.start_byte.to_int64()),
    Signed(view.end_byte.to_int64()),
    Signed(view.start_line),
    Signed(view.start_column),
    Signed(view.end_line),
    Signed(view.end_column),
  ])
}

///|
fn v3_source_span_option(span : @identity.SourceSpan?) -> CanonicalValue {
  match span {
    None => v3_none()
    Some(value) => v3_some(v3_source_span(value))
  }
}

///|
fn v3_origin(
  state : CanonicalV3State,
  origin : @identity.Origin,
) -> CanonicalValue {
  match origin.view() {
    UserOrigin(name, span, attributes) =>
      v3_node(b"Origin.User", [
        v3_bytes(name),
        v3_source_span_option(span),
        v3_set([ for attribute in attributes => v3_bytes(attribute) ]),
      ])
    GeneratedOrigin(stage, name, span, attributes) =>
      v3_node(b"Origin.Generated", [
        v3_bytes(stage.canonical_name()),
        v3_bytes(name),
        v3_source_span_option(state.generated_source_span(span)),
        v3_set([ for attribute in attributes => v3_bytes(attribute) ]),
      ])
  }
}

///|
fn CanonicalV3State::reserve(
  self : CanonicalV3State,
  kind : CanonicalV3DefinitionKind,
) -> (UInt, Int) {
  let tag = kind.tag()
  let index = self.next_indices[tag]
  self.next_indices[tag] = index + 1U
  let position = self.definitions.length()
  self.definitions.push(v3_unit())
  (index, position)
}

///|
fn CanonicalV3State::fill(
  self : CanonicalV3State,
  kind : CanonicalV3DefinitionKind,
  index : UInt,
  position : Int,
  value : CanonicalValue,
) -> Unit {
  self.definitions[position] = v3_node(b"Definition", [
    canonical_text(kind.name()),
    Unsigned(index),
    value,
  ])
}

///|
fn v3_reference(
  kind : CanonicalV3DefinitionKind,
  index : UInt,
) -> CanonicalValue {
  v3_node(b"Reference", [canonical_text(kind.name()), Unsigned(index)])
}

///|
fn v3_de_bruijn(index : UInt) -> CanonicalValue {
  v3_node(b"DeBruijn", [Unsigned(index)])
}

///|
fn CanonicalV3State::semantic_index(
  self : CanonicalV3State,
  kind : CanonicalV3DefinitionKind,
  id : @identity.SemanticId,
) -> UInt? {
  self.semantic_indices.get((kind.tag(), id))
}

///|
fn CanonicalV3State::remember_semantic_index(
  self : CanonicalV3State,
  kind : CanonicalV3DefinitionKind,
  id : @identity.SemanticId,
  index : UInt,
) -> Unit {
  self.semantic_indices[(kind.tag(), id)] = index
}

///|
fn v3_attribute(
  state : CanonicalV3State,
  attribute : BytesView,
) -> CanonicalValue {
  let owned = attribute.to_owned()
  match state.attribute_indices.get(owned) {
    Some(index) => v3_reference(V3Attribute, index)
    None => {
      let (index, position) = state.reserve(V3Attribute)
      state.attribute_indices[owned] = index
      state.fill(
        V3Attribute,
        index,
        position,
        v3_node(b"Ident.attribute", [v3_bytes(attribute)]),
      )
      v3_reference(V3Attribute, index)
    }
  }
}

///|
fn v3_attributes(
  state : CanonicalV3State,
  attributes : ArrayView[Bytes],
) -> CanonicalValue {
  v3_set([ for attribute in attributes => v3_attribute(state, attribute) ])
}

///|
fn v3_identifier(
  state : CanonicalV3State,
  id : @identity.SemanticId,
  origin : @identity.Origin,
) -> CanonicalValue {
  match state.identifier_indices.get(id) {
    Some(index) => v3_reference(V3Identifier, index)
    None => {
      let (index, position) = state.reserve(V3Identifier)
      state.identifier_indices[id] = index
      let ident = v3_node(b"Ident.ident", [
        v3_bytes(origin.display_name()),
        v3_attributes(state, origin.attributes()),
        v3_source_span_option(origin.identifier_source_span()),
      ])
      state.fill(
        V3Identifier,
        index,
        position,
        v3_product([ident, v3_origin(state, origin)]),
      )
      v3_reference(V3Identifier, index)
    }
  }
}

///|
fn CanonicalV3State::finish(
  self : CanonicalV3State,
  roots : Array[CanonicalValue],
) -> CanonicalJson {
  encode_canonical_value(
    v3_node(b"GraphV3", [
      canonical_array(roots),
      canonical_array(self.definitions),
    ]),
  )
}

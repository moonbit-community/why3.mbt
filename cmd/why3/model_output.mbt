// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn model_symbol_json(symbol : @z3.SmtModelSymbol) -> String {
  match symbol {
    UserSymbol(name) =>
      "{\"kind\":\"user\",\"name_hex\":\"" + bytes_hex_string(name) + "\"}"
    ProverSymbol(name) =>
      "{\"kind\":\"prover\",\"name_hex\":\"" + bytes_hex_string(name) + "\"}"
  }
}

///|
fn model_index_json(index : @z3.SmtModelIndex) -> String {
  match index {
    NumeralIndex(value) =>
      "{\"kind\":\"numeral\",\"value\":\"" + value.to_string() + "\"}"
    SymbolIndex(symbol) =>
      "{\"kind\":\"symbol\",\"symbol\":" + model_symbol_json(symbol) + "}"
  }
}

///|
fn model_identifier_json(identifier : @z3.SmtModelIdentifier) -> String {
  match identifier {
    SimpleIdentifier(symbol) =>
      "{\"kind\":\"simple\",\"symbol\":" + model_symbol_json(symbol) + "}"
    IndexedIdentifier(symbol, indices) =>
      "{\"kind\":\"indexed\",\"symbol\":" +
      model_symbol_json(symbol) +
      ",\"indices\":[" +
      indices.map(model_index_json).join(",") +
      "]}"
  }
}

///|
fn model_sort_json(sort : @z3.SmtModelSort) -> String {
  match sort {
    StringSort => "{\"kind\":\"String\"}"
    RegLanSort => "{\"kind\":\"RegLan\"}"
    IntegerSort => "{\"kind\":\"Int\"}"
    RealSort => "{\"kind\":\"Real\"}"
    RoundingModeSort => "{\"kind\":\"RoundingMode\"}"
    BooleanSort => "{\"kind\":\"Bool\"}"
    BitVectorSort(length) =>
      "{\"kind\":\"BitVec\",\"length\":" + length.to_string() + "}"
    FloatingPointSort(exponent, significand) =>
      "{\"kind\":\"FloatingPoint\",\"exponent\":" +
      exponent.to_string() +
      ",\"significand\":" +
      significand.to_string() +
      "}"
    ArraySort(index, element) =>
      "{\"kind\":\"Array\",\"index\":" +
      model_sort_json(index) +
      ",\"element\":" +
      model_sort_json(element) +
      "}"
    SimpleSort(identifier) =>
      "{\"kind\":\"simple\",\"identifier\":" +
      model_identifier_json(identifier) +
      "}"
    AppliedSort(identifier, arguments) =>
      "{\"kind\":\"applied\",\"identifier\":" +
      model_identifier_json(identifier) +
      ",\"arguments\":[" +
      arguments.map(model_sort_json).join(",") +
      "]}"
  }
}

///|
fn model_bitvector_json(value : @z3.SmtModelBitVector) -> String {
  "{\"value\":\"" +
  value.value.to_string() +
  "\",\"bit_length\":" +
  value.bit_length.to_string() +
  ",\"verbatim_hex\":\"" +
  bytes_hex_string(value.verbatim) +
  "\"}"
}

///|
fn model_real_json(value : @z3.SmtModelReal) -> String {
  "{\"significand\":\"" +
  value.significand.to_string() +
  "\",\"decimal_scale\":" +
  value.decimal_scale.to_string() +
  ",\"verbatim_hex\":\"" +
  bytes_hex_string(value.verbatim) +
  "\"}"
}

///|
fn model_float_value_json(value : @z3.SmtModelFloatValue) -> String {
  match value {
    PlusInfinity => "{\"kind\":\"plus-infinity\"}"
    MinusInfinity => "{\"kind\":\"minus-infinity\"}"
    PlusZero => "{\"kind\":\"plus-zero\"}"
    MinusZero => "{\"kind\":\"minus-zero\"}"
    NotANumber => "{\"kind\":\"nan\"}"
    FloatBits(sign, exponent, mantissa) =>
      "{\"kind\":\"bits\",\"sign\":" +
      model_bitvector_json(sign) +
      ",\"exponent\":" +
      model_bitvector_json(exponent) +
      ",\"mantissa\":" +
      model_bitvector_json(mantissa) +
      "}"
  }
}

///|
fn model_constant_json(constant : @z3.SmtModelConstant) -> String {
  match constant {
    BooleanConstant(value) =>
      "{\"kind\":\"boolean\",\"value\":" +
      (if value { "true" } else { "false" }) +
      "}"
    StringConstant(value) =>
      "{\"kind\":\"string\",\"value_hex\":\"" + bytes_hex_string(value) + "\"}"
    IntegerConstant(value) =>
      "{\"kind\":\"integer\",\"value\":\"" +
      value.value.to_string() +
      "\",\"verbatim_hex\":\"" +
      bytes_hex_string(value.verbatim) +
      "\"}"
    RealConstant(value) =>
      "{\"kind\":\"real\",\"value\":" + model_real_json(value) + "}"
    FloatConstant(value) =>
      "{\"kind\":\"float\",\"exponent_size\":" +
      value.exponent_size.to_string() +
      ",\"significand_size\":" +
      value.significand_size.to_string() +
      ",\"value\":" +
      model_float_value_json(value.value) +
      "}"
    BitVectorConstant(value) =>
      "{\"kind\":\"bitvector\",\"value\":" + model_bitvector_json(value) + "}"
    FractionConstant(value) =>
      "{\"kind\":\"fraction\",\"numerator\":" +
      model_real_json(value.numerator) +
      ",\"denominator\":" +
      model_real_json(value.denominator) +
      ",\"verbatim_hex\":\"" +
      bytes_hex_string(value.verbatim) +
      "\"}"
  }
}

///|
fn model_qualified_identifier_json(
  identifier : @z3.SmtModelQualifiedIdentifier,
) -> String {
  match identifier {
    UnannotatedIdentifier(identifier) =>
      "{\"kind\":\"unannotated\",\"identifier\":" +
      model_identifier_json(identifier) +
      "}"
    AnnotatedIdentifier(identifier, sort) =>
      "{\"kind\":\"annotated\",\"identifier\":" +
      model_identifier_json(identifier) +
      ",\"sort\":" +
      model_sort_json(sort) +
      "}"
  }
}

///|
fn model_term_json(term : @z3.SmtModelTerm) -> String {
  match term {
    ConstantTerm(constant) =>
      "{\"kind\":\"constant\",\"constant\":" +
      model_constant_json(constant) +
      "}"
    VariableTerm(identifier) =>
      "{\"kind\":\"variable\",\"identifier\":" +
      model_qualified_identifier_json(identifier) +
      "}"
    ApplicationTerm(identifier, arguments) =>
      "{\"kind\":\"application\",\"identifier\":" +
      model_qualified_identifier_json(identifier) +
      ",\"arguments\":[" +
      arguments.map(model_term_json).join(",") +
      "]}"
    ConditionalTerm(condition, consequent, alternative) =>
      "{\"kind\":\"ite\",\"condition\":" +
      model_term_json(condition) +
      ",\"consequent\":" +
      model_term_json(consequent) +
      ",\"alternative\":" +
      model_term_json(alternative) +
      "}"
    ArrayTerm(index_sort, element_sort, elements) => {
      let indices = elements.indices.map(entry => {
        "{\"index\":" +
        model_term_json(entry.0) +
        ",\"value\":" +
        model_term_json(entry.1) +
        "}"
      })
      "{\"kind\":\"array\",\"index_sort\":" +
      model_sort_json(index_sort) +
      ",\"element_sort\":" +
      model_sort_json(element_sort) +
      ",\"indices\":[" +
      indices.join(",") +
      "],\"others\":" +
      model_term_json(elements.others) +
      "}"
    }
    AsArrayTerm(function_) =>
      "{\"kind\":\"as-array\",\"function\":" + model_term_json(function_) + "}"
    UnparsedTerm(value) =>
      "{\"kind\":\"unparsed\",\"value_hex\":\"" +
      bytes_hex_string(value) +
      "\"}"
  }
}

///|
fn model_source_span_json(span : @identity.SourceSpan) -> String {
  let view = span.view()
  "{\"path_hex\":\"" +
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
  view.end_column.to_string() +
  "}"
}

///|
fn model_origin_json(origin : @identity.Origin?) -> String {
  match origin {
    None => "null"
    Some(origin) => {
      let (kind, stage) = match origin.view() {
        UserOrigin(_, _, _) => ("user", "null")
        GeneratedOrigin(stage, _, _, _) =>
          ("generated", "\"" + display_bytes(stage.canonical_name()) + "\"")
      }
      let span = match origin.source_span() {
        None => "null"
        Some(span) => model_source_span_json(span)
      }
      "{\"kind\":\"" +
      kind +
      "\",\"stage\":" +
      stage +
      ",\"name_hex\":\"" +
      bytes_hex_string(origin.display_name()) +
      "\",\"span\":" +
      span +
      "}"
    }
  }
}

///|
fn model_value_json(value : @z3.SmtModelValue) -> String {
  let definition = value.definition
  let arguments = definition.arguments.map(argument => {
    "{\"name\":" +
    model_symbol_json(argument.0) +
    ",\"sort\":" +
    model_sort_json(argument.1) +
    "}"
  })
  "{\"name_hex\":\"" +
  bytes_hex_string(definition.name) +
  "\",\"arguments\":[" +
  arguments.join(",") +
  "],\"result\":" +
  model_sort_json(definition.result) +
  ",\"body\":" +
  model_term_json(definition.body) +
  ",\"matched_source_symbol\":" +
  (if value.semantic_id is Some(_) { "true" } else { "false" }) +
  ",\"origin\":" +
  model_origin_json(value.origin) +
  "}"
}

///|
fn model_values_json(values : ArrayView[@z3.SmtModelValue]) -> String {
  "[" + values.map(model_value_json).join(",") + "]"
}

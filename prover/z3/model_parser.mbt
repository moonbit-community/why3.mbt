// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum ModelParseErrorKind {
  UnexpectedEndOfModel
  UnexpectedClosingParenthesis
  UnclosedModelList
  UnclosedQuotedSymbol
  UnclosedModelString
  ExcessiveModelNesting
  MultipleModels
} derive(Eq, Debug)

///|
pub(all) struct ModelParseDiagnostic {
  kind : ModelParseErrorKind
  byte_offset : Int
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror ModelParseError {
  ModelParseError(ModelParseDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_model_parse(
  kind : ModelParseErrorKind,
  byte_offset : Int,
  message : String,
) -> A raise ModelParseError {
  raise ModelParseError({ kind, byte_offset, message })
}

///|
pub(all) enum SmtModelSymbol {
  UserSymbol(Bytes)
  ProverSymbol(Bytes)
} derive(Eq, Debug)

///|
pub(all) enum SmtModelIndex {
  NumeralIndex(BigInt)
  SymbolIndex(SmtModelSymbol)
} derive(Eq, Debug)

///|
pub(all) enum SmtModelIdentifier {
  SimpleIdentifier(SmtModelSymbol)
  IndexedIdentifier(SmtModelSymbol, Array[SmtModelIndex])
} derive(Eq, Debug)

///|
pub(all) enum SmtModelSort {
  StringSort
  RegLanSort
  IntegerSort
  RealSort
  RoundingModeSort
  BooleanSort
  BitVectorSort(Int)
  FloatingPointSort(Int, Int)
  ArraySort(SmtModelSort, SmtModelSort)
  SimpleSort(SmtModelIdentifier)
  AppliedSort(SmtModelIdentifier, Array[SmtModelSort])
} derive(Eq, Debug)

///|
pub(all) struct SmtModelInteger {
  value : BigInt
  verbatim : Bytes
} derive(Eq, Debug)

///|
pub(all) struct SmtModelReal {
  significand : BigInt
  decimal_scale : Int
  verbatim : Bytes
} derive(Eq, Debug)

///|
pub(all) struct SmtModelBitVector {
  value : BigInt
  bit_length : Int
  verbatim : Bytes
} derive(Eq, Debug)

///|
pub(all) struct SmtModelFraction {
  numerator : SmtModelReal
  denominator : SmtModelReal
  verbatim : Bytes
} derive(Eq, Debug)

///|
pub(all) enum SmtModelFloatValue {
  PlusInfinity
  MinusInfinity
  PlusZero
  MinusZero
  NotANumber
  FloatBits(SmtModelBitVector, SmtModelBitVector, SmtModelBitVector)
} derive(Eq, Debug)

///|
pub(all) struct SmtModelFloat {
  exponent_size : Int
  significand_size : Int
  value : SmtModelFloatValue
} derive(Eq, Debug)

///|
pub(all) enum SmtModelConstant {
  BooleanConstant(Bool)
  StringConstant(Bytes)
  IntegerConstant(SmtModelInteger)
  RealConstant(SmtModelReal)
  FloatConstant(SmtModelFloat)
  BitVectorConstant(SmtModelBitVector)
  FractionConstant(SmtModelFraction)
} derive(Eq, Debug)

///|
pub(all) enum SmtModelQualifiedIdentifier {
  UnannotatedIdentifier(SmtModelIdentifier)
  AnnotatedIdentifier(SmtModelIdentifier, SmtModelSort)
} derive(Eq, Debug)

///|
pub(all) struct SmtModelArrayElements {
  indices : Array[(SmtModelTerm, SmtModelTerm)]
  others : SmtModelTerm
} derive(Eq, Debug)

///|
pub(all) enum SmtModelTerm {
  ConstantTerm(SmtModelConstant)
  VariableTerm(SmtModelQualifiedIdentifier)
  ApplicationTerm(SmtModelQualifiedIdentifier, Array[SmtModelTerm])
  ConditionalTerm(SmtModelTerm, SmtModelTerm, SmtModelTerm)
  ArrayTerm(SmtModelSort, SmtModelSort, SmtModelArrayElements)
  AsArrayTerm(SmtModelTerm)
  UnparsedTerm(Bytes)
} derive(Eq, Debug)

///|
pub(all) struct SmtModelFunctionDefinition {
  name : Bytes
  arguments : Array[(SmtModelSymbol, SmtModelSort)]
  result : SmtModelSort
  body : SmtModelTerm
} derive(Eq, Debug)

///|
pub(all) struct SmtModel {
  definitions : Array[SmtModelFunctionDefinition]
} derive(Eq, Debug)

///|
pub fn SmtModel::is_empty(self : SmtModel) -> Bool {
  self.definitions.is_empty()
}

///|
pub fn SmtModel::definitions(
  self : SmtModel,
) -> ArrayView[SmtModelFunctionDefinition] {
  self.definitions[:]
}

///|
pub(all) struct SmtModelValue {
  definition : SmtModelFunctionDefinition
  semantic_id : @identity.SemanticId?
  origin : @identity.Origin?
} derive(Eq)

///|
priv enum ModelSexp {
  ModelAtom(Bytes)
  ModelList(Array[ModelSexp])
} derive(Eq, Debug)

///|
priv struct ModelSexpReader {
  input : Bytes
  mut index : Int
  mut depth : Int
}

///|
fn ModelSexpReader::new(input : BytesView) -> ModelSexpReader {
  { input: input.to_owned(), index: 0, depth: 0 }
}

///|
fn model_ascii_space(byte : Byte) -> Bool {
  byte == b' ' || byte == b'\t' || byte == b'\r' || byte == b'\n'
}

///|
fn ModelSexpReader::skip_layout(self : ModelSexpReader) -> Unit {
  while self.index < self.input.length() {
    if model_ascii_space(self.input[self.index]) {
      self.index = self.index + 1
      continue
    }
    if self.input[self.index] == b';' {
      while self.index < self.input.length() && self.input[self.index] != b'\n' {
        self.index = self.index + 1
      }
      continue
    }
    break
  }
}

///|
fn ModelSexpReader::quoted_atom(
  self : ModelSexpReader,
  delimiter : Byte,
) -> Bytes raise ModelParseError {
  let start = self.index
  self.index = self.index + 1
  while self.index < self.input.length() {
    let byte = self.input[self.index]
    if delimiter == b'"' &&
      byte == b'"' &&
      self.index + 1 < self.input.length() &&
      self.input[self.index + 1] == b'"' {
      self.index = self.index + 2
      continue
    }
    if delimiter == b'|' &&
      byte == b'\\' &&
      self.index + 1 < self.input.length() {
      self.index = self.index + 2
      continue
    }
    self.index = self.index + 1
    if byte == delimiter {
      return self.input[start:self.index].to_owned()
    }
  }
  fail_model_parse(
    if delimiter == b'"' {
      UnclosedModelString
    } else {
      UnclosedQuotedSymbol
    },
    start,
    if delimiter == b'"' {
      "unterminated SMT-LIB string in model"
    } else {
      "unterminated quoted SMT-LIB symbol in model"
    },
  )
}

///|
fn ModelSexpReader::plain_atom(
  self : ModelSexpReader,
) -> Bytes raise ModelParseError {
  let start = self.index
  while self.index < self.input.length() {
    let byte = self.input[self.index]
    if model_ascii_space(byte) || byte == b'(' || byte == b')' || byte == b';' {
      break
    }
    self.index = self.index + 1
  }
  if self.index == start {
    fail_model_parse(
      UnexpectedEndOfModel,
      start,
      "expected an SMT-LIB atom in model",
    )
  }
  self.input[start:self.index].to_owned()
}

///|
fn ModelSexpReader::one(
  self : ModelSexpReader,
) -> ModelSexp raise ModelParseError {
  self.skip_layout()
  if self.index >= self.input.length() {
    fail_model_parse(
      UnexpectedEndOfModel,
      self.index,
      "unexpected end of SMT-LIB model",
    )
  }
  match self.input[self.index] {
    b')' =>
      fail_model_parse(
        UnexpectedClosingParenthesis,
        self.index,
        "unexpected closing parenthesis in SMT-LIB model",
      )
    b'(' => {
      let start = self.index
      self.index = self.index + 1
      self.depth = self.depth + 1
      if self.depth > 1024 {
        fail_model_parse(
          ExcessiveModelNesting,
          start,
          "SMT-LIB model nesting exceeds 1024 lists",
        )
      }
      let values : Array[ModelSexp] = []
      while true {
        self.skip_layout()
        if self.index >= self.input.length() {
          fail_model_parse(
            UnclosedModelList,
            start,
            "unterminated list in SMT-LIB model",
          )
        }
        if self.input[self.index] == b')' {
          self.index = self.index + 1
          self.depth = self.depth - 1
          return ModelList(values)
        }
        values.push(self.one())
      }
      ModelList(values)
    }
    b'"' => ModelAtom(self.quoted_atom(b'"'))
    b'|' => ModelAtom(self.quoted_atom(b'|'))
    _ => ModelAtom(self.plain_atom())
  }
}

///|
fn ModelSexpReader::all(
  self : ModelSexpReader,
) -> Array[ModelSexp] raise ModelParseError {
  let result : Array[ModelSexp] = []
  while true {
    self.skip_layout()
    if self.index >= self.input.length() {
      return result
    }
    result.push(self.one())
  }
  result
}

///|
fn model_bytes_equal(left : BytesView, right : BytesView) -> Bool {
  left == right
}

///|
fn model_atom(value : ModelSexp) -> Bytes? {
  match value {
    ModelAtom(atom) => Some(atom)
    ModelList(_) => None
  }
}

///|
fn model_atom_is(value : ModelSexp, expected : BytesView) -> Bool {
  model_atom(value) is Some(actual) && model_bytes_equal(actual, expected)
}

///|
fn model_contains_definition(value : ModelSexp) -> Bool {
  match value {
    ModelAtom(_) => false
    ModelList(values) =>
      values.any(value => {
        model_atom_is(value, b"define-fun") || model_contains_definition(value)
      })
  }
}

///|
fn model_sexp_bytes(value : ModelSexp) -> Bytes {
  match value {
    ModelAtom(atom) => atom
    ModelList(values) => {
      let buffer = @buffer.Buffer()
      buffer.write_byte(b'(')
      for index, value in values {
        if index > 0 {
          buffer.write_byte(b' ')
        }
        buffer.write_bytes(model_sexp_bytes(value))
      }
      buffer.write_byte(b')')
      buffer.to_bytes()
    }
  }
}

///|
fn model_is_digits(value : BytesView) -> Bool {
  if value.is_empty() {
    return false
  }
  for byte in value {
    if byte < b'0' || byte > b'9' {
      return false
    }
  }
  true
}

///|
fn model_decimal_int(value : BytesView) -> Int? {
  if !model_is_digits(value) {
    return None
  }
  let mut result = 0
  for byte in value {
    let digit = byte.to_int() - b'0'.to_int()
    if result > (2147483647 - digit) / 10 {
      return None
    }
    result = result * 10 + digit
  }
  Some(result)
}

///|
fn model_bigint(value : BytesView, radix? : Int = 10) -> BigInt? {
  if value.is_empty() {
    return None
  }
  for byte in value {
    let valid = if radix == 2 {
      byte == b'0' || byte == b'1'
    } else if radix == 16 {
      (byte >= b'0' && byte <= b'9') ||
      (byte >= b'a' && byte <= b'f') ||
      (byte >= b'A' && byte <= b'F')
    } else {
      byte >= b'0' && byte <= b'9'
    }
    if !valid {
      return None
    }
  }
  let text = @utf8.decode(value) catch { _ => return None }
  Some(BigInt::from_string(text, radix~))
}

///|
fn model_is_prover_symbol(value : BytesView) -> Bool {
  if value.is_empty() {
    return false
  }
  if value[0] == b'@' || value[0] == b'.' {
    return true
  }
  let mut first = -1
  let mut second = -1
  for index, byte in value {
    if byte == b'!' {
      if first < 0 {
        first = index
      } else if second < 0 {
        second = index
      } else {
        return false
      }
    }
  }
  first > 0 &&
  second > first + 1 &&
  model_bytes_equal(value[first + 1:second], b"val") &&
  second + 1 < value.length()
}

///|
fn model_unquote_symbol(value : BytesView) -> Bytes? {
  if value.length() >= 2 &&
    value[0] == b'|' &&
    value[value.length() - 1] == b'|' {
    Some(value[1:value.length() - 1].to_owned())
  } else {
    None
  }
}

///|
fn model_symbol(value : ModelSexp) -> SmtModelSymbol? {
  guard model_atom(value) is Some(atom) else { return None }
  let normalized = model_unquote_symbol(atom).unwrap_or(atom)
  if normalized.is_empty() {
    return None
  }
  if model_is_prover_symbol(normalized) {
    Some(ProverSymbol(normalized))
  } else {
    Some(UserSymbol(normalized))
  }
}

///|
fn model_identifier(value : ModelSexp) -> SmtModelIdentifier? {
  if model_symbol(value) is Some(symbol) {
    return Some(SimpleIdentifier(symbol))
  }
  guard value is ModelList(values) &&
    values.length() >= 3 &&
    model_atom_is(values[0], b"_") &&
    model_symbol(values[1]) is Some(symbol) else {
    return None
  }
  let indices : Array[SmtModelIndex] = []
  let source : Array[ModelSexp] = if values.length() == 3 &&
    values[2] is ModelList(nested) {
    nested
  } else {
    values[2:].to_owned()
  }
  for value in source {
    match value {
      ModelAtom(atom) =>
        match model_bigint(atom) {
          Some(value) => indices.push(NumeralIndex(value))
          None =>
            match model_symbol(value) {
              Some(symbol) => indices.push(SymbolIndex(symbol))
              None => return None
            }
        }
      ModelList(_) => return None
    }
  }
  Some(IndexedIdentifier(symbol, indices))
}

///|
fn model_sort(value : ModelSexp) -> SmtModelSort? {
  match value {
    ModelAtom(atom) =>
      match atom {
        b"String" => Some(StringSort)
        b"RegLan" => Some(RegLanSort)
        b"Int" => Some(IntegerSort)
        b"Real" => Some(RealSort)
        b"RoundingMode" => Some(RoundingModeSort)
        b"Bool" => Some(BooleanSort)
        b"Float16" => Some(FloatingPointSort(5, 11))
        b"Float32" => Some(FloatingPointSort(8, 24))
        b"Float64" => Some(FloatingPointSort(11, 53))
        b"Float128" => Some(FloatingPointSort(15, 113))
        _ => model_identifier(value).map(identifier => SimpleSort(identifier))
      }
    ModelList(values) => {
      if values is [ModelAtom(b"_"), ModelAtom(b"BitVec"), ModelAtom(length)] &&
        model_decimal_int(length) is Some(length) {
        return Some(BitVectorSort(length))
      }
      if values
        is [
          ModelAtom(b"_"),
          ModelAtom(b"FloatingPoint"),
          ModelAtom(exponent),
          ModelAtom(significand),
        ] &&
        model_decimal_int(exponent) is Some(exponent) &&
        model_decimal_int(significand) is Some(significand) {
        return Some(FloatingPointSort(exponent, significand))
      }
      if values is [ModelAtom(b"Array"), index, element] &&
        model_sort(index) is Some(index_sort) &&
        model_sort(element) is Some(element_sort) {
        return Some(ArraySort(index_sort, element_sort))
      }
      guard !values.is_empty() &&
        model_identifier(values[0]) is Some(identifier) else {
        return None
      }
      let arguments : Array[SmtModelSort] = []
      for value in values[1:] {
        match model_sort(value) {
          Some(sort) => arguments.push(sort)
          None => return None
        }
      }
      Some(AppliedSort(identifier, arguments))
    }
  }
}

///|
fn model_signed_integer(value : ModelSexp) -> SmtModelInteger? {
  match value {
    ModelAtom(atom) =>
      model_bigint(atom).map(value => { value, verbatim: atom })
    ModelList([ModelAtom(b"-"), ModelAtom(atom)]) =>
      model_bigint(atom).map(value => { value: -value, verbatim: b"-" + atom })
    _ => None
  }
}

///|
fn model_real_parts(value : BytesView) -> (BigInt, Int)? {
  let mut separator = -1
  for index, byte in value {
    if byte == b'.' {
      if separator >= 0 {
        return None
      }
      separator = index
    } else if byte < b'0' || byte > b'9' {
      return None
    }
  }
  if separator <= 0 || separator + 1 >= value.length() {
    return None
  }
  let digits = value[:separator].to_owned() + value[separator + 1:].to_owned()
  model_bigint(digits).map(significand => {
    (significand, value.length() - separator - 1)
  })
}

///|
fn model_signed_real(value : ModelSexp) -> SmtModelReal? {
  match value {
    ModelAtom(atom) =>
      model_real_parts(atom).map(parts => {
        significand: parts.0,
        decimal_scale: parts.1,
        verbatim: atom,
      })
    ModelList([ModelAtom(b"-"), ModelAtom(atom)]) =>
      model_real_parts(atom).map(parts => {
        significand: -parts.0,
        decimal_scale: parts.1,
        verbatim: b"-" + atom,
      })
    _ => None
  }
}

///|
fn model_fraction_component(value : ModelSexp) -> SmtModelReal? {
  match model_signed_real(value) {
    Some(real) => Some(real)
    None =>
      model_signed_integer(value).map(integer => {
        significand: integer.value,
        decimal_scale: 0,
        verbatim: integer.verbatim,
      })
  }
}

///|
fn model_fraction(value : ModelSexp) -> SmtModelFraction? {
  let (negative, fraction) = match value {
    ModelList([ModelAtom(b"-"), fraction]) => (true, fraction)
    _ => (false, value)
  }
  guard fraction
    is ModelList([ModelAtom(b"/"), numerator_source, denominator_source]) &&
    model_fraction_component(numerator_source) is Some(numerator) &&
    model_fraction_component(denominator_source) is Some(denominator) else {
    return None
  }
  let numerator = if negative {
    {
      ..numerator,
      significand: -numerator.significand,
      verbatim: b"-" + numerator.verbatim,
    }
  } else {
    numerator
  }
  Some({
    numerator,
    denominator,
    verbatim: numerator.verbatim + b"/" + denominator.verbatim,
  })
}

///|
fn model_bitvector(value : ModelSexp) -> SmtModelBitVector? {
  match value {
    ModelAtom(atom) if atom.length() > 2 && atom[0] == b'#' && atom[1] == b'b' =>
      model_bigint(atom[2:], radix=2).map(value => {
        value,
        bit_length: atom.length() - 2,
        verbatim: atom,
      })
    ModelAtom(atom) if atom.length() > 2 && atom[0] == b'#' && atom[1] == b'x' =>
      model_bigint(atom[2:], radix=16).map(value => {
        value,
        bit_length: (atom.length() - 2) * 4,
        verbatim: atom,
      })
    ModelList([ModelAtom(b"_"), ModelAtom(number), ModelAtom(length)]) if number.length() >
      2 &&
      number[0] == b'b' &&
      number[1] == b'v' &&
      model_bigint(number[2:]) is Some(integer_value) &&
      model_decimal_int(length) is Some(bit_length) =>
      Some({
        value: integer_value,
        bit_length,
        verbatim: model_sexp_bytes(value),
      })
    _ => None
  }
}

///|
fn model_float(value : ModelSexp) -> SmtModelFloat? {
  guard value is ModelList(values) else { return None }
  if values
    is [
      ModelAtom(b"_"),
      ModelAtom(kind),
      ModelAtom(exponent),
      ModelAtom(significand),
    ] &&
    model_decimal_int(exponent) is Some(exponent_size) &&
    model_decimal_int(significand) is Some(significand_size) {
    let value = match kind {
      b"+zero" => PlusZero
      b"-zero" => MinusZero
      b"+oo" => PlusInfinity
      b"-oo" => MinusInfinity
      b"NaN" => NotANumber
      _ => return None
    }
    return Some({ exponent_size, significand_size, value })
  }
  if values is [ModelAtom(b"fp"), sign, exponent, mantissa] &&
    model_bitvector(sign) is Some(sign) &&
    model_bitvector(exponent) is Some(exponent) &&
    model_bitvector(mantissa) is Some(mantissa) {
    return Some({
      exponent_size: exponent.bit_length,
      significand_size: sign.bit_length + mantissa.bit_length,
      value: FloatBits(sign, exponent, mantissa),
    })
  }
  None
}

///|
fn model_string_constant(value : ModelSexp) -> Bytes? {
  guard value is ModelAtom(atom) &&
    atom.length() >= 2 &&
    atom[0] == b'"' &&
    atom[atom.length() - 1] == b'"' else {
    return None
  }
  Some(atom[1:atom.length() - 1].to_owned())
}

///|
fn model_constant(value : ModelSexp) -> SmtModelConstant? {
  if model_signed_integer(value) is Some(integer) {
    return Some(IntegerConstant(integer))
  }
  if model_signed_real(value) is Some(real) {
    return Some(RealConstant(real))
  }
  if model_fraction(value) is Some(fraction) {
    return Some(FractionConstant(fraction))
  }
  if model_bitvector(value) is Some(bitvector) {
    return Some(BitVectorConstant(bitvector))
  }
  if model_float(value) is Some(float) {
    return Some(FloatConstant(float))
  }
  if model_atom_is(value, b"true") {
    return Some(BooleanConstant(true))
  }
  if model_atom_is(value, b"false") {
    return Some(BooleanConstant(false))
  }
  model_string_constant(value).map(value => StringConstant(value))
}

///|
fn model_qualified_identifier(
  value : ModelSexp,
) -> SmtModelQualifiedIdentifier? {
  if model_identifier(value) is Some(identifier) {
    return Some(UnannotatedIdentifier(identifier))
  }
  guard value is ModelList([ModelAtom(b"as"), identifier_source, sort_source]) &&
    model_identifier(identifier_source) is Some(identifier) &&
    model_sort(sort_source) is Some(sort) else {
    return None
  }
  Some(AnnotatedIdentifier(identifier, sort))
}

///|
fn model_array(value : ModelSexp) -> SmtModelTerm? {
  if value is ModelList([ModelAtom(b"_"), ModelAtom(b"as-array"), function_]) {
    return Some(AsArrayTerm(model_term(function_)))
  }
  if value
    is ModelList(
      [
        ModelList(
          [
            ModelAtom(b"as"),
            ModelAtom(b"const"),
            ModelList([ModelAtom(b"Array"), index_sort, element_sort]),
          ]
        ),
        default,
      ]
    ) &&
    model_sort(index_sort) is Some(index_sort) &&
    model_sort(element_sort) is Some(element_sort) {
    return Some(
      ArrayTerm(index_sort, element_sort, {
        indices: [],
        others: model_term(default),
      }),
    )
  }
  if value is ModelList([ModelAtom(b"store"), base, index, element]) &&
    model_array(base) is Some(ArrayTerm(index_sort, element_sort, elements)) {
    return Some(
      ArrayTerm(index_sort, element_sort, {
        indices: [(model_term(index), model_term(element))] + elements.indices,
        others: elements.others,
      }),
    )
  }
  None
}

///|
fn model_term(value : ModelSexp) -> SmtModelTerm {
  if model_constant(value) is Some(constant) {
    return ConstantTerm(constant)
  }
  // These three array forms also satisfy the generic indexed/application
  // grammar, so they must be recognized before qualified identifiers.
  if model_array(value) is Some(array) {
    return array
  }
  if model_qualified_identifier(value) is Some(identifier) {
    return VariableTerm(identifier)
  }
  if value is ModelList([ModelAtom(b"ite"), condition, consequent, alternative]) {
    return ConditionalTerm(
      model_term(condition),
      model_term(consequent),
      model_term(alternative),
    )
  }
  if value is ModelList(values) &&
    !values.is_empty() &&
    model_qualified_identifier(values[0]) is Some(identifier) {
    return ApplicationTerm(
      identifier,
      [
        for argument in values[1:] => model_term(argument)
      ],
    )
  }
  UnparsedTerm(model_sexp_bytes(value))
}

///|
fn model_function_argument(
  value : ModelSexp,
) -> (SmtModelSymbol, SmtModelSort)? {
  guard value is ModelList([name, sort]) &&
    model_symbol(name) is Some(name) &&
    model_sort(sort) is Some(sort) else {
    return None
  }
  Some((name, sort))
}

///|
fn model_function_definition(value : ModelSexp) -> SmtModelFunctionDefinition? {
  guard value
    is ModelList(
      [
        ModelAtom(b"define-fun"),
        ModelAtom(raw_name),
        ModelList(raw_arguments),
        raw_result,
        raw_body,
      ]
    ) &&
    model_sort(raw_result) is Some(result) else {
    return None
  }
  let name = model_unquote_symbol(raw_name).unwrap_or(raw_name)
  let arguments : Array[(SmtModelSymbol, SmtModelSort)] = []
  for argument in raw_arguments {
    match model_function_argument(argument) {
      Some(argument) => arguments.push(argument)
      None => return None
    }
  }
  Some({ name, arguments, result, body: model_term(raw_body) })
}

///|
fn model_declaration_list(
  sexps : ArrayView[ModelSexp],
) -> Array[ModelSexp] raise ModelParseError {
  let mut selected : Array[ModelSexp]? = None
  let mut selected_index = -1
  for index, value in sexps {
    let candidate = match value {
      ModelList([ModelAtom(b"model"), .. rest]) => Some(rest.to_owned())
      ModelList(values) if values.any(model_contains_definition) => Some(values)
      _ => None
    }
    if candidate is Some(candidate) {
      if selected is Some(_) {
        fail_model_parse(
          MultipleModels,
          0,
          "multiple SMT-LIB models are not separated by the driver",
        )
      }
      selected = Some(candidate)
      selected_index = index
    }
  }
  guard selected is Some(selected) else { return [] }
  for index = selected_index + 1; index < sexps.length(); index = index + 1 {
    if model_contains_definition(sexps[index]) {
      fail_model_parse(
        MultipleModels,
        0,
        "another SMT-LIB model follows the selected model",
      )
    }
  }
  selected
}

///|
/// Parses the raw function definitions returned by an SMT-LIB 2 model. The
/// parser accepts both `(model ...)` and Z3's outer-list form, preserves exact
/// constant spelling, and keeps solver-specific terms as `UnparsedTerm`.
pub fn parse_smtv2_model(input : BytesView) -> SmtModel raise ModelParseError {
  let sexps = ModelSexpReader::new(input).all()
  let declarations = model_declaration_list(sexps)
  let definitions : Array[SmtModelFunctionDefinition] = []
  for declaration in declarations {
    if model_function_definition(declaration) is Some(definition) {
      definitions.push(definition)
    }
  }
  { definitions, }
}

///|
fn model_query_occurrence(
  query : @smtv2.SmtQuery,
  name : BytesView,
) -> @smtv2.PrintedIdentifier? {
  let bytes = query.bytes()
  for occurrence in query.identifiers() {
    if occurrence.start >= 0 &&
      occurrence.end >= occurrence.start &&
      occurrence.end <= bytes.length() {
      let printed = bytes[occurrence.start:occurrence.end]
      let normalized = model_unquote_symbol(printed).unwrap_or(
        printed.to_owned(),
      )
      if model_bytes_equal(normalized, name) {
        return Some(occurrence)
      }
    }
  }
  None
}

///|
/// Associates parsed model definitions with the semantic identities recorded
/// by the SMT printer. Solver-introduced definitions remain present with no
/// identity, matching Why3's distinction between queried and prover symbols.
pub fn parse_smtv2_model_for_query(
  query : @smtv2.SmtQuery,
  input : BytesView,
) -> Array[SmtModelValue] raise ModelParseError {
  let model = parse_smtv2_model(input)
  model.definitions.map(definition => {
    match model_query_occurrence(query, definition.name) {
      Some(occurrence) =>
        {
          definition,
          semantic_id: Some(occurrence.semantic_id),
          origin: Some(occurrence.origin),
        }
      None => { definition, semantic_id: None, origin: None }
    }
  })
}

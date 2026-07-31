// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn[A] KnownMap::parse_record_fields(
  self : KnownMap,
  fields : ArrayView[(LSymbol, A)],
  span : @identity.SourceSpan?,
) -> (DataConstructor, Array[LSymbol], Map[LSymbol, A]) raise TypeError {
  if fields.is_empty() {
    fail_type(EmptyRecord, span, "record field list is empty")
  }
  let first_field = fields[0].0
  guard first_field.argument_types
    is [{ node: ApplicationNode(type_symbol, _), .. }] else {
    fail_type(BadRecordField, span, "record field has an invalid signature")
  }
  let constructors = self.find_constructors(type_symbol, span)
  if constructors.length() != 1 {
    fail_type(
      BadRecordType,
      span,
      "record type must have exactly one constructor",
    )
  }
  let data_constructor = constructors[0]
  let projections : Array[LSymbol] = []
  for projection in data_constructor.projections {
    match projection {
      Some(projection) => projections.push(projection)
      None =>
        fail_type(
          BadRecordType,
          span,
          "record constructor contains an unnamed field",
        )
    }
  }
  let values : Map[LSymbol, A] = Map([])
  for entry in fields {
    let (field, value) = entry
    if !projections.contains(field) {
      fail_type(
        BadRecordField,
        span,
        "field does not belong to the record type",
      )
    }
    if values.contains(field) {
      fail_type(
        DuplicateRecordField,
        span,
        "record field is assigned more than once",
      )
    }
    values[field] = value
  }
  (data_constructor, projections, values)
}

///|
/// Resolves and validates the unique constructor and declaration-order field
/// layout shared by record terms, updates, and patterns.
pub fn KnownMap::record_layout(
  self : KnownMap,
  fields : ArrayView[LSymbol],
  span : @identity.SourceSpan?,
) -> (DataConstructor, Array[LSymbol]) raise TypeError {
  let entries = fields.map(field => (field, ()))
  let (data_constructor, projections, _) = self.parse_record_fields(
    entries, span,
  )
  (data_constructor, projections)
}

///|
pub fn KnownMap::make_record(
  self : KnownMap,
  fields : ArrayView[(LSymbol, Term)],
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  let (data_constructor, projections, values) = self.parse_record_fields(
    fields, span,
  )
  let arguments : Array[Term] = []
  for projection in projections {
    match values.get(projection) {
      Some(value) => arguments.push(value)
      None =>
        fail_type(RecordFieldMissing, span, "record construction omits a field")
    }
  }
  Term::elaborated_apply(
    data_constructor.symbol,
    arguments,
    Some(result_type),
    span,
  )
}

///|
pub fn KnownMap::make_record_update(
  self : KnownMap,
  record : Term,
  fields : ArrayView[(LSymbol, Term)],
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  let (data_constructor, projections, values) = self.parse_record_fields(
    fields, span,
  )
  let arguments : Array[Term] = []
  for projection in projections {
    match values.get(projection) {
      Some(value) => arguments.push(value)
      None => arguments.push(Term::apply_function(projection, [record], span))
    }
  }
  Term::elaborated_apply(
    data_constructor.symbol,
    arguments,
    Some(result_type),
    span,
  )
}

///|
pub fn KnownMap::make_record_pattern(
  self : KnownMap,
  fields : ArrayView[(LSymbol, Pattern)],
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Pattern raise TypeError {
  let (data_constructor, projections, values) = self.parse_record_fields(
    fields, span,
  )
  let argument_types = constructor_argument_types(
    data_constructor, result_type, span,
  )
  let arguments : Array[Pattern] = []
  for index, projection in projections {
    match values.get(projection) {
      Some(pattern) => arguments.push(pattern)
      None => arguments.push(Pattern::wild(argument_types[index]))
    }
  }
  Pattern::app(data_constructor.symbol, arguments, result_type, span)
}

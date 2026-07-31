// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn type_contains_any_symbol(ty : Ty, symbols : Map[TypeSymbol, Unit]) -> Bool {
  match ty.node {
    VariableNode(_) => false
    ApplicationNode(symbol, arguments) =>
      symbols.contains(symbol) ||
      arguments.any(argument => type_contains_any_symbol(argument, symbols))
  }
}

///|
fn type_is_founded(
  known : KnownMap,
  visiting : Map[TypeSymbol, Unit],
  uninhabited_parameters : Map[TyVarSymbol, Unit],
  ty : Ty,
) -> Bool {
  match ty.node {
    VariableNode(variable) => !uninhabited_parameters.contains(variable)
    ApplicationNode(symbol, arguments) => {
      let bad_parameters : Map[TyVarSymbol, Unit] = Map([])
      let parameters = symbol.view().parameters
      for index, argument in arguments {
        if !type_is_founded(known, visiting, uninhabited_parameters, argument) {
          bad_parameters[parameters[index]] = ()
        }
      }
      type_symbol_is_founded(known, visiting, bad_parameters, symbol)
    }
  }
}

///|
fn type_symbol_is_founded(
  known : KnownMap,
  visiting : Map[TypeSymbol, Unit],
  uninhabited_parameters : Map[TyVarSymbol, Unit],
  symbol : TypeSymbol,
) -> Bool {
  if visiting.contains(symbol) {
    return false
  }
  let constructors = known.find_constructors(symbol, None) catch {
    _ => return false
  }
  if constructors.is_empty() {
    return uninhabited_parameters.is_empty()
  }
  let nested = visiting.copy()
  nested[symbol] = ()
  constructors.any(data_constructor => {
    data_constructor.view().symbol.view().argument_types.all(argument => {
      type_is_founded(known, nested, uninhabited_parameters, argument)
    })
  })
}

///|
fn validate_data_foundness(
  known : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  guard declaration.node is DataDeclarationNode(declarations) else { return }
  for data in declarations {
    if !type_symbol_is_founded(known, Map([]), Map([]), data.type_symbol) {
      fail_type(
        NonFoundedTypeDeclaration,
        span,
        "algebraic type has no finite inhabitant",
      )
    }
  }
}

///|
fn function_type_symbol(symbol : TypeSymbol) -> Bool {
  let view = symbol.view()
  view.name == b"infix ->" && view.parameters.length() == 2
}

///|
fn collect_negative_type_variables(
  known : KnownMap,
  visiting : Map[TypeSymbol, Unit],
  ty : Ty,
  negative : Map[TyVarSymbol, Unit],
) -> Unit {
  match ty.node {
    VariableNode(_) => ()
    ApplicationNode(symbol, arguments) => {
      let positions = type_symbol_positive_parameters(known, visiting, symbol)
      for index, argument in arguments {
        if positions[index] {
          collect_negative_type_variables(known, visiting, argument, negative)
        } else {
          for variable in argument.free_variables() {
            negative[variable] = ()
          }
        }
      }
    }
  }
}

///|
fn type_symbol_positive_parameters(
  known : KnownMap,
  visiting : Map[TypeSymbol, Unit],
  symbol : TypeSymbol,
) -> Array[Bool] {
  if function_type_symbol(symbol) {
    return [false, true]
  }
  let parameters = symbol.view().parameters
  if visiting.contains(symbol) {
    return parameters.map(_ => true)
  }
  let constructors = known.find_constructors(symbol, None) catch {
    _ => return parameters.map(_ => false)
  }
  if constructors.is_empty() {
    return parameters.map(_ => false)
  }
  let nested = visiting.copy()
  nested[symbol] = ()
  let negative : Map[TyVarSymbol, Unit] = Map([])
  for data_constructor in constructors {
    for argument in data_constructor.view().symbol.view().argument_types {
      collect_negative_type_variables(known, nested, argument, negative)
    }
  }
  parameters.map(parameter => !negative.contains(parameter))
}

///|
fn validate_positive_type(
  known : KnownMap,
  data_symbols : Map[TypeSymbol, Unit],
  ty : Ty,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  match ty.node {
    VariableNode(_) => ()
    ApplicationNode(symbol, arguments) => {
      let positions = type_symbol_positive_parameters(known, Map([]), symbol)
      for index, argument in arguments {
        if positions[index] {
          validate_positive_type(known, data_symbols, argument, span)
        } else if type_contains_any_symbol(argument, data_symbols) {
          fail_type(
            NonPositiveTypeDeclaration,
            span,
            "recursive algebraic type occurs in a non-positive position",
          )
        }
      }
    }
  }
}

///|
fn validate_data_positivity(
  known : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  guard declaration.node is DataDeclarationNode(declarations) else { return }
  let data_symbols : Map[TypeSymbol, Unit] = Map([])
  for data in declarations {
    data_symbols[data.type_symbol] = ()
  }
  for data in declarations {
    for data_constructor in data.constructors {
      for argument in data_constructor.symbol.argument_types {
        validate_positive_type(known, data_symbols, argument, span)
      }
    }
  }
}

///|
fn validate_pattern_constructor(
  known : KnownMap,
  pattern : Pattern,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  match pattern.node {
    WildPattern | VariablePattern(_) => ()
    ApplicationPattern(symbol, arguments) => {
      guard pattern.ty.node is ApplicationNode(type_symbol, _) else {
        fail_type(
          InvalidDeclaration,
          span,
          "constructor pattern has a non-algebraic result type",
        )
      }
      let constructors = known.find_constructors(type_symbol, span)
      if !constructors.any(data_constructor => data_constructor.symbol == symbol) {
        fail_type(
          InvalidDeclaration,
          span,
          "pattern constructor does not belong to its result type",
        )
      }
      for argument in arguments {
        validate_pattern_constructor(known, argument, span)
      }
    }
    OrPattern(left, right) => {
      validate_pattern_constructor(known, left, span)
      validate_pattern_constructor(known, right, span)
    }
    AsPattern(inner, _) => validate_pattern_constructor(known, inner, span)
  }
}

///|
fn constructor_argument_types(
  data_constructor : DataConstructor,
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Array[Ty] raise TypeError {
  let symbol = data_constructor.symbol
  guard symbol.result_type is Some(formal_result) else {
    abort("validated constructor lost its result type")
  }
  let substitution = type_match(formal_result, result_type, span)
  [
    for argument in symbol.argument_types => substitution.apply(argument, span)
  ]
}

///|
fn wildcard_patterns(types : ArrayView[Ty]) -> Array[Pattern] {
  types.map(Pattern::wild)
}

///|
fn specialize_pattern(
  pattern : Pattern,
  constructor_symbol : LSymbol,
  constructor_arguments : ArrayView[Ty],
) -> Array[Array[Pattern]] {
  match pattern.node {
    WildPattern | VariablePattern(_) =>
      [wildcard_patterns(constructor_arguments)]
    ApplicationPattern(symbol, arguments) =>
      if symbol == constructor_symbol {
        [arguments.copy()]
      } else {
        []
      }
    OrPattern(left, right) => {
      let result = specialize_pattern(
        left, constructor_symbol, constructor_arguments,
      )
      for
        row in specialize_pattern(
          right, constructor_symbol, constructor_arguments,
        ) {
        result.push(row)
      }
      result
    }
    AsPattern(inner, _) =>
      specialize_pattern(inner, constructor_symbol, constructor_arguments)
  }
}

///|
fn wildcard_pattern(pattern : Pattern) -> Bool {
  match pattern.node {
    WildPattern | VariablePattern(_) => true
    AsPattern(inner, _) => wildcard_pattern(inner)
    OrPattern(left, right) => wildcard_pattern(left) || wildcard_pattern(right)
    ApplicationPattern(_, _) => false
  }
}

///|
fn specialize_row(
  row : ArrayView[Pattern],
  constructor_symbol : LSymbol,
  constructor_arguments : ArrayView[Ty],
) -> Array[Array[Pattern]] {
  let result : Array[Array[Pattern]] = []
  for
    head in specialize_pattern(
      row[0],
      constructor_symbol,
      constructor_arguments,
    ) {
    let specialized = head.copy()
    for index = 1; index < row.length(); index = index + 1 {
      specialized.push(row[index])
    }
    result.push(specialized)
  }
  result
}

///|
fn pattern_matrix_is_exhaustive(
  known : KnownMap,
  types : ArrayView[Ty],
  rows : ArrayView[Array[Pattern]],
  span : @identity.SourceSpan?,
) -> Bool raise TypeError {
  if rows.is_empty() {
    return false
  }
  if types.is_empty() {
    return true
  }
  let wildcard_tails : Array[Array[Pattern]] = []
  for row in rows {
    if wildcard_pattern(row[0]) {
      wildcard_tails.push(row[1:].to_owned())
    }
  }
  if !wildcard_tails.is_empty() &&
    pattern_matrix_is_exhaustive(known, types[1:], wildcard_tails, span) {
    return true
  }
  let constructors : Array[DataConstructor] = match types[0].node {
    VariableNode(_) => []
    ApplicationNode(symbol, _) => known.find_constructors(symbol, span)
  }
  if constructors.is_empty() {
    return pattern_matrix_is_exhaustive(known, types[1:], wildcard_tails, span)
  }
  for data_constructor in constructors {
    let argument_types = constructor_argument_types(
      data_constructor,
      types[0],
      span,
    )
    let specialized : Array[Array[Pattern]] = []
    for row in rows {
      for
        specialized_row in specialize_row(
          row,
          data_constructor.symbol,
          argument_types,
        ) {
        specialized.push(specialized_row)
      }
    }
    let specialized_types = argument_types.copy()
    for index = 1; index < types.length(); index = index + 1 {
      specialized_types.push(types[index])
    }
    if !pattern_matrix_is_exhaustive(
        known, specialized_types, specialized, span,
      ) {
      return false
    }
  }
  true
}

///|
/// Reports whether every value described by `types` is covered by one of the
/// pattern rows. Program elaboration uses the same constructor-aware check as
/// logical declaration validation before adding Why3's implicit `absurd`
/// fallback branch.
pub fn KnownMap::patterns_are_exhaustive(
  self : KnownMap,
  types : ArrayView[Ty],
  rows : ArrayView[Array[Pattern]],
  span : @identity.SourceSpan?,
) -> Bool raise TypeError {
  pattern_matrix_is_exhaustive(self, types, rows, span)
}

///|
fn validate_term_patterns(
  known : KnownMap,
  term : Term,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  let recurse = fn(child : Term) -> Unit raise TypeError {
    validate_term_patterns(known, child, span)
  }
  match term.node {
    VariableTerm(_) | ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(_, _, arguments) =>
      for argument in arguments {
        recurse(argument)
      }
    IfTerm(condition, then_branch, else_branch) => {
      recurse(condition)
      recurse(then_branch)
      recurse(else_branch)
    }
    LetTerm(_, value, body) => {
      recurse(value)
      recurse(body)
    }
    CaseTerm(scrutinee, branches) => {
      recurse(scrutinee)
      let rows : Array[Array[Pattern]] = []
      for branch in branches {
        validate_pattern_constructor(known, branch.pattern, span)
        recurse(branch.body)
        rows.push([branch.pattern])
      }
      guard scrutinee.result_type is Some(scrutinee_type) else {
        abort("validated case scrutinee lost its type")
      }
      if !pattern_matrix_is_exhaustive(known, [scrutinee_type], rows, span) {
        fail_type(
          NonExhaustivePattern,
          span,
          "case expression has a non-exhaustive pattern set",
        )
      }
    }
    EpsilonTerm(_, body) => recurse(body)
    QuantifiedTerm(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          recurse(trigger)
        }
      }
      recurse(body)
    }
    BinaryTerm(_, left, right) => {
      recurse(left)
      recurse(right)
    }
    NotTerm(inner) => recurse(inner)
  }
}

///|
fn validate_declaration_patterns(
  known : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  match declaration.node {
    TypeDeclaration(_) | DataDeclarationNode(_) | ParameterDeclaration(_) => ()
    LogicDeclaration(definitions) =>
      for definition in definitions {
        validate_term_patterns(known, definition.body, span)
      }
    InductiveDeclarationNode(_, declarations) =>
      for inductive in declarations {
        for case_ in inductive.cases {
          validate_term_patterns(known, case_.formula, span)
        }
      }
    PropositionDeclaration(_, _, formula) =>
      validate_term_patterns(known, formula, span)
  }
}

///|
fn validate_known_declaration(
  known : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  validate_data_positivity(known, declaration, span)
  validate_data_foundness(known, declaration, span)
  validate_declaration_patterns(known, declaration, span)
}

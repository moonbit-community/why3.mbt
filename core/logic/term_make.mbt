// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn require_value_type(
  term : Term,
  span : @identity.SourceSpan?,
) -> Ty raise TypeError {
  match term.result_type {
    Some(ty) => ty
    None =>
      fail_type(ValueExpected, span, "expected a value term, found a formula")
  }
}

///|
fn require_formula(
  term : Term,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  if term.result_type is Some(_) {
    fail_type(FormulaExpected, span, "expected a formula, found a value term")
  }
}

///|
fn require_same_term_kind(
  left : Term,
  right : Term,
  span : @identity.SourceSpan?,
) -> Ty? raise TypeError {
  require_same_result_type(left.result_type, right.result_type, span)
}

///|
fn require_same_result_type(
  left : Ty?,
  right : Ty?,
  span : @identity.SourceSpan?,
) -> Ty? raise TypeError {
  match (left, right) {
    (None, None) => None
    (Some(left_type), Some(right_type)) =>
      if left_type == right_type {
        Some(left_type)
      } else {
        fail_type(TypeMismatch, span, "branches have different value types")
      }
    (None, Some(_)) | (Some(_), None) =>
      fail_type(
        TypeMismatch,
        span,
        "formula and value branches require an explicit elaborator coercion",
      )
  }
}

///|
pub fn Term::variable(variable : VSymbol) -> Term {
  make_term(VariableTerm(variable), Some(variable.ty))
}

///|
pub fn Term::constant(
  constant : Constant,
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  validate_constant_type(constant, result_type, span)
  make_term(ConstantTerm(constant), Some(result_type))
}

///|
fn apply_logic_symbol(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if arguments.length() != symbol.argument_types.length() {
    fail_type(
      ArityMismatch,
      span,
      "logic symbol expected \{symbol.argument_types.length()} arguments but received \{arguments.length()}",
    )
  }
  let copied = arguments.to_owned()
  let mut substitution = TySubstitution::new()
  for index, formal in symbol.argument_types {
    let actual = require_value_type(copied[index], span)
    substitution = substitution.match_type(formal, actual, span)
  }
  let instantiation : Array[(TyVarSymbol, Ty)] = []
  for parameter in symbol.type_parameters {
    if substitution.get(parameter) is Some(actual) {
      instantiation.push((parameter, actual))
    }
  }
  let result_type = match symbol.result_type {
    None => None
    Some(ty) => Some(substitution.apply(ty, span))
  }
  make_term(ApplicationTerm(symbol, instantiation, copied), result_type)
}

///|
fn apply_logic_symbol_with_result(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  result_type : Ty?,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if arguments.length() != symbol.argument_types.length() {
    fail_type(
      ArityMismatch,
      span,
      "logic symbol application has the wrong arity",
    )
  }
  let copied = arguments.to_owned()
  let mut substitution = TySubstitution::new()
  for index, formal in symbol.argument_types {
    let actual = require_value_type(copied[index], span)
    substitution = substitution.match_type(formal, actual, span)
  }
  match (symbol.result_type, result_type) {
    (None, None) => ()
    (Some(formal), Some(actual)) =>
      substitution = substitution.match_type(formal, actual, span)
    (None, Some(_)) | (Some(_), None) =>
      fail_type(
        TypeMismatch,
        span,
        "application result disagrees with its symbol kind",
      )
  }
  let instantiation : Array[(TyVarSymbol, Ty)] = []
  for parameter in symbol.type_parameters {
    if substitution.get(parameter) is Some(actual) {
      instantiation.push((parameter, actual))
    }
  }
  make_term(ApplicationTerm(symbol, instantiation, copied), result_type)
}

///|
/// Elaborator entry point whose delayed typing has already fixed the result
/// instantiation, including nullary polymorphic functions.
pub fn Term::elaborated_apply(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  result_type : Ty?,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  apply_logic_symbol_with_result(symbol, arguments, result_type, span)
}

///|
/// Trusted snapshot application constructor. Unlike ordinary elaboration,
/// the frozen representation carries the expected result type explicitly;
/// matching it is necessary for nullary polymorphic symbols whose type
/// arguments cannot be recovered from value arguments alone.
pub fn Term::trusted_snapshot_apply(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  result_type : Ty?,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if !(symbol.origin.kind().view() is SnapshotKind) {
    fail_type(
      SnapshotOriginRequired,
      span,
      "trusted term application requires a snapshot logic symbol",
    )
  }
  apply_logic_symbol_with_result(symbol, arguments, result_type, span)
}

///|
/// Applies a logic symbol and infers whether the result is a value or formula
/// from the immutable symbol signature.
pub fn Term::apply(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  apply_logic_symbol(symbol, arguments, span)
}

///|
pub fn Term::apply_function(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if symbol.result_type is None {
    fail_type(FunctionExpected, span, "predicate used as a function")
  }
  apply_logic_symbol(symbol, arguments, span)
}

///|
pub fn Term::apply_predicate(
  symbol : LSymbol,
  arguments : ArrayView[Term],
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if symbol.result_type is Some(_) {
    fail_type(PredicateExpected, span, "function used as a predicate")
  }
  apply_logic_symbol(symbol, arguments, span)
}

///|
pub fn Term::if_then_else(
  condition : Term,
  then_branch : Term,
  else_branch : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  require_formula(condition, span)
  let result_type = require_same_term_kind(then_branch, else_branch, span)
  make_term(IfTerm(condition, then_branch, else_branch), result_type)
}

///|
pub fn Term::let_in(
  variable : VSymbol,
  value : Term,
  body : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if require_value_type(value, span) != variable.ty {
    fail_type(TypeMismatch, span, "let-bound value has the wrong type")
  }
  make_term(LetTerm(variable, value, body), body.result_type)
}

///|
fn validate_binders(
  binders : ArrayView[VSymbol],
  span : @identity.SourceSpan?,
) -> Array[VSymbol] raise TypeError {
  let copied = binders.to_owned()
  let seen : Map[VSymbol, Unit] = Map([])
  for binder in copied {
    if seen.contains(binder) {
      fail_type(DuplicateBinder, span, "quantifier repeats a binder")
    }
    seen[binder] = ()
  }
  copied
}

///|
fn validate_triggers(
  binders : ArrayView[VSymbol],
  triggers : ArrayView[Array[Term]],
  body : Term,
  span : @identity.SourceSpan?,
) -> Array[Array[Term]] raise TypeError {
  let allowed : Map[VSymbol, Unit] = Map([])
  for variable in body.free_variables() {
    allowed[variable] = ()
  }
  for binder in binders {
    allowed[binder] = ()
  }
  let copied : Array[Array[Term]] = []
  for group in triggers {
    if group.is_empty() {
      fail_type(InvalidTrigger, span, "trigger groups cannot be empty")
    }
    let group_copy = group.copy()
    for trigger_term in group_copy {
      for variable in trigger_term.free_variables() {
        if !allowed.contains(variable) {
          fail_type(
            InvalidTrigger,
            span,
            "trigger references a variable outside the quantified body",
          )
        }
      }
    }
    copied.push(group_copy)
  }
  copied
}

///|
pub fn Term::quantify(
  quantifier : Quantifier,
  binders : ArrayView[VSymbol],
  triggers : ArrayView[Array[Term]],
  body : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  require_formula(body, span)
  let binders = validate_binders(binders, span)
  if binders.is_empty() {
    return body
  }
  let triggers = validate_triggers(binders, triggers, body, span)
  make_term(QuantifiedTerm(quantifier, binders, triggers, body), None)
}

///|
pub fn Term::binary(
  operator : BinaryLogicOp,
  left : Term,
  right : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  require_formula(left, span)
  require_formula(right, span)
  make_term(BinaryTerm(operator, left, right), None)
}

///|
pub fn Term::not(
  term : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  require_formula(term, span)
  make_term(NotTerm(term), None)
}

///|
pub fn Term::true_formula() -> Term {
  make_term(TrueTerm, None)
}

///|
pub fn Term::false_formula() -> Term {
  make_term(FalseTerm, None)
}

///|
pub fn Term::trusted_case(
  scrutinee : Term,
  branches : ArrayView[(Pattern, Term)],
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  let scrutinee_type = require_value_type(scrutinee, span)
  if branches.is_empty() {
    fail_type(EmptyDeclaration, span, "case expression has no branches")
  }
  let result : Array[TermBranch] = []
  let mut result_type : Ty? = None
  let mut saw_first = false
  for entry in branches {
    let (pattern, body) = entry
    if pattern.ty != scrutinee_type {
      fail_type(TypeMismatch, span, "case pattern has the wrong type")
    }
    if !saw_first {
      result_type = body.result_type
      saw_first = true
    } else {
      ignore(require_same_result_type(result_type, body.result_type, span))
    }
    result.push({ pattern, body })
  }
  make_term(CaseTerm(scrutinee, result), result_type)
}

///|
pub fn Term::trusted_epsilon(
  variable : VSymbol,
  body : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  require_formula(body, span)
  make_term(EpsilonTerm(variable, body), Some(variable.ty))
}

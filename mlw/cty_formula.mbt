// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).

///|
fn formula_split_stops(term : @logic.Term) -> Bool {
  term.attributes().any(attribute => attribute == b"stop_split")
}

///|
fn formula_tuple_name(arity : Int, constructor_name : Bool) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(if constructor_name { b"Tuple" } else { b"tuple" })
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn formula_program_variable(
  context : @identity.CompilationContext,
  program_space : ProgramNamespace,
  source : @logic.VSymbol,
  span : @identity.SourceSpan?,
) -> PVariable raise {
  let view = source.view()
  PVariable::trusted_new(
    context,
    @theory.SemanticName::new(
      view.name,
      view.origin.attributes(),
      view.origin.source_span(),
    ),
    Ity::from_ty(program_space, view.ty, span),
    false,
    span,
  )
}

///|
fn formula_substitution(
  context : @identity.CompilationContext,
  sources : ArrayView[@logic.VSymbol],
  targets : ArrayView[PVariable],
  term : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let mut substitution = @logic.TermSubstitution::new()
  for index = 0; index < sources.length(); index = index + 1 {
    substitution = substitution.bind(
      sources[index],
      @logic.Term::variable(targets[index].view().pure_symbol),
      span,
    )
  }
  substitution.apply(context, term, span)
}

///|
fn formula_type_variables_are_bound(
  arguments : ArrayView[PVariable],
  result : Ity,
  preconditions : ArrayView[@logic.Term],
  postcondition : @logic.Term,
) -> Bool {
  let allowed : Map[@logic.TyVarSymbol, Unit] = Map([])
  for variable in result.free_type_variables() {
    allowed[variable] = ()
  }
  for argument in arguments {
    for variable in argument.view().ity.free_type_variables() {
      allowed[variable] = ()
    }
  }
  for precondition in preconditions {
    for variable in precondition.free_type_variables() {
      if !allowed.contains(variable) {
        return false
      }
    }
  }
  for variable in postcondition.free_type_variables() {
    if !allowed.contains(variable) {
      return false
    }
  }
  true
}

///|
/// Direct counterpart of Why3's `Expr.cty_from_formula`. A leading universal
/// prefix becomes routine arguments, implications become preconditions, and a
/// leading existential/conjunction prefix becomes the result/postcondition.
/// `None` is the same `UnboundTypeVar` escape used by parser typing.
pub fn Cty::from_formula(
  context : @identity.CompilationContext,
  pure_space : @theory.Namespace,
  program_space : ProgramNamespace,
  source : @logic.Term,
  span : @identity.SourceSpan?,
) -> Cty? raise {
  let universal : Array[@logic.VSymbol] = []
  let source_preconditions : Array[@logic.Term] = []
  let mut body = source
  let mut decomposing = true
  while decomposing {
    if formula_split_stops(body) {
      break
    }
    match body.view() {
      Tquant(ForallQuantifier, binders, _, nested) => {
        for binder in binders {
          universal.push(binder)
        }
        body = nested
      }
      Tbinop(Implies, premise, consequence) => {
        source_preconditions.push(premise)
        body = consequence
      }
      _ => decomposing = false
    }
  }

  let arguments : Array[PVariable] = []
  for variable in universal {
    arguments.push(
      formula_program_variable(context, program_space, variable, span),
    )
  }
  let preconditions = source_preconditions.map(precondition => {
    formula_substitution(context, universal, arguments, precondition, span)
  })
  body = formula_substitution(context, universal, arguments, body, span)

  let existential : Array[@logic.VSymbol] = []
  let conjuncts : Array[@logic.Term] = []
  decomposing = true
  while decomposing {
    if formula_split_stops(body) {
      break
    }
    match body.view() {
      Tquant(ExistsQuantifier, binders, _, nested) => {
        for binder in binders {
          existential.push(binder)
        }
        body = nested
      }
      Tbinop(And, left, right) => {
        conjuncts.push(left)
        body = right
      }
      _ => decomposing = false
    }
  }
  let mut formula = body
  let mut index = conjuncts.length()
  while index > 0 {
    index = index - 1
    formula = @logic.Term::binary(And, conjuncts[index], formula, span)
  }

  let (result_variable, result) = match existential.length() {
    0 => {
      let unit = Ity::instantiate(
        program_space.find_type([b"unit"], span),
        [],
        [],
        span,
      )
      (
        @logic.VSymbol::new(
          context,
          b"result",
          @identity.Origin::user(b"result", None, []),
          unit.to_ty(span),
          span,
        ),
        unit,
      )
    }
    1 => {
      let variable = existential[0]
      (variable, Ity::from_ty(program_space, variable.ty(), span))
    }
    arity => {
      let tuple_type = pure_space.find_type(
        [formula_tuple_name(arity, false)],
        span,
      )
      let result_type = @logic.Ty::app(
        tuple_type,
        existential.map(variable => variable.ty()),
        span,
      )
      let result_variable = @logic.VSymbol::new(
        context,
        b"result",
        @identity.Origin::user(b"result", None, []),
        result_type,
        span,
      )
      let pattern = @logic.Pattern::app(
        pure_space.find_logic([formula_tuple_name(arity, true)], span),
        existential.map(@logic.Pattern::variable),
        result_type,
        span,
      )
      formula = @logic.Term::case(
        @logic.Term::variable(result_variable),
        [(pattern, formula)],
        span,
      )
      (result_variable, Ity::from_ty(program_space, result_type, span))
    }
  }
  if !formula_type_variables_are_bound(
      arguments, result, preconditions, formula,
    ) {
    return None
  }
  let postcondition = Postcondition::trusted_new(result_variable, formula, span)
  Some(
    Cty::new(
      arguments,
      preconditions,
      [postcondition],
      [],
      [],
      Effect::pure(false),
      result,
      span,
    ),
  )
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn record_tuple_arity(arities : Map[Int, Unit], arity : Int) -> Unit {
  arities[arity] = ()
}

///|
fn collect_tuple_pty(arities : Map[Int, Unit], source : @parser.Pty) -> Unit {
  match source {
    PTtyvar(_) => ()
    PTtyapp(_, arguments) =>
      for argument in arguments {
        collect_tuple_pty(arities, argument)
      }
    PTref(arguments) => {
      record_tuple_arity(arities, -1)
      for argument in arguments {
        collect_tuple_pty(arities, argument)
      }
    }
    PTtuple(arguments) => {
      record_tuple_arity(arities, arguments.length())
      for argument in arguments {
        collect_tuple_pty(arities, argument)
      }
    }
    PTarrow(parameter, result) => {
      record_tuple_arity(arities, -2)
      collect_tuple_pty(arities, parameter)
      collect_tuple_pty(arities, result)
    }
    PTscope(_, nested) | PTparen(nested) | PTpure(nested) =>
      collect_tuple_pty(arities, nested)
  }
}

///|
fn collect_tuple_pattern(
  arities : Map[Int, Unit],
  pattern : @parser.Pattern,
) -> Unit {
  match pattern.desc {
    Pwild | Pvar(_) => ()
    Papp(_, arguments) =>
      for argument in arguments {
        collect_tuple_pattern(arities, argument)
      }
    Prec(fields) =>
      for field in fields {
        collect_tuple_pattern(arities, field.1)
      }
    Ptuple(arguments) => {
      record_tuple_arity(arities, arguments.length())
      for argument in arguments {
        collect_tuple_pattern(arities, argument)
      }
    }
    Pas(inner, _, _) | Pscope(_, inner) | Pparen(inner) | Pghost(inner) =>
      collect_tuple_pattern(arities, inner)
    Por(left, right) => {
      collect_tuple_pattern(arities, left)
      collect_tuple_pattern(arities, right)
    }
    Pcast(inner, annotation) => {
      collect_tuple_pattern(arities, inner)
      collect_tuple_pty(arities, annotation)
    }
  }
}

///|
fn collect_tuple_binders(
  arities : Map[Int, Unit],
  binders : ArrayView[@parser.Binder],
) -> Unit {
  for binder in binders {
    if binder.binder_type is Some(annotation) {
      collect_tuple_pty(arities, annotation)
    }
  }
}

///|
fn collect_tuple_term(arities : Map[Int, Unit], term : @parser.Term) -> Unit {
  match term.desc {
    Ttrue | Tfalse | Tconst(_) | Tident(_) => ()
    Tasref(_) => record_tuple_arity(arities, -1)
    Tidapp(_, arguments) =>
      for argument in arguments {
        collect_tuple_term(arities, argument)
      }
    Tapply(function_, argument) => {
      record_tuple_arity(arities, -3)
      if !term_application_has_ident_head(term) {
        record_tuple_arity(arities, -2)
      }
      collect_tuple_term(arities, function_)
      collect_tuple_term(arities, argument)
    }
    Tinfix(function_, _, argument)
    | Tinnfix(function_, _, argument)
    | Tbinop(function_, _, argument)
    | Tbinnop(function_, _, argument) => {
      collect_tuple_term(arities, function_)
      collect_tuple_term(arities, argument)
    }
    Tnot(inner) | Tattr(_, inner) | Tscope(_, inner) | Tat(inner, _) =>
      collect_tuple_term(arities, inner)
    Tif(condition, consequent, alternative) => {
      collect_tuple_term(arities, condition)
      collect_tuple_term(arities, consequent)
      collect_tuple_term(arities, alternative)
    }
    Tquant(quantifier, binders, triggers, body) => {
      if quantifier is DTlambda {
        record_tuple_arity(arities, -2)
      }
      collect_tuple_binders(arities, binders)
      for group in triggers {
        for trigger in group {
          collect_tuple_term(arities, trigger)
        }
      }
      collect_tuple_term(arities, body)
    }
    Teps(_, annotation, body) => {
      collect_tuple_pty(arities, annotation)
      collect_tuple_term(arities, body)
    }
    Tlet(_, value, body) => {
      collect_tuple_term(arities, value)
      collect_tuple_term(arities, body)
    }
    Tcase(scrutinee, branches) => {
      collect_tuple_term(arities, scrutinee)
      for branch in branches {
        collect_tuple_pattern(arities, branch.0)
        collect_tuple_term(arities, branch.1)
      }
    }
    Tcast(inner, annotation) => {
      collect_tuple_term(arities, inner)
      collect_tuple_pty(arities, annotation)
    }
    Ttuple(arguments) => {
      record_tuple_arity(arities, arguments.length())
      for argument in arguments {
        collect_tuple_term(arities, argument)
      }
    }
    Trecord(fields) =>
      for field in fields {
        collect_tuple_term(arities, field.1)
      }
    Tupdate(source, fields) => {
      collect_tuple_term(arities, source)
      for field in fields {
        collect_tuple_term(arities, field.1)
      }
    }
  }
}

///|
fn term_application_has_ident_head(term : @parser.Term) -> Bool {
  match term.desc {
    Tapply(function_, _) => term_application_has_ident_head(function_)
    // `Tapply` is flattened only through a bare identifier. A `Tidapp` head
    // has already consumed its direct arguments, so every surrounding
    // application is lowered through HighOrd's `infix @`.
    Tident(_) => true
    _ => false
  }
}

///|
fn expr_application_has_ident_head(expression : @parser.Expr) -> Bool {
  match expression.desc {
    Eapply(function_, _) => expr_application_has_ident_head(function_)
    // As for pure terms, a pre-applied identifier is typed first and the
    // remaining arguments use the synthesized higher-order application.
    Eident(_) | Eidpur(_) | Eref => true
    _ => false
  }
}

///|
fn collect_tuple_invariant(
  arities : Map[Int, Unit],
  invariant : @parser.Invariant,
) -> Unit {
  for term in invariant.terms {
    collect_tuple_term(arities, term)
  }
}

///|
fn collect_tuple_variant(
  arities : Map[Int, Unit],
  variant : @parser.Variant,
) -> Unit {
  for item in variant.items {
    collect_tuple_term(arities, item.0)
  }
}

///|
fn collect_tuple_spec(arities : Map[Int, Unit], spec : @parser.Spec) -> Unit {
  for term in spec.preconditions {
    collect_tuple_term(arities, term)
  }
  for postcondition in spec.postconditions {
    for branch in postcondition.branches {
      collect_tuple_pattern(arities, branch.0)
      collect_tuple_term(arities, branch.1)
    }
  }
  for postcondition in spec.exceptional_postconditions {
    for branch in postcondition.branches {
      if branch.1 is Some((pattern, formula)) {
        collect_tuple_pattern(arities, pattern)
        collect_tuple_term(arities, formula)
      }
    }
  }
  for write in spec.writes {
    collect_tuple_term(arities, write)
  }
  for alias_entry in spec.aliases {
    collect_tuple_term(arities, alias_entry.0)
    collect_tuple_term(arities, alias_entry.1)
  }
  collect_tuple_variant(arities, spec.variant)
}

///|
fn cty_formula_has_stop_split(term : @parser.Term) -> Bool {
  match term.desc {
    Tattr(Text(attribute), _) => attribute == b"stop_split"
    _ => false
  }
}

///|
fn cty_formula_existential_arity(term : @parser.Term, count : Int) -> Int {
  if cty_formula_has_stop_split(term) {
    return count
  }
  match term.desc {
    Tattr(_, inner) | Tscope(_, inner) | Tcast(inner, _) =>
      cty_formula_existential_arity(inner, count)
    Tquant(DTexists, binders, _, body) =>
      cty_formula_existential_arity(body, count + binders.length())
    Tbinop(_, DTand, right) | Tbinnop(_, DTand, right) =>
      cty_formula_existential_arity(right, count)
    _ => count
  }
}

///|
fn cty_formula_result_arity(term : @parser.Term) -> Int {
  if cty_formula_has_stop_split(term) {
    return 0
  }
  match term.desc {
    Tattr(_, inner) | Tscope(_, inner) | Tcast(inner, _) =>
      cty_formula_result_arity(inner)
    Tquant(DTforall, _, _, body) => cty_formula_result_arity(body)
    Tbinop(_, DTimplies, right) | Tbinnop(_, DTimplies, right) =>
      cty_formula_result_arity(right)
    Tbinop(left, DTby, _) | Tbinnop(left, DTby, _) =>
      cty_formula_result_arity(left)
    _ => cty_formula_existential_arity(term, 0)
  }
}

///|
fn collect_tuple_params(
  arities : Map[Int, Unit],
  parameters : ArrayView[@parser.Param],
) -> Unit {
  for parameter in parameters {
    collect_tuple_pty(arities, parameter.param_type)
  }
}

///|
fn collect_tuple_function(
  arities : Map[Int, Unit],
  definition : @parser.FunctionDef,
) -> Unit {
  collect_tuple_binders(arities, definition.binders)
  if definition.return_type is Some(result) {
    collect_tuple_pty(arities, result)
  }
  collect_tuple_pattern(arities, definition.return_pattern)
  collect_tuple_spec(arities, definition.spec)
  collect_tuple_expr(arities, definition.body)
}

///|
fn collect_tuple_routine_literal(
  arities : Map[Int, Unit],
  expression : @parser.Expr,
) -> Bool {
  match expression.desc {
    Efun(binders, result, pattern, _, spec, body) => {
      collect_tuple_binders(arities, binders)
      if result is Some(result) {
        collect_tuple_pty(arities, result)
      }
      collect_tuple_pattern(arities, pattern)
      collect_tuple_spec(arities, spec)
      collect_tuple_expr(arities, body)
      true
    }
    Eany(parameters, _, result, pattern, _, spec) => {
      collect_tuple_params(arities, parameters)
      if result is Some(result) {
        collect_tuple_pty(arities, result)
      }
      collect_tuple_pattern(arities, pattern)
      collect_tuple_spec(arities, spec)
      true
    }
    _ => false
  }
}

///|
fn collect_tuple_expr(
  arities : Map[Int, Unit],
  expression : @parser.Expr,
) -> Unit {
  match expression.desc {
    Etrue | Efalse | Econst(_) | Eident(_) | Eidpur(_) | Eabsurd => ()
    Eref | Easref(_) => record_tuple_arity(arities, -1)
    Eidapp(_, arguments) =>
      for argument in arguments {
        collect_tuple_expr(arities, argument)
      }
    Eapply(function_, argument) => {
      record_tuple_arity(arities, -3)
      if !expr_application_has_ident_head(expression) {
        record_tuple_arity(arities, -2)
      }
      collect_tuple_expr(arities, function_)
      collect_tuple_expr(arities, argument)
    }
    Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Esequence(function_, argument)
    | Eand(function_, argument)
    | Eor(function_, argument) => {
      collect_tuple_expr(arities, function_)
      collect_tuple_expr(arities, argument)
    }
    Elet(_, _, kind, value, body) => {
      if kind == RKfunc || kind == RKpred {
        // Explicitly pure local routines are represented by Why3's `RLpv`
        // mapping variable, whose purified type is a curried HighOrd arrow.
        record_tuple_arity(arities, -2)
      }
      if !collect_tuple_routine_literal(arities, value) {
        collect_tuple_expr(arities, value)
      }
      collect_tuple_expr(arities, body)
    }
    Erec(definitions, body) => {
      for definition in definitions {
        if definition.kind == RKfunc || definition.kind == RKpred {
          record_tuple_arity(arities, -2)
        }
        collect_tuple_function(arities, definition)
      }
      collect_tuple_expr(arities, body)
    }
    Efun(binders, _, _, _, _, _) => {
      if !binders.is_empty() {
        record_tuple_arity(arities, -2)
      }
      ignore(collect_tuple_routine_literal(arities, expression))
    }
    Eany(parameters, _, _, _, _, _) => {
      if !parameters.is_empty() {
        record_tuple_arity(arities, -2)
      }
      ignore(collect_tuple_routine_literal(arities, expression))
    }
    Etuple(arguments) => {
      record_tuple_arity(arities, arguments.length())
      for argument in arguments {
        collect_tuple_expr(arities, argument)
      }
    }
    Erecord(fields) =>
      for field in fields {
        collect_tuple_expr(arities, field.1)
      }
    Eupdate(source, fields) => {
      collect_tuple_expr(arities, source)
      for field in fields {
        collect_tuple_expr(arities, field.1)
      }
    }
    Eassign(assignments) =>
      for assignment in assignments {
        collect_tuple_expr(arities, assignment.target)
        collect_tuple_expr(arities, assignment.value)
      }
    Eif(condition, consequent, alternative) => {
      collect_tuple_expr(arities, condition)
      collect_tuple_expr(arities, consequent)
      collect_tuple_expr(arities, alternative)
    }
    Ewhile(condition, invariant, variant, body) => {
      collect_tuple_expr(arities, condition)
      collect_tuple_invariant(arities, invariant)
      collect_tuple_variant(arities, variant)
      collect_tuple_expr(arities, body)
    }
    Enot(inner)
    | Escope(_, inner)
    | Elabel(_, inner)
    | Eghost(inner)
    | Eattr(_, inner)
    | Eoptexn(_, _, inner) => collect_tuple_expr(arities, inner)
    Ematch(scrutinee, regular, exceptional) => {
      collect_tuple_expr(arities, scrutinee)
      for branch in regular {
        collect_tuple_pattern(arities, branch.pattern)
        collect_tuple_expr(arities, branch.body)
      }
      for branch in exceptional {
        if branch.pattern is Some(pattern) {
          collect_tuple_pattern(arities, pattern)
        }
        collect_tuple_expr(arities, branch.body)
      }
    }
    Epure(term) | Eassert(_, term) => collect_tuple_term(arities, term)
    Eraise(_, payload) =>
      if payload is Some(payload) {
        collect_tuple_expr(arities, payload)
      }
    Eexn(_, payload, _, body) => {
      collect_tuple_pty(arities, payload)
      collect_tuple_expr(arities, body)
    }
    Efor(_, first, _, last, invariant, body) => {
      collect_tuple_expr(arities, first)
      collect_tuple_expr(arities, last)
      collect_tuple_invariant(arities, invariant)
      collect_tuple_expr(arities, body)
    }
    Ecast(inner, annotation) => {
      collect_tuple_expr(arities, inner)
      collect_tuple_pty(arities, annotation)
    }
  }
}

///|
fn collect_tuple_type_declaration(
  arities : Map[Int, Unit],
  declaration : @parser.TypeDecl,
) -> Unit {
  collect_tuple_invariant(arities, declaration.invariant)
  if declaration.witness is Some(witness) {
    collect_tuple_expr(arities, witness)
    if declaration.definition is TDrecord(fields) {
      // Why3 checks a record-type witness through the tuple of its fields,
      // before the represented type itself has entered the pure theory.
      record_tuple_arity(arities, fields.length())
    }
  }
  match declaration.definition {
    TDalias(target) => collect_tuple_pty(arities, target)
    TDalgebraic(cases) =>
      for case_ in cases {
        collect_tuple_params(arities, case_.params)
      }
    TDrecord(fields) =>
      for field in fields {
        collect_tuple_pty(arities, field.field_type)
      }
    TDrange(_, _) | TDfloat(_, _) => ()
  }
}

///|
fn collect_tuple_declaration(
  arities : Map[Int, Unit],
  declaration : @parser.Decl,
) -> Unit {
  match declaration {
    Dtype(declarations) =>
      for declaration in declarations {
        collect_tuple_type_declaration(arities, declaration)
      }
    Dlogic(declarations) =>
      for declaration in declarations {
        collect_tuple_params(arities, declaration.params)
        if declaration.return_type is Some(result) {
          collect_tuple_pty(arities, result)
        }
        if declaration.definition is Some(definition) {
          collect_tuple_term(arities, definition)
        }
      }
    Dind(_, declarations) =>
      for declaration in declarations {
        collect_tuple_params(arities, declaration.params)
        for case_ in declaration.cases {
          collect_tuple_term(arities, case_.body)
        }
      }
    Dprop(kind, _, formula) => {
      collect_tuple_term(arities, formula)
      if kind != Pgoal {
        let result_arity = cty_formula_result_arity(formula)
        if result_arity > 1 {
          record_tuple_arity(arities, result_arity)
        }
      }
    }
    Dlet(_, _, _, expression) =>
      if !collect_tuple_routine_literal(arities, expression) {
        collect_tuple_expr(arities, expression)
      }
    Drec(definitions) =>
      for definition in definitions {
        collect_tuple_function(arities, definition)
      }
    Dexn(_, payload, _) => collect_tuple_pty(arities, payload)
    Dmeta(_, arguments) =>
      for argument in arguments {
        if argument is Mty(annotation) {
          collect_tuple_pty(arities, annotation)
        }
      }
    Dcloneexport(_, _, substitutions)
    | Dcloneimport(_, _, _, _, substitutions) =>
      for substitution in substitutions {
        if substitution is CStsym(_, _, target) {
          collect_tuple_pty(arities, target)
        }
      }
    // Dependencies inside a scope are installed while elaborating each nested
    // declaration.  Hoisting them here changes the module-unit order compared
    // with Why3's declaration-driven `add_use`.
    Dscope(_, _, _, _) => ()
    Duseexport(_) | Duseimport(_, _, _) | Dimport(_) => ()
  }
}

///|
fn tuple_declaration_dependencies(declaration : @parser.Decl) -> Array[Int] {
  let arities : Map[Int, Unit] = Map([])
  collect_tuple_declaration(arities, declaration)
  let result = [ for arity in arities.keys() if arity >= 0 => arity ]
  result.sort_by(Int::compare)
  result
}

///|
fn reference_declaration_dependency(declaration : @parser.Decl) -> Bool {
  let arities : Map[Int, Unit] = Map([])
  collect_tuple_declaration(arities, declaration)
  arities.contains(-1)
}

///|
fn high_order_declaration_dependency(declaration : @parser.Decl) -> Bool {
  let arities : Map[Int, Unit] = Map([])
  collect_tuple_declaration(arities, declaration)
  arities.contains(-2)
}

///|
fn collect_signature_function(
  arities : Map[Int, Unit],
  definition : @parser.FunctionDef,
) -> Unit {
  collect_tuple_binders(arities, definition.binders)
  if definition.return_type is Some(result) {
    collect_tuple_pty(arities, result)
  }
  collect_tuple_pattern(arities, definition.return_pattern)
}

///|
fn collect_signature_high_order_dependency(
  arities : Map[Int, Unit],
  declaration : @parser.Decl,
) -> Unit {
  match declaration {
    Dtype(declarations) =>
      for declaration in declarations {
        match declaration.definition {
          TDalias(target) => collect_tuple_pty(arities, target)
          TDalgebraic(cases) =>
            for case_ in cases {
              collect_tuple_params(arities, case_.params)
            }
          TDrecord(fields) =>
            for field in fields {
              collect_tuple_pty(arities, field.field_type)
            }
          TDrange(_, _) | TDfloat(_, _) => ()
        }
      }
    Dlogic(declarations) =>
      for declaration in declarations {
        collect_tuple_params(arities, declaration.params)
        if declaration.return_type is Some(result) {
          collect_tuple_pty(arities, result)
        }
      }
    Dind(_, declarations) =>
      for declaration in declarations {
        collect_tuple_params(arities, declaration.params)
      }
    Dlet(_, _, _, expression) =>
      match expression.desc {
        Efun(binders, result, pattern, _, _, _) => {
          collect_tuple_binders(arities, binders)
          if result is Some(result) {
            collect_tuple_pty(arities, result)
          }
          collect_tuple_pattern(arities, pattern)
        }
        Eany(parameters, _, result, pattern, _, _) => {
          collect_tuple_params(arities, parameters)
          if result is Some(result) {
            collect_tuple_pty(arities, result)
          }
          collect_tuple_pattern(arities, pattern)
        }
        _ => ()
      }
    Drec(definitions) =>
      for definition in definitions {
        collect_signature_function(arities, definition)
      }
    Dexn(_, payload, _) => collect_tuple_pty(arities, payload)
    Dcloneexport(_, _, substitutions)
    | Dcloneimport(_, _, _, _, substitutions) =>
      for substitution in substitutions {
        if substitution is CStsym(_, _, target) {
          collect_tuple_pty(arities, target)
        }
      }
    Dprop(_, _, _)
    | Dmeta(_, _)
    | Dscope(_, _, _, _)
    | Duseexport(_)
    | Duseimport(_, _, _)
    | Dimport(_) => ()
  }
}

///|
/// Whether the declaration's exported symbol signatures, rather than only an
/// implementation term such as a local lambda, mention the function type.
fn signature_high_order_declaration_dependency(
  declaration : @parser.Decl,
) -> Bool {
  let arities : Map[Int, Unit] = Map([])
  collect_signature_high_order_dependency(arities, declaration)
  arities.contains(-2)
}

///|
fn application_declaration_dependency(declaration : @parser.Decl) -> Bool {
  let arities : Map[Int, Unit] = Map([])
  collect_tuple_declaration(arities, declaration)
  arities.contains(-3)
}

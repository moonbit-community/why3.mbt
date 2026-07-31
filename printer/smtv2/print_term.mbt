// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn print_term_template(
  state : PrinterState,
  template : BytesView,
  arguments : ArrayView[@logic.Term],
) -> Unit raise PrinterError {
  let mut literal_start = 0
  let mut index = 0
  while index < template.length() {
    if template[index] != b'%' {
      index = index + 1
      continue
    }
    state.writer.write(template[literal_start:index])
    let (argument, next) = parse_template_index(template, index + 1)
    if argument > arguments.length() {
      fail_printer(
        InvalidSyntaxTemplate,
        "SMT logic syntax placeholder exceeds symbol arity",
      )
    }
    print_expression(state, arguments[argument - 1])
    index = next
    literal_start = next
  }
  state.writer.write(template[literal_start:])
}

///|
fn type_contains_variable(
  ty : @logic.Ty,
  variable : @logic.TyVarSymbol,
) -> Bool {
  match ty.view() {
    TyVar(candidate) => candidate == variable
    TyApp(_, arguments) =>
      arguments.any(argument => type_contains_variable(argument, variable))
  }
}

///|
fn logic_symbol_is_unambiguous(symbol : @logic.LSymbol) -> Bool {
  let view = symbol.view()
  guard view.result_type is Some(result_type) else { return true }
  result_type
  .free_variables()
  .all(variable => {
    view.argument_types.any(argument => {
      type_contains_variable(argument, variable)
    })
  })
}

///|
fn print_application(
  state : PrinterState,
  symbol : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
  result_type : @logic.Ty?,
) -> Unit raise PrinterError {
  match state.syntax.logic_template(symbol) {
    Some(template) => print_term_template(state, template, arguments)
    None => {
      let ambiguous = result_type is Some(_) &&
        !logic_symbol_is_unambiguous(symbol)
      if arguments.is_empty() {
        if ambiguous {
          state.writer.write(b"(as ")
          print_logic_identifier(state, symbol)
          state.writer.write(b" ")
          guard result_type is Some(result_type) else {
            fail_printer(
              UnsupportedTerm,
              "ambiguous value application has no result type",
            )
          }
          print_type(state, result_type)
          state.writer.write(b")")
        } else {
          print_logic_identifier(state, symbol)
        }
      } else if ambiguous {
        state.writer.write(b"((as ")
        print_logic_identifier(state, symbol)
        state.writer.write(b" ")
        guard result_type is Some(result_type) else {
          fail_printer(
            UnsupportedTerm,
            "ambiguous value application has no result type",
          )
        }
        print_type(state, result_type)
        state.writer.write(b")")
        for argument in arguments {
          state.writer.write(b" ")
          print_expression(state, argument)
        }
        state.writer.write(b")")
      } else {
        state.writer.write(b"(")
        print_logic_identifier(state, symbol)
        for argument in arguments {
          state.writer.write(b" ")
          print_expression(state, argument)
        }
        state.writer.write(b")")
      }
    }
  }
}

///|
fn print_case_body(
  state : PrinterState,
  body : @logic.Term,
  formula_body : Bool,
) -> Unit raise PrinterError {
  if formula_body {
    print_formula(state, body)
  } else {
    print_term(state, body)
  }
}

///|
fn print_match_pattern(
  state : PrinterState,
  pattern : @logic.Pattern,
) -> Unit raise PrinterError {
  match pattern.view() {
    Pwild(_) => state.writer.write(state.names.fresh(b"wildcard"))
    Papp(symbol, arguments, _) =>
      if arguments.is_empty() {
        print_logic_identifier(state, symbol)
      } else {
        state.writer.write(b"(")
        print_logic_identifier(state, symbol)
        for argument in arguments {
          guard argument.view() is Pvar(variable) else {
            fail_printer(
              UnsupportedTerm,
              "nested pattern matching must be compiled before SMT printing",
            )
          }
          state.writer.write(b" ")
          print_variable_identifier(state, variable)
        }
        state.writer.write(b")")
      }
    Pvar(_) | Por(_, _, _) | Pas(_, _, _) =>
      fail_printer(
        UnsupportedTerm,
        "nested pattern matching must be compiled before SMT printing",
      )
  }
}

///|
fn print_boolean_case(
  state : PrinterState,
  scrutinee : @logic.Term,
  branches : ArrayView[@logic.TermBranch],
  formula_body : Bool,
) -> Unit raise PrinterError {
  guard branches.length() == 2 else {
    fail_printer(
      UnsupportedTerm,
      "Boolean pattern matching must have exactly two branches",
    )
  }
  let first = branches[0].view()
  let second = branches[1].view()
  guard first.pattern.view() is Papp(first_constructor, _, _) else {
    fail_printer(
      UnsupportedTerm,
      "Boolean pattern matching must start with a constructor",
    )
  }
  let first_is_true = first_constructor.view().origin
    .attributes()
    .any(attribute => attribute == b"why3:builtin:boolean:true")
  let (then_branch, else_branch) = if first_is_true {
    (first.body, second.body)
  } else {
    (second.body, first.body)
  }
  state.writer.write(b"(ite ")
  print_term(state, scrutinee)
  state.writer.write(b" ")
  print_case_body(state, then_branch, formula_body)
  state.writer.write(b" ")
  print_case_body(state, else_branch, formula_body)
  state.writer.write(b")")
}

///|
fn print_case(
  state : PrinterState,
  scrutinee : @logic.Term,
  branches : ArrayView[@logic.TermBranch],
  formula_body : Bool,
) -> Unit raise PrinterError {
  if scrutinee.ty() is Some(ty) &&
    ty.view() is TyApp(symbol, _) &&
    symbol.builtin_kind() == Some(BuiltinBoolean) {
    print_boolean_case(state, scrutinee, branches, formula_body)
    return
  }
  state.writer.write(b"(match ")
  print_term(state, scrutinee)
  state.writer.write(b" (")
  for index, branch in branches {
    if index > 0 {
      state.writer.write(b" ")
    }
    let view = branch.view()
    state.writer.write(b"(")
    print_match_pattern(state, view.pattern)
    state.writer.write(b" ")
    print_case_body(state, view.body, formula_body)
    state.writer.write(b")")
  }
  state.writer.write(b"))")
}

///|
fn print_term(
  state : PrinterState,
  term : @logic.Term,
) -> Unit raise PrinterError {
  match term.view() {
    Tvar(variable) => print_variable_identifier(state, variable)
    Tconst(constant) => print_constant(state, constant)
    Tapp(symbol, _, arguments) =>
      print_application(state, symbol, arguments, term.ty())
    Tif(condition, then_branch, else_branch) => {
      state.writer.write(b"(ite ")
      print_formula(state, condition)
      state.writer.write(b" ")
      print_term(state, then_branch)
      state.writer.write(b" ")
      print_term(state, else_branch)
      state.writer.write(b")")
    }
    Tlet(variable, value, body) => {
      state.writer.write(b"(let ((")
      print_variable_identifier(state, variable)
      state.writer.write(b" ")
      print_term(state, value)
      state.writer.write(b")) ")
      print_term(state, body)
      state.writer.write(b")")
      state.names.forget(variable.semantic_id())
    }
    Tcase(scrutinee, branches) => print_case(state, scrutinee, branches, false)
    Teps(_, _) =>
      fail_printer(UnsupportedTerm, "SMT term still contains epsilon")
    Tquant(_, _, _, _) | Tbinop(_, _, _) | Tnot(_) | Ttrue | Tfalse =>
      fail_printer(
        UnsupportedTerm,
        "formula found where SMT value was expected",
      )
  }
}

///|
fn print_triggers(
  state : PrinterState,
  triggers : ArrayView[Array[@logic.Term]],
) -> Unit raise PrinterError {
  for group in triggers {
    state.writer.write(b" :pattern (")
    for index, trigger in group {
      if index > 0 {
        state.writer.write(b" ")
      }
      print_expression(state, trigger)
    }
    state.writer.write(b")")
  }
}

///|
fn print_formula(
  state : PrinterState,
  formula : @logic.Term,
) -> Unit raise PrinterError {
  match formula.view() {
    Tapp(symbol, _, arguments) =>
      print_application(state, symbol, arguments, None)
    Tquant(quantifier, binders, triggers, body) => {
      state.writer.write(
        if quantifier == ForallQuantifier {
          b"(forall ("
        } else {
          b"(exists ("
        },
      )
      for index, binder in binders {
        if index > 0 {
          state.writer.write(b" ")
        }
        print_typed_variable(state, binder)
      }
      state.writer.write(b") ")
      if triggers.is_empty() {
        print_formula(state, body)
      } else {
        state.writer.write(b"(! ")
        print_formula(state, body)
        print_triggers(state, triggers)
        state.writer.write(b")")
      }
      state.writer.write(b")")
      for binder in binders {
        state.names.forget(binder.semantic_id())
      }
    }
    Tbinop(operator, left, right) => {
      let token = match operator {
        And => b"and"
        Or => b"or"
        Implies => b"=>"
        Iff => b"="
      }
      state.writer.write(b"(")
      state.writer.write(token)
      state.writer.write(b" ")
      print_formula(state, left)
      state.writer.write(b" ")
      print_formula(state, right)
      state.writer.write(b")")
    }
    Tnot(inner) => {
      state.writer.write(b"(not ")
      print_formula(state, inner)
      state.writer.write(b")")
    }
    Ttrue => state.writer.write(b"true")
    Tfalse => state.writer.write(b"false")
    Tif(condition, then_branch, else_branch) => {
      state.writer.write(b"(ite ")
      print_formula(state, condition)
      state.writer.write(b" ")
      print_formula(state, then_branch)
      state.writer.write(b" ")
      print_formula(state, else_branch)
      state.writer.write(b")")
    }
    Tlet(variable, value, body) => {
      state.writer.write(b"(let ((")
      print_variable_identifier(state, variable)
      state.writer.write(b" ")
      print_term(state, value)
      state.writer.write(b")) ")
      print_formula(state, body)
      state.writer.write(b")")
      state.names.forget(variable.semantic_id())
    }
    Tcase(scrutinee, branches) => print_case(state, scrutinee, branches, true)
    Tvar(_) | Tconst(_) | Teps(_, _) =>
      fail_printer(
        UnsupportedTerm,
        "SMT formula contains an invalid value node",
      )
  }
}

///|
fn print_expression(
  state : PrinterState,
  expression : @logic.Term,
) -> Unit raise PrinterError {
  if expression.is_formula() {
    print_formula(state, expression)
  } else {
    print_term(state, expression)
  }
}

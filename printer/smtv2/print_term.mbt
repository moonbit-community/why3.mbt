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
fn print_application(
  state : PrinterState,
  symbol : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
) -> Unit raise PrinterError {
  match state.syntax.logic_template(symbol) {
    Some(template) => print_term_template(state, template, arguments)
    None => {
      if !arguments.is_empty() {
        state.writer.write(b"(")
      }
      print_logic_identifier(state, symbol)
      for argument in arguments {
        state.writer.write(b" ")
        print_expression(state, argument)
      }
      if !arguments.is_empty() {
        state.writer.write(b")")
      }
    }
  }
}

///|
fn print_term(
  state : PrinterState,
  term : @logic.Term,
) -> Unit raise PrinterError {
  match term.view() {
    Tvar(variable) => print_variable_identifier(state, variable)
    Tconst(constant) => print_constant(state, constant)
    Tapp(symbol, _, arguments) => print_application(state, symbol, arguments)
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
    Tcase(_, _) =>
      fail_printer(UnsupportedTerm, "SMT term still contains pattern matching")
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
    Tapp(symbol, _, arguments) => print_application(state, symbol, arguments)
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
    Tcase(_, _) =>
      fail_printer(
        UnsupportedTerm,
        "SMT formula still contains pattern matching",
      )
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

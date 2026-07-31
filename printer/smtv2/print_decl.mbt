// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn print_type_declaration(
  state : PrinterState,
  symbol : @logic.TypeSymbol,
) -> Unit {
  if state.syntax.type_template(symbol) is Some(_) ||
    symbol.view().definition is Alias(_) {
    return
  }
  state.writer.write(b"(declare-sort ")
  print_type_identifier(state, symbol)
  state.writer.write(b" ")
  state.writer.write_string_utf8(symbol.arity().to_string())
  state.writer.write(b")\n")
}

///|
fn print_data_declarations(
  state : PrinterState,
  declarations : ArrayView[@logic.DataDeclaration],
) -> Unit raise PrinterError {
  if declarations.length() == 1 &&
    state.syntax.type_template(declarations[0].view().type_symbol) is Some(_) {
    return
  }
  state.writer.write(b"(declare-datatypes (")
  for index, declaration in declarations {
    if index > 0 {
      state.writer.write(b" ")
    }
    let view = declaration.view()
    state.writer.write(b"(")
    print_type_identifier(state, view.type_symbol)
    state.writer.write(b" ")
    state.writer.write_string_utf8(view.type_symbol.arity().to_string())
    state.writer.write(b")")
  }
  state.writer.write(b") (")
  for declaration_index, declaration in declarations {
    if declaration_index > 0 {
      state.writer.write(b" ")
    }
    let declaration_view = declaration.view()
    let parameters = declaration_view.type_symbol.view().parameters
    if parameters.is_empty() {
      state.writer.write(b"(")
    } else {
      state.writer.write(b"(par (")
      for index, parameter in parameters {
        if index > 0 {
          state.writer.write(b" ")
        }
        print_type_variable_identifier(state, parameter)
      }
      state.writer.write(b") (")
    }
    let is_record = declaration_view.constructors.length() == 1
    for constructor_index, data_constructor in declaration_view.constructors {
      if constructor_index > 0 {
        state.writer.write(b" ")
      }
      let view = data_constructor.view()
      state.writer.write(b"(")
      print_logic_identifier(state, view.symbol)
      for argument_index, argument in view.symbol.view().argument_types {
        state.writer.write(b" (")
        match view.projections[argument_index] {
          Some(projection) => {
            if !is_record {
              fail_printer(
                UnsupportedDatatype,
                "sum types cannot declare projections in SMT-LIB 2.6",
              )
            }
            print_logic_identifier(state, projection)
          }
          None => {
            let name = view.symbol.view().name + b"_proj"
            state.writer.write(state.names.fresh(name))
          }
        }
        state.writer.write(b" ")
        print_type(state, argument)
        state.writer.write(b")")
      }
      state.writer.write(b")")
    }
    state.writer.write(if parameters.is_empty() { b")" } else { b"))" })
  }
  state.writer.write(b"))\n")
}

///|
fn print_parameter_declaration(
  state : PrinterState,
  symbol : @logic.LSymbol,
) -> Unit raise PrinterError {
  if state.syntax.logic_template(symbol) is Some(_) {
    return
  }
  let view = symbol.view()
  state.writer.write(b"(declare-fun ")
  print_logic_identifier(state, symbol)
  state.writer.write(b" (")
  for index, argument in view.argument_types {
    if index > 0 {
      state.writer.write(b" ")
    }
    print_type(state, argument)
  }
  state.writer.write(b") ")
  print_value_type(state, view.result_type)
  state.writer.write(b")\n")
}

///|
fn print_logic_definition(
  state : PrinterState,
  definition : @logic.LogicDefinition,
) -> Unit raise PrinterError {
  let view = definition.view()
  if state.syntax.logic_template(view.symbol) is Some(_) {
    return
  }
  state.writer.write(b"(define-fun ")
  print_logic_identifier(state, view.symbol)
  state.writer.write(b" (")
  for index, parameter in view.parameters {
    if index > 0 {
      state.writer.write(b" ")
    }
    print_typed_variable(state, parameter)
  }
  state.writer.write(b") ")
  print_value_type(state, view.symbol.view().result_type)
  state.writer.write(b" ")
  print_expression(state, view.body)
  state.writer.write(b")\n")
  for parameter in view.parameters {
    state.names.forget(parameter.semantic_id())
  }
}

///|
fn print_proposition(
  state : PrinterState,
  kind : @logic.PropositionKind,
  symbol : @logic.PrSymbol,
  formula : @logic.Term,
) -> Unit raise PrinterError {
  if state.syntax.removes(symbol) {
    return
  }
  match kind {
    Paxiom => {
      state.writer.write(b"(assert ")
      print_formula(state, formula)
      state.writer.write(b")\n")
    }
    Pgoal => {
      state.writer.write(b"(assert (not ")
      print_formula(state, formula)
      state.writer.write(b"))\n")
      if state.request_model && state.model_needs_push {
        state.writer.write(b"(push)\n")
      }
      state.writer.write(b"(check-sat)\n")
      if state.request_model {
        state.writer.write(b"(get-model)\n")
      }
    }
    Plemma =>
      fail_printer(
        UnsupportedDeclaration,
        "lemma declaration reached the SMT printer",
      )
  }
}

///|
fn print_declaration(
  state : PrinterState,
  declaration : @logic.Decl,
) -> Unit raise PrinterError {
  match declaration.view() {
    Dtype(symbols) =>
      for symbol in symbols {
        print_type_declaration(state, symbol)
      }
    Ddata(declarations) => print_data_declarations(state, declarations)
    Dparam(symbol) => print_parameter_declaration(state, symbol)
    Dlogic(definitions) =>
      for definition in definitions {
        print_logic_definition(state, definition)
      }
    Dind(_, _) =>
      fail_printer(
        UnsupportedDeclaration,
        "inductive declaration reached the SMT printer",
      )
    Dprop(kind, symbol, formula) =>
      print_proposition(state, kind, symbol, formula)
  }
}

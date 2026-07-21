// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct PrinterState {
  writer : QueryWriter
  names : NameAllocator
  syntax : SyntaxMaps
}

///|
fn PrinterState::new(syntax : SyntaxMaps) -> PrinterState {
  { writer: QueryWriter::new(), names: NameAllocator::new(), syntax }
}

///|
fn print_type_identifier(
  state : PrinterState,
  symbol : @logic.TypeSymbol,
) -> Unit {
  let view = symbol.view()
  state.writer.identifier(
    state.names.unique(view.id, view.name),
    view.id,
    view.origin,
  )
}

///|
fn print_logic_identifier(
  state : PrinterState,
  symbol : @logic.LSymbol,
) -> Unit {
  let view = symbol.view()
  state.writer.identifier(
    state.names.unique(view.id, view.name),
    view.id,
    view.origin,
  )
}

///|
fn print_variable_identifier(
  state : PrinterState,
  symbol : @logic.VSymbol,
) -> Unit {
  let view = symbol.view()
  state.writer.identifier(
    state.names.unique(view.id, view.name),
    view.id,
    view.origin,
  )
}

///|
fn parse_template_index(
  template : BytesView,
  start : Int,
) -> (Int, Int) raise PrinterError {
  let mut index = start
  let mut value = 0
  while index < template.length() &&
        template[index] >= b'0' &&
        template[index] <= b'9' {
    value = value * 10 + template[index].to_int() - b'0'.to_int()
    index = index + 1
  }
  if index == start || value <= 0 {
    fail_printer(
      InvalidSyntaxTemplate,
      "SMT syntax placeholder must be a positive decimal argument index",
    )
  }
  (value, index)
}

///|
fn print_type_template(
  state : PrinterState,
  template : BytesView,
  arguments : ArrayView[@logic.Ty],
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
        "SMT type syntax placeholder exceeds symbol arity",
      )
    }
    print_type(state, arguments[argument - 1])
    index = next
    literal_start = next
  }
  state.writer.write(template[literal_start:])
}

///|
fn print_type(state : PrinterState, ty : @logic.Ty) -> Unit raise PrinterError {
  match ty.view() {
    TyVar(_) =>
      fail_printer(
        ResidualTypeVariable,
        "SMT printer received a residual type variable",
      )
    TyApp(symbol, arguments) =>
      match state.syntax.type_template(symbol) {
        Some(template) => print_type_template(state, template, arguments)
        None => {
          if !arguments.is_empty() {
            state.writer.write(b"(")
          }
          print_type_identifier(state, symbol)
          for argument in arguments {
            state.writer.write(b" ")
            print_type(state, argument)
          }
          if !arguments.is_empty() {
            state.writer.write(b")")
          }
        }
      }
  }
}

///|
fn print_value_type(
  state : PrinterState,
  ty : @logic.Ty?,
) -> Unit raise PrinterError {
  match ty {
    None => state.writer.write(b"Bool")
    Some(ty) => print_type(state, ty)
  }
}

///|
fn print_typed_variable(
  state : PrinterState,
  variable : @logic.VSymbol,
) -> Unit raise PrinterError {
  state.writer.write(b"(")
  print_variable_identifier(state, variable)
  state.writer.write(b" ")
  print_type(state, variable.ty())
  state.writer.write(b")")
}

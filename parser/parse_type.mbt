// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

// WhyML type and binder grammar productions.

///|
fn starts_ty_block(parser : Parser) -> Bool {
  parser.at_symbol(LeftPar) || parser.at_symbol(LeftBrc)
}

///|
fn starts_ty_arg(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true) ||
  parser.peek_kind_n(0) is Some(QuoteLident(_)) ||
  starts_ty_block(parser)
}

///|
fn Parser::parse_ty_block_body(
  self : Parser,
  opening : LocatedToken,
) -> Pty raise {
  if opening.kind is Symbol(LeftBrc) {
    let ty = self.parse_ty()
    ignore(self.expect_symbol(RightBrc))
    return PTpure(ty)
  }
  if self.consume_symbol(RightPar) is Some(_) {
    return PTtuple([])
  }
  let first = self.parse_ty()
  if self.consume_symbol(Comma) is None {
    ignore(self.expect_symbol(RightPar))
    return PTparen(first)
  }
  let elements = parse_comma_list2(
    self,
    parser => starts_ty_arg(parser),
    parser => parser.parse_ty(),
    expected="type",
    first=Some(first),
  )
  ignore(self.expect_symbol(RightPar))
  PTtuple(elements)
}

///|
fn Parser::parse_ty_block(self : Parser) -> Pty raise {
  let opening = self.peek()
  guard opening.kind is Symbol(LeftPar | LeftBrc) else {
    self.fail_syntax("type block")
  }
  ignore(self.advance())
  self.enter_nesting(opening.span)
  let result = self.parse_ty_block_body(opening) catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn QualId::append(self : QualId, ident : Ident) -> QualId {
  Qdot(self, ident)
}

///|
fn Parser::parse_ty_arg(self : Parser) -> Pty raise {
  if self.peek_kind_n(0) is Some(QuoteLident(_)) {
    return PTtyvar(self.parse_quote_lident())
  }
  if starts_ty_block(self) {
    return self.parse_ty_block()
  }
  if starts_uident_kind(self.peek_kind_n(0)) {
    let path = self.parse_uqualid()
    if self.consume_symbol(Dot) is Some(_) {
      if starts_ty_block(self) {
        return PTscope(path, self.parse_ty_block())
      }
      let tail = self.parse_lident(false, true)
      return PTtyapp(path.append(tail), [])
    }
    return PTtyapp(path, [])
  }
  PTtyapp(self.parse_lqualid(), [])
}

///|
fn Parser::parse_ty_application(self : Parser) -> Pty raise {
  let head = self.parse_ty_arg()
  guard head is PTtyapp(constructor_path, []) && starts_ty_arg(self) else {
    return head
  }
  let arguments : Array[Pty] = []
  while starts_ty_arg(self) {
    arguments.push(self.parse_ty_arg())
  }
  PTtyapp(constructor_path, arguments)
}

///|
fn Parser::parse_ty(self : Parser) -> Pty raise {
  let left = self.parse_ty_application()
  if self.consume_symbol(Arrow) is Some(_) {
    PTarrow(left, self.parse_ty())
  } else {
    left
  }
}

///|
fn Parser::parse_cast(self : Parser) -> Pty raise {
  ignore(self.expect_symbol(Colon))
  self.parse_ty()
}

///|
fn is_reference_ident(ident : Ident) -> Bool {
  for attribute in ident.attributes {
    if attribute is Text(name) && name == reference_attribute {
      return true
    }
  }
  false
}

///|
fn[A] fail_binder_semantic(
  kind : ParseErrorKind,
  span : Span,
  actual? : String,
) -> A raise ParseError {
  if actual is Some(actual) {
    fail_with_diagnostic(make_parse_diagnostic(kind, span, actual~))
  } else {
    fail_with_diagnostic(make_parse_diagnostic(kind, span))
  }
}

///|
fn set_reference(ident : Ident) -> Ident raise ParseError {
  if is_reference_ident(ident) {
    fail_binder_semantic(DoubleReference, ident.span)
  }
  { ..ident, attributes: [Text(reference_attribute)] + ident.attributes }
}

///|
fn Parser::parse_sym_binder(self : Parser) -> Ident raise {
  if self.consume_symbol(Amp) is Some(_) {
    return set_reference(
      parse_attrs_ident(self, parser => parser.parse_lident(true, false)),
    )
  }
  parse_attrs_ident(self, parser => parser.parse_lident_rich())
}

///|
fn Parser::parse_var_binder_ident(self : Parser) -> Ident raise {
  if self.consume_symbol(Amp) is Some(_) {
    return set_reference(
      parse_attrs_ident(self, parser => parser.parse_lident(true, false)),
    )
  }
  parse_attrs_ident(self, parser => parser.parse_lident(true, false))
}

///|
fn Parser::parse_ref_binder(self : Parser) -> Ident raise {
  if self.consume_symbol(Amp) is Some(_) {
    let ident = parse_attrs_ident(self, parser => {
      parser.parse_lident(true, false)
    })
    return fail_binder_semantic(DoubleReference, ident.span)
  }
  set_reference(
    parse_attrs_ident(self, parser => parser.parse_lident(true, false)),
  )
}

///|
fn binder_ident(ident : Ident) -> Ident raise ParseError {
  if ident.name == b"ref" {
    fail_binder_semantic(UnexpectedToken, ident.span, actual="ref")
  }
  ident
}

///|
priv struct BinderSlot {
  span : Span
  ident : Ident?
}

///|
fn Parser::parse_binder_slot(self : Parser) -> BinderSlot raise {
  let mark = self.mark()
  if self.consume_symbol(Underscore) is Some(_) {
    return { span: self.span_from(mark), ident: None }
  }
  if self.consume_symbol(Amp) is Some(_) {
    let ident = parse_attrs_ident(self, parser => {
      parser.parse_lident(true, false)
    })
    return { span: self.span_from(mark), ident: Some(set_reference(ident)) }
  }
  let ident = parse_attrs_ident(self, parser => parser.parse_lident(true, false))
  { span: self.span_from(mark), ident: Some(ident) }
}

///|
fn starts_binder_slot(parser : Parser) -> Bool {
  parser.at_symbol(Underscore) ||
  parser.at_symbol(Amp) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), false)
}

///| `binder_vars_head` first parses a type application. Consequently its

///| identifier-shaped prefix intentionally retains Why3 1.7.2's core-name

///|
/// gap; later `binder_var` items still use the `_nq` productions.
fn Parser::parse_binder_head_slots(self : Parser) -> Array[BinderSlot] raise {
  let slots : Array[BinderSlot] = []
  while starts_plain_lident_kind(self.peek_kind_n(0), true) {
    let mark = self.mark()
    let ident = binder_ident(self.parse_lident(false, true))
    slots.push({ span: self.span_from(mark), ident: Some(ident) })
  }
  if !slots.is_empty() && starts_attribute(self) {
    let last_index = slots.length() - 1
    let slot = slots[last_index]
    guard slot.ident is Some(ident) else { self.fail_syntax("named binder") }
    slots[last_index] = {
      span: slot.span.join(self.peek().span),
      ident: Some(ident.add_attributes(parse_attributes(self))),
    }
    slots[last_index] = {
      ..slots[last_index],
      span: slots[last_index].span.join(self.span_from(self.index - 1)),
    }
  }
  slots
}

///|
fn apply_group_reference(
  slot : BinderSlot,
  reference : Bool,
) -> Ident? raise ParseError {
  if !reference {
    return slot.ident
  }
  if slot.ident is Some(ident) {
    Some(set_reference(ident))
  } else {
    fail_binder_semantic(AnonymousReference, slot.span)
  }
}

///|
fn[A] undetermined_parameter(span : Span) -> A raise ParseError {
  fail_binder_semantic(UndeterminedParameterType, span)
}

///|
fn make_parsed_binder(
  span : Span,
  ident : Ident?,
  ghost : Bool,
  binder_type : Pty?,
) -> Array[Binder] {
  [make_binder(span, ident, ghost, binder_type)]
}

///|
fn type_as_binder(ty : Pty, span : Span, ghost : Bool) -> Array[Binder] raise {
  match ty {
    PTparen(PTtyapp(Qident({ name: b"ref", .. }), [PTtyapp(Qident(ident), [])])) =>
      make_parsed_binder(
        span,
        Some(set_reference(binder_ident(ident))),
        ghost,
        None,
      )
    PTtyapp(Qident(ident), []) | PTparen(PTtyapp(Qident(ident), [])) =>
      make_parsed_binder(span, Some(binder_ident(ident)), ghost, None)
    _ => make_parsed_binder(span, None, ghost, Some(ty))
  }
}

///|
fn type_as_param(ty : Pty, span : Span, ghost : Bool) -> Array[Param] {
  [{ span, ident: None, ghost, param_type: ty }]
}

///|
fn Parser::parse_standalone_attributed_name(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  let mark = self.mark()
  let ident = self.parse_lident(true, false)
  let attributes = parse_attributes(self)
  guard !attributes.is_empty() else { self.fail_syntax("attribute") }
  let span = self.span_from(mark)
  let ident = ident.add_attributes(attributes)
  if parameter {
    undetermined_parameter(span)
  } else {
    (make_parsed_binder(span, Some(ident), false, None), [])
  }
}

///|
fn Parser::parse_special_standalone(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  let slot = self.parse_binder_slot()
  if parameter {
    undetermined_parameter(slot.span)
  } else {
    (make_parsed_binder(slot.span, slot.ident, false, None), [])
  }
}

///|
fn Parser::parse_ghost_typed_group(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  let mark = self.mark()
  ignore(self.expect_symbol(LeftPar))
  ignore(self.expect_keyword(Ghost))
  let ty = self.parse_ty()
  ignore(self.expect_symbol(RightPar))
  let span = self.span_from(mark)
  if parameter {
    ([], type_as_param(ty, span, true))
  } else {
    (type_as_binder(ty, span, true), [])
  }
}

///|
fn Parser::parse_binder_var_group(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  ignore(self.expect_symbol(LeftPar))
  let ghost = self.consume_keyword(Ghost) is Some(_)
  let group_reference = self.consume_keyword(Ref) is Some(_)
  let slots = self.parse_binder_head_slots()
  while starts_binder_slot(self) {
    slots.push(self.parse_binder_slot())
  }
  guard !slots.is_empty() else { self.fail_syntax("binder variable") }
  if self.consume_symbol(Colon) is None {
    let closing = self.expect_symbol(RightPar)
    if slots.length() != 1 {
      return self.fail_syntax("type annotation")
    }
    let slot = slots[0]
    let ident = apply_group_reference(slot, group_reference)
    if parameter {
      undetermined_parameter(slot.span)
    } else {
      return (make_parsed_binder(slot.span, ident, ghost, None), [])
    }
    ignore(closing)
  }
  let ty = self.parse_ty()
  ignore(self.expect_symbol(RightPar))
  let binder_type = if group_reference { PTref([ty]) } else { ty }
  let binders : Array[Binder] = []
  let params : Array[Param] = []
  for slot in slots {
    let ident = apply_group_reference(slot, group_reference)
    if parameter {
      params.push({ span: slot.span, ident, ghost, param_type: binder_type })
    } else {
      binders.push(make_binder(slot.span, ident, ghost, Some(binder_type)))
    }
  }
  (binders, params)
}

///|
fn Parser::parse_parenthesized_binder(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  if self.peek_kind_n(1) is Some(Keyword(Ghost)) {
    return parse_alternative(
      self,
      parser => parser.parse_ghost_typed_group(parameter),
      parser => parser.parse_binder_var_group(parameter),
    )
  }
  parse_alternative(
    self,
    parser => {
      let mark = parser.mark()
      let ty = parser.parse_ty_arg()
      let span = parser.span_from(mark)
      if parameter {
        ([], type_as_param(ty, span, false))
      } else {
        (type_as_binder(ty, span, false), [])
      }
    },
    // Menhir's local conflict between `ty_arg` and `binder_vars_rest`.
    parser => parser.parse_binder_var_group(parameter),
  )
}

///|
fn Parser::parse_binder_or_param(
  self : Parser,
  parameter : Bool,
) -> (Array[Binder], Array[Param]) raise {
  if self.at_symbol(Underscore) || self.at_symbol(Amp) {
    return self.parse_special_standalone(parameter)
  }
  if self.at_symbol(LeftPar) {
    return self.parse_parenthesized_binder(parameter)
  }
  if starts_plain_lident_kind(self.peek_kind_n(0), false) &&
    self.peek_kind_n(1) is Some(AttributeToken(_) | PositionToken(_)) {
    return self.parse_standalone_attributed_name(parameter)
  }
  let mark = self.mark()
  let ty = self.parse_ty_arg()
  let span = self.span_from(mark)
  if parameter {
    ([], type_as_param(ty, span, false))
  } else {
    (type_as_binder(ty, span, false), [])
  }
}

///|
fn starts_binder_or_param(parser : Parser) -> Bool {
  starts_ty_arg(parser) || parser.at_symbol(Underscore) || parser.at_symbol(Amp)
}

///|
fn Parser::parse_param(self : Parser) -> Array[Param] raise {
  let (_, params) = self.parse_binder_or_param(true)
  params
}

///|
fn Parser::parse_binder(self : Parser) -> Array[Binder] raise {
  let (binders, _) = self.parse_binder_or_param(false)
  binders
}

///|
fn Parser::parse_params(
  self : Parser,
  require_one : Bool,
) -> Array[Param] raise {
  let params : Array[Param] = []
  while starts_binder_or_param(self) {
    params.push_iter(self.parse_param().iter())
  }
  if require_one && params.is_empty() {
    self.fail_syntax("parameter")
  }
  params
}

///|
fn Parser::parse_binders(self : Parser) -> Array[Binder] raise {
  guard starts_binder_or_param(self) else { self.fail_syntax("binder") }
  let binders : Array[Binder] = []
  while starts_binder_or_param(self) {
    binders.push_iter(self.parse_binder().iter())
  }
  binders
}

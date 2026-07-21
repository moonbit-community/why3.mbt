// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

// Pratt program-expression parser and WhyML control productions.

///|
fn starts_expr_arg(parser : Parser) -> Bool {
  starts_ident(parser) ||
  parser.at_symbol(Amp) ||
  parser.peek_kind_n(0)
  is Some(Integer(_) | Real(_) | StringToken(_) | OpPref(_)) ||
  parser.at_keyword(True) ||
  parser.at_keyword(False) ||
  parser.at_keyword(Begin) ||
  parser.at_keyword(Pure) ||
  parser.at_symbol(LeftBrc) ||
  parser.at_symbol(LeftSqBar)
}

///|
fn starts_assertion(parser : Parser) -> Bool {
  parser.at_keyword(Assert) ||
  parser.at_keyword(Assume) ||
  parser.at_keyword(Check)
}

///|
fn starts_control_expr(parser : Parser) -> Bool {
  parser.at_keyword(If) ||
  parser.at_keyword(Let) ||
  parser.at_keyword(Fun) ||
  parser.at_keyword(Any) ||
  parser.at_keyword(Val) ||
  parser.at_keyword(Match) ||
  parser.at_keyword(Exception) ||
  parser.at_keyword(Label) ||
  parser.at_keyword(While) ||
  parser.at_keyword(For) ||
  parser.at_keyword(Absurd) ||
  parser.at_keyword(Raise) ||
  parser.at_keyword(Return) ||
  parser.at_keyword(Break) ||
  parser.at_keyword(Continue) ||
  parser.at_keyword(Try) ||
  parser.at_keyword(Ghost) ||
  starts_assertion(parser)
}

///|
fn starts_single_expr(parser : Parser) -> Bool {
  starts_expr_arg(parser) ||
  starts_attribute(parser) ||
  starts_prefix_operator(parser) ||
  parser.at_keyword(Not) ||
  starts_control_expr(parser)
}

///|
fn Parser::parse_expr_field(self : Parser) -> (QualId, Expr) raise {
  let field = self.parse_lqualid()
  ignore(self.expect_symbol(Equal))
  (field, self.parse_expr())
}

///|
fn starts_expr_field(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true)
}

///|
fn Parser::parse_expr_record_desc(self : Parser) -> ExprDesc raise {
  Erecord(
    parse_semicolon_list1(
      self,
      parser => starts_expr_field(parser),
      parser => parser.parse_expr_field(),
      expected="record field",
    ),
  )
}

///|
fn Parser::parse_expr_update_desc(self : Parser) -> ExprDesc raise {
  let base = self.parse_expr_arg()
  ignore(self.expect_keyword(With))
  let fields = parse_semicolon_list1(
    self,
    parser => starts_expr_field(parser),
    parser => parser.parse_expr_field(),
    expected="record update field",
  )
  Eupdate(base, fields)
}

///|
fn Parser::parse_expr_block(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.peek()
  guard opening.kind is (Keyword(Begin) | Symbol(LeftPar | LeftBrc)) else {
    self.fail_syntax("expression block")
  }
  ignore(self.advance())
  self.enter_nesting(opening.span)
  let expression = try {
    let desc = if opening.kind is Keyword(Begin) {
      if self.consume_keyword(End) is Some(_) {
        Etuple([])
      } else if starts_spec(self) {
        let first = self.parse_single_spec()
        let specification = spec_union(first, self.parse_spec())
        let body = if self.at_keyword(End) {
          None
        } else {
          Some(self.parse_seq_expr())
        }
        ignore(self.expect_keyword(End))
        let span = self.span_from(mark)
        let body = if body is Some(body) {
          body
        } else {
          make_expr(Etuple([]), span)
        }
        Efun(
          [],
          None,
          make_pattern(Pwild, span),
          MaskVisible,
          specification,
          body,
        )
      } else {
        let inner = self.parse_seq_expr()
        ignore(self.expect_keyword(End))
        inner.desc
      }
    } else if opening.kind is Symbol(LeftPar) {
      if self.consume_symbol(RightPar) is Some(_) {
        Etuple([])
      } else {
        let inner = self.parse_seq_expr()
        ignore(self.expect_symbol(RightPar))
        inner.desc
      }
    } else {
      let desc = parse_alternative(
        self,
        parser => parser.parse_expr_update_desc(),
        parser => parser.parse_expr_record_desc(),
      )
      ignore(self.expect_symbol(RightBrc))
      desc
    }
    make_expr(desc, self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  expression
}

///|
fn Parser::parse_scoped_expr_block(self : Parser) -> Expr raise {
  let mark = self.mark()
  let path = self.parse_uqualid()
  ignore(self.expect_symbol(Dot))
  guard self.at_keyword(Begin) ||
    self.at_symbol(LeftPar) ||
    self.at_symbol(LeftBrc) else {
    self.fail_syntax("expression block")
  }
  let block = self.parse_expr_block()
  make_expr(Escope(path, block), self.span_from(mark))
}

///|
fn Parser::parse_expr_pure_symbol(self : Parser) -> Expr raise {
  let mark = self.mark()
  if self.consume_symbol(LeftBrc) is Some(opening) {
    self.enter_nesting(opening.span)
    let expression = try {
      let path = self.parse_qualid()
      ignore(self.expect_symbol(RightBrc))
      make_expr(Eidpur(path), self.span_from(mark))
    } catch {
      error => {
        self.leave_nesting()
        raise error
      }
    }
    self.leave_nesting()
    return expression
  }
  let path = self.parse_uqualid()
  ignore(self.expect_symbol(Dot))
  let opening = self.expect_symbol(LeftBrc)
  self.enter_nesting(opening.span)
  let result = try {
    let ident = self.parse_ident()
    ignore(self.expect_symbol(RightBrc))
    make_expr(Eidpur(path.append(ident)), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_pure_term_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  ignore(self.expect_keyword(Pure))
  let opening = self.expect_symbol(LeftBrc)
  self.enter_nesting(opening.span)
  let result = try {
    let term = self.parse_term()
    ignore(self.expect_symbol(RightBrc))
    make_expr(Epure(term), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_expr_qualid(self : Parser) -> (Expr, Bool) raise {
  let mark = self.mark()
  let path = self.parse_qualid()
  (
    make_expr(Eident(path), self.span_from(mark)),
    qualid_can_start_term_dot(path),
  )
}

///|
fn Parser::parse_expr_fun_literal(self : Parser) -> Expr raise {
  let opening = self.expect_symbol(LeftSqBar)
  self.enter_nesting(opening.span)
  let result = try {
    let (mappings, default) = parse_alternative(
      self,
      parser => {
        parse_mapping_list_with_default(
          parser,
          parser => starts_single_expr(parser),
          parser => parser.parse_expr(),
          expected="function literal mapping",
        )
      },
      parser => {
        let values = parse_semicolon_list1(
          parser,
          parser => starts_single_expr(parser),
          parser => parser.parse_expr(),
          expected="function literal value",
        )
        (indexed_expr_values(values), None)
      },
    )
    let closing = self.expect_symbol(BarRightSq)
    desugar_expr_function_literal(opening.span, closing.span, mappings, default)
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
priv struct ExprArgResult {
  expression : Expr
  dot_eligible : Bool
}

///|
fn Parser::parse_expr_arg_atom(self : Parser) -> ExprArgResult raise {
  let mark = self.mark()
  let token = self.peek()
  match token.kind {
    Integer(constant) => {
      ignore(self.advance())
      {
        expression: make_expr(Econst(ConstInt(constant)), token.span),
        dot_eligible: false,
      }
    }
    Real(constant) => {
      ignore(self.advance())
      {
        expression: make_expr(Econst(ConstReal(constant)), token.span),
        dot_eligible: false,
      }
    }
    StringToken(bytes) => {
      ignore(self.advance())
      {
        expression: make_expr(Econst(ConstStr(bytes)), token.span),
        dot_eligible: false,
      }
    }
    Keyword(True) => {
      ignore(self.advance())
      { expression: make_expr(Etrue, token.span), dot_eligible: false }
    }
    Keyword(False) => {
      ignore(self.advance())
      { expression: make_expr(Efalse, token.span), dot_eligible: false }
    }
    OpPref(_) => {
      let operator = self.parse_oppref()
      let argument = self.parse_expr_arg_atom()
      {
        expression: make_expr(
          Eidapp(Qident(operator), [argument.expression]),
          self.span_from(mark),
        ),
        dot_eligible: argument.dot_eligible,
      }
    }
    Symbol(Amp) => {
      ignore(self.advance())
      let path = self.parse_qualid()
      {
        expression: make_expr(Easref(path), self.span_from(mark)),
        dot_eligible: false,
      }
    }
    Symbol(LeftSqBar) =>
      { expression: self.parse_expr_fun_literal(), dot_eligible: false }
    Keyword(Pure) =>
      { expression: self.parse_pure_term_expr(), dot_eligible: true }
    Keyword(Begin) =>
      { expression: self.parse_expr_block(), dot_eligible: true }
    Symbol(LeftBrc) => {
      let expression = parse_alternative(
        self,
        parser => parser.parse_expr_block(),
        parser => parser.parse_expr_pure_symbol(),
      )
      { expression, dot_eligible: true }
    }
    Symbol(LeftPar) => {
      let (expression, dot_eligible) = parse_alternative(
        self,
        parser => parser.parse_expr_qualid(),
        parser => (parser.parse_expr_block(), true),
      )
      { expression, dot_eligible }
    }
    Uident(_) | CoreUident(_) => {
      let (expression, dot_eligible) = parse_alternative(
        self,
        parser => (parser.parse_scoped_expr_block(), true),
        parser => {
          parse_alternative(
            parser,
            parser => (parser.parse_expr_pure_symbol(), true),
            parser => parser.parse_expr_qualid(),
          )
        },
      )
      { expression, dot_eligible }
    }
    _ => {
      let (expression, dot_eligible) = self.parse_expr_qualid()
      { expression, dot_eligible }
    }
  }
}

///|
fn mixfix_expr_call(
  base : Expr,
  opening_span : Span,
  closing_span : Span,
  name : Bytes,
  arguments : Array[Expr],
) -> Expr {
  let operator = Ident::{ name, attributes: [], span: opening_span }
  make_expr(
    Eidapp(Qident(operator), [base] + arguments),
    base.span.join(closing_span),
  )
}

///|
fn Parser::parse_expr_index(self : Parser, base : Expr) -> Expr raise {
  let opening = self.expect_symbol(LeftSq)
  self.enter_nesting(opening.span)
  let result = try {
    if self.consume_symbol(DotDot) is Some(_) {
      let upper = self.parse_expr()
      let (suffix, closing_span) = parse_rightsq(self)
      mixfix_expr_call(base, opening.span, closing_span, op_lcut(suffix), [
        upper,
      ])
    } else {
      let first = self.parse_expr()
      if self.consume_symbol(LArrow) is Some(_) {
        let value = self.parse_expr()
        let (suffix, closing_span) = parse_rightsq(self)
        mixfix_expr_call(base, opening.span, closing_span, op_update(suffix), [
          first, value,
        ])
      } else if self.consume_symbol(DotDot) is Some(_) {
        if self.peek_kind_n(0) is Some(Symbol(RightSq) | RightSqQuote(_)) {
          let (suffix, closing_span) = parse_rightsq(self)
          mixfix_expr_call(base, opening.span, closing_span, op_rcut(suffix), [
            first,
          ])
        } else {
          let upper = self.parse_expr()
          let (suffix, closing_span) = parse_rightsq(self)
          mixfix_expr_call(base, opening.span, closing_span, op_cut(suffix), [
            first, upper,
          ])
        }
      } else {
        let (suffix, closing_span) = parse_rightsq(self)
        mixfix_expr_call(base, opening.span, closing_span, op_get(suffix), [
          first,
        ])
      }
    }
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_expr_dot_suffix(self : Parser, base : Expr) -> Expr raise {
  let pure_mark = self.mark()
  let pure = parse_alternative(
    self,
    parser => parser.parse_expr_pure_symbol(),
    parser => {
      let field = parser.parse_lqualid_rich()
      make_expr(
        Eidapp(field, [base]),
        base.span.join(parser.span_from(pure_mark)),
      )
    },
  )
  match pure.desc {
    Eidpur(_) => make_expr(Eapply(pure, base), base.span.join(pure.span))
    _ => pure
  }
}

///|
fn Parser::parse_expr_arg_result(self : Parser) -> ExprArgResult raise {
  let mut result = self.parse_expr_arg_atom()
  while true {
    if result.dot_eligible && self.consume_symbol(Dot) is Some(_) {
      result = {
        expression: self.parse_expr_dot_suffix(result.expression),
        dot_eligible: true,
      }
      continue
    }
    if self.at_symbol(LeftSq) {
      result = {
        expression: self.parse_expr_index(result.expression),
        dot_eligible: true,
      }
      continue
    }
    break
  }
  result
}

///|
fn Parser::parse_expr_arg(self : Parser) -> Expr raise {
  self.parse_expr_arg_result().expression
}

///|
fn Parser::parse_expr_application(self : Parser) -> (Expr, Bool) raise {
  let first = self.parse_expr_arg_result()
  let mut expression = first.expression
  let mut applied = false
  while starts_expr_arg(self) {
    let argument = self.parse_expr_arg()
    self.record_application_fold()
    expression = make_expr(
      Eapply(expression, argument),
      expression.span.join(argument.span),
    )
    applied = true
  }
  (expression, applied)
}

///|
fn break_expr_relation_chain(expression : Expr) -> Expr {
  match expression.desc {
    Einfix(left, operator, right) =>
      { ..expression, desc: Einnfix(left, operator, right) }
    _ => expression
  }
}

///|
fn Parser::parse_signed_expr_numeral(self : Parser) -> Expr raise {
  let mark = self.mark()
  ignore(self.expect_symbol(Minus))
  let token = self.peek()
  let constant = match token.kind {
    Integer(constant) => ConstInt(constant.negated())
    Real(constant) => ConstReal(constant.negated())
    _ => return self.fail_syntax("numeric literal")
  }
  ignore(self.advance())
  make_expr(Econst(constant), self.span_from(mark))
}

///|
fn Parser::parse_single_expr_prefix(self : Parser) -> Expr raise {
  let mark = self.mark()
  if starts_attribute(self) {
    let attribute = parse_attribute(self)
    let inner = self.parse_single_expr_bp(40)
    return make_expr(Eattr(attribute, inner), self.span_from(mark))
  }
  if self.consume_keyword(Not) is Some(_) {
    let inner = self.parse_single_expr_bp(negation_binding_power())
    return make_expr(Enot(inner), self.span_from(mark))
  }
  if self.at_symbol(Minus) && self.peek_kind_n(1) is Some(Integer(_) | Real(_)) {
    return self.parse_signed_expr_numeral()
  }
  if starts_prefix_operator(self) {
    let operator = self.parse_prefix_op()
    let operand = self.parse_single_expr_bp(ordinary_prefix_binding_power())
    return make_expr(Eidapp(Qident(operator), [operand]), self.span_from(mark))
  }
  if starts_control_expr(self) {
    return self.parse_control_expr()
  }
  let (expression, applied) = self.parse_expr_application()
  if applied {
    expression
  } else {
    break_expr_relation_chain(expression)
  }
}

///|
fn Parser::parse_single_expr_bp(
  self : Parser,
  minimum_binding : Int,
) -> Expr raise {
  let mut left = self.parse_single_expr_prefix()
  let mut last_nonassoc = -1
  while true {
    if self.at_symbol(Comma) ||
      self.at_symbol(LArrow) ||
      self.at_symbol(Semicolon) {
      break
    }
    let binding = if self.peek_kind_n(0) is Some(kind) {
      pratt_binding(kind, true)
    } else {
      None
    }
    guard binding is Some((power, associativity)) && power >= minimum_binding else {
      break
    }
    if associativity is PrattNonassoc && last_nonassoc == power {
      self.fail_syntax("non-associative operator")
    }
    if self.at_symbol(Colon) {
      let ty = self.parse_cast()
      left = make_expr(
        Ecast(left, ty),
        left.span.join(self.span_from(self.index - 1)),
      )
      last_nonassoc = power
      continue
    }
    let right_binding = if associativity is PrattRight {
      power
    } else {
      power + 1
    }
    if self.consume_symbol(AmpAmp) is Some(_) {
      let right = self.parse_single_expr_bp(right_binding)
      left = make_expr(Eand(left, right), left.span.join(right.span))
    } else if self.consume_symbol(BarBar) is Some(_) {
      let right = self.parse_single_expr_bp(right_binding)
      left = make_expr(Eor(left, right), left.span.join(right.span))
    } else if self.peek_kind_n(0)
      is Some(Op1(_) | Symbol(Equal | LtGt | Lt | Gt)) {
      let operator = self.parse_infix_op_1()
      let right = self.parse_single_expr_bp(right_binding)
      left = make_expr(
        Einfix(left, operator, right),
        left.span.join(right.span),
      )
    } else if self.peek_kind_n(0)
      is Some(Op2(_) | Op3(_) | Op4(_) | Symbol(Minus)) {
      let operator = self.parse_infix_op_234()
      let right = self.parse_single_expr_bp(right_binding)
      left = make_expr(
        Eidapp(Qident(operator), [left, right]),
        left.span.join(right.span),
      )
    } else {
      break
    }
    last_nonassoc = if associativity is PrattNonassoc { power } else { -1 }
  }
  left
}

///|
fn Parser::parse_single_expr(self : Parser) -> Expr raise {
  self.parse_single_expr_bp(0)
}

///|
fn Parser::parse_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let first = self.parse_single_expr()
  guard self.consume_symbol(Comma) is Some(_) else { return first }
  let elements : Array[Expr] = [first]
  guard starts_single_expr(self) else { self.fail_syntax("expression") }
  elements.push(self.parse_single_expr())
  while self.consume_symbol(Comma) is Some(_) {
    guard starts_single_expr(self) else { self.fail_syntax("expression") }
    elements.push(self.parse_single_expr())
  }
  make_expr(Etuple(elements), self.span_from(mark))
}

///|
fn Parser::parse_assign_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let left = self.parse_expr()
  guard self.consume_symbol(LArrow) is Some(_) else { return left }
  let right = self.parse_expr()
  make_expr(
    desugar_assignment(left, right, self.span_from(mark)),
    self.span_from(mark),
  )
}

///|
fn Parser::parse_contract_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let body = self.parse_assign_expr()
  guard starts_spec(self) else { return body }
  let first = self.parse_single_spec()
  let specification = spec_union(first, self.parse_spec())
  let span = self.span_from(mark)
  let function = make_expr(
    Efun([], None, make_pattern(Pwild, span), MaskVisible, specification, body),
    span,
  )
  make_expr(Eattr(Text(white_box_attribute), function), span)
}

///|
fn Parser::parse_seq_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let first = self.parse_contract_expr()
  guard self.consume_symbol(Semicolon) is Some(_) else { return first }
  guard starts_single_expr(self) else { return first }
  let rest = self.parse_seq_expr()
  make_expr(Esequence(first, rest), self.span_from(mark))
}

///|
fn Parser::parse_partiality(self : Parser) -> Partiality raise ParseError {
  let mark = self.mark()
  if self.consume_keyword(Ghost) is Some(_) {
    if self.consume_keyword(Partial) is Some(_) {
      return fail_with_diagnostic(
        make_parse_diagnostic(GhostPartialConflict, self.span_from(mark)),
      )
    }
    return GhostModifier
  }
  if self.consume_keyword(Partial) is Some(_) {
    if self.consume_keyword(Ghost) is Some(_) {
      return fail_with_diagnostic(
        make_parse_diagnostic(GhostPartialConflict, self.span_from(mark)),
      )
    }
    return PartialModifier
  }
  RegularModifier
}

///|
fn Parser::parse_routine_kind(self : Parser) -> RoutineKind raise ParseError {
  if self.consume_keyword(Function) is Some(_) ||
    self.consume_keyword(Constant) is Some(_) {
    RKfunc
  } else if self.consume_keyword(Predicate) is Some(_) {
    RKpred
  } else if self.consume_keyword(Lemma) is Some(_) {
    RKlemma
  } else {
    RKnone
  }
}

///|
fn Parser::parse_function_definition(self : Parser) -> Expr raise {
  let mark = self.mark()
  let binders = self.parse_binders()
  let (return_pattern, return_type, mask) = self.parse_return_opt()
  let before = self.parse_spec()
  let equal = self.expect_symbol(Equal)
  let after = self.parse_spec()
  let body = self.parse_seq_expr()
  let specification = apply_return(return_pattern, spec_union(before, after))
  let return_ident = Ident::{
    name: return_label,
    attributes: [],
    span: equal.span,
  }
  let wrapped_body = optional_exception(return_ident, mask, body)
  make_expr(
    Efun(
      binders, return_type, return_pattern, mask, specification, wrapped_body,
    ),
    self.span_from(mark),
  )
}

///|
fn Parser::parse_constant_definition(self : Parser) -> Expr raise {
  let return_type = if self.at_symbol(Colon) {
    Some(self.parse_cast())
  } else {
    None
  }
  ignore(self.expect_symbol(Equal))
  let body = self.parse_seq_expr()
  if return_type is Some(return_type) {
    { ..body, desc: Ecast(body, return_type) }
  } else {
    body
  }
}

///|
fn Parser::parse_function_declaration(self : Parser) -> Expr raise {
  let mark = self.mark()
  let params = self.parse_params(true)
  let (return_pattern, return_type, mask) = self.parse_return_opt()
  let specification = apply_return(return_pattern, self.parse_spec())
  make_expr(
    Eany(params, RKnone, return_type, return_pattern, mask, specification),
    self.span_from(mark),
  )
}

///|
fn Parser::parse_constant_declaration(self : Parser) -> Expr raise {
  let mark = self.mark()
  let (return_pattern, return_type, mask) = self.parse_return_opt()
  let specification = apply_return(return_pattern, self.parse_spec())
  make_expr(
    Eany([], RKnone, return_type, return_pattern, mask, specification),
    self.span_from(mark),
  )
}

///|
fn Parser::parse_rec_definition(self : Parser) -> FunctionDef raise {
  let partiality = self.parse_partiality()
  let kind = self.parse_routine_kind()
  let name = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let binders = self.parse_binders()
  let (return_pattern, return_type, mask) = self.parse_return_opt()
  let before = self.parse_spec()
  let equal = self.expect_symbol(Equal)
  let after = self.parse_spec()
  let body = self.parse_seq_expr()
  let specification = apply_partial_spec(
    partiality,
    apply_return(return_pattern, spec_union(before, after)),
  )
  let return_ident = Ident::{
    name: return_label,
    attributes: [],
    span: equal.span,
  }
  {
    name,
    ghost: partiality.is_ghost(),
    kind,
    binders,
    return_type,
    return_pattern,
    mask,
    spec: specification,
    body: optional_exception(return_ident, mask, body),
  }
}

///|
fn Parser::parse_let_rec_expr(self : Parser) -> ExprDesc raise {
  let definitions : Array[FunctionDef] = [self.parse_rec_definition()]
  while self.consume_keyword(With) is Some(_) {
    definitions.push(self.parse_rec_definition())
  }
  ignore(self.expect_keyword(In))
  Erec(definitions, self.parse_seq_expr())
}

///|
fn Parser::parse_pattern_let_expr(
  self : Parser,
  partiality : Partiality,
  kind : RoutineKind,
  kind_span : Span,
) -> ExprDesc raise {
  let pattern = self.parse_let_pattern()
  ignore(self.expect_symbol(Equal))
  let value = apply_partial_expr(partiality, self.parse_seq_expr())
  ignore(self.expect_keyword(In))
  let body = self.parse_seq_expr()
  let pattern = if partiality.is_ghost() {
    push_ghost_pattern(pattern)
  } else {
    pattern
  }
  simplify_expr_pattern_let(kind, value, pattern, body, kind_span)
}

///|
fn Parser::parse_named_let_expr(
  self : Parser,
  partiality : Partiality,
  kind : RoutineKind,
) -> ExprDesc raise {
  let name = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let value = if starts_binder_or_param(self) {
    self.parse_function_definition()
  } else {
    self.parse_constant_definition()
  }
  ignore(self.expect_keyword(In))
  let body = self.parse_seq_expr()
  Elet(
    name,
    partiality.is_ghost(),
    kind,
    apply_partial_expr(partiality, value),
    body,
  )
}

///|
fn Parser::parse_reference_let_expr(
  self : Parser,
  partiality : Partiality,
  reference_token : LocatedToken,
) -> ExprDesc raise {
  let name = self.parse_ref_binder()
  let value = self.parse_constant_definition()
  let reference = make_expr(Eref, reference_token.span)
  let allocated = { ..value, desc: Eapply(reference, value) }
  ignore(self.expect_keyword(In))
  Elet(
    name,
    partiality.is_ghost(),
    RKnone,
    apply_partial_expr(partiality, allocated),
    self.parse_seq_expr(),
  )
}

///|
fn Parser::parse_let_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Let)
  self.enter_nesting(opening.span)
  let result = try {
    let desc = if self.consume_keyword(Rec) is Some(_) {
      self.parse_let_rec_expr()
    } else {
      let partiality = self.parse_partiality()
      let kind_mark = self.mark()
      let kind = self.parse_routine_kind()
      let kind_span = self.span_from(kind_mark)
      if self.consume_keyword(Ref) is Some(reference_token) {
        self.parse_reference_let_expr(partiality, reference_token)
      } else {
        parse_alternative(
          self,
          parser => parser.parse_pattern_let_expr(partiality, kind, kind_span),
          parser => parser.parse_named_let_expr(partiality, kind),
        )
      }
    }
    make_expr(desc, self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_anonymous_function(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Fun)
  self.enter_nesting(opening.span)
  let result = try {
    let binders = self.parse_binders()
    let before = self.parse_spec()
    let arrow = self.expect_symbol(Arrow)
    let after = self.parse_spec()
    let body = self.parse_seq_expr()
    let return_ident = Ident::{
      name: return_label,
      attributes: [],
      span: arrow.span,
    }
    let span = self.span_from(mark)
    make_expr(
      Efun(
        binders,
        None,
        make_pattern(Pwild, span),
        MaskVisible,
        spec_union(before, after),
        optional_exception(return_ident, MaskVisible, body),
      ),
      span,
    )
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn restricted_any_spec(
  specification : Spec,
  span : Span,
) -> Unit raise ParseError {
  if !specification.writes.is_empty() ||
    !specification.exceptional_postconditions.is_empty() ||
    !specification.aliases.is_empty() ||
    specification.diverges ||
    specification.partial {
    fail_with_diagnostic(make_parse_diagnostic(RestrictedAnySpec, span))
  }
}

///|
fn Parser::parse_any_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Any)
  self.enter_nesting(opening.span)
  let result = try {
    let return_info = self.parse_return_named()
    let mut specification = apply_return(return_info.pattern, self.parse_spec())
    let span = self.span_from(mark)
    restricted_any_spec(specification, span)
    let witnesses = preconditions_of_any(
      span,
      return_info.return_type,
      specification.postconditions,
    )
    specification = {
      ..specification,
      preconditions: specification.preconditions + witnesses,
    }
    make_expr(
      Eany(
        [],
        RKnone,
        Some(return_info.return_type),
        make_pattern(Pwild, span),
        return_info.mask,
        specification,
      ),
      span,
    )
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_reference_val_expr(
  self : Parser,
  partiality : Partiality,
  reference_token : LocatedToken,
) -> ExprDesc raise {
  let name = self.parse_ref_binder()
  let value = self.parse_constant_declaration()
  let reference = make_expr(Eref, reference_token.span)
  let allocated = { ..value, desc: Eapply(reference, value) }
  ignore(self.expect_keyword(In))
  Elet(
    name,
    partiality.is_ghost(),
    RKnone,
    apply_partial_expr(partiality, allocated),
    self.parse_seq_expr(),
  )
}

///|
fn Parser::parse_val_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Val)
  self.enter_nesting(opening.span)
  let result = try {
    let partiality = self.parse_partiality()
    let kind = self.parse_routine_kind()
    let desc = if self.consume_keyword(Ref) is Some(reference_token) {
      self.parse_reference_val_expr(partiality, reference_token)
    } else {
      let (name, declaration) = if self.at_symbol(Amp) {
        let name = self.parse_sym_binder()
        (name, self.parse_constant_declaration())
      } else {
        let name = parse_attrs_ident(self, parser => parser.parse_lident_rich())
        let declaration = if starts_binder_or_param(self) &&
          !self.at_symbol(Colon) {
          self.parse_function_declaration()
        } else {
          self.parse_constant_declaration()
        }
        (name, declaration)
      }
      ignore(self.expect_keyword(In))
      Elet(
        name,
        partiality.is_ghost(),
        kind,
        apply_partial_expr(partiality, declaration),
        self.parse_seq_expr(),
      )
    }
    make_expr(desc, self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_regular_expr_branch(self : Parser) -> RegularBranch raise {
  let pattern = self.parse_pattern()
  ignore(self.expect_symbol(Arrow))
  { pattern, body: self.parse_seq_expr() }
}

///|
fn Parser::parse_exception_expr_branch(self : Parser) -> ExceptionBranch raise {
  let exception = self.parse_uqualid()
  let pattern = if starts_pat_arg(self) && !self.at_symbol(Arrow) {
    Some(self.parse_pat_arg())
  } else {
    None
  }
  ignore(self.expect_symbol(Arrow))
  { exception, pattern, body: self.parse_seq_expr() }
}

///|
fn Parser::parse_extended_match_cases(
  self : Parser,
) -> (Array[RegularBranch], Array[ExceptionBranch]) raise {
  ignore(self.consume_symbol(Bar))
  let regular : Array[RegularBranch] = []
  let exceptions : Array[ExceptionBranch] = []
  while true {
    if self.consume_keyword(Exception) is Some(_) {
      exceptions.push(self.parse_exception_expr_branch())
    } else {
      guard starts_pattern(self) else { self.fail_syntax("match case") }
      regular.push(self.parse_regular_expr_branch())
    }
    guard self.consume_symbol(Bar) is Some(_) else { break }
  }
  (regular, exceptions)
}

///|
fn Parser::parse_match_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Match)
  self.enter_nesting(opening.span)
  let result = try {
    let scrutinee = self.parse_seq_expr()
    let with_token = self.expect_keyword(With)
    let (regular, exceptions) = self.parse_extended_match_cases()
    ignore(self.expect_keyword(End))
    if regular.is_empty() {
      regular.push({
        pattern: make_pattern(Pwild, with_token.span),
        body: make_expr(Eabsurd, with_token.span),
      })
    }
    make_expr(Ematch(scrutinee, regular, exceptions), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_local_exception(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Exception)
  self.enter_nesting(opening.span)
  let result = try {
    let name = parse_attrs_ident(self, parser => parser.parse_uident(false))
    let (exception_type, mask) = if self.at_keyword(In) {
      (PTtuple([]), MaskVisible)
    } else {
      let info = self.parse_generic_return()
      (info.return_type, info.mask)
    }
    ignore(self.expect_keyword(In))
    let body = self.parse_seq_expr()
    make_expr(Eexn(name, exception_type, mask, body), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_loop_annotation(self : Parser) -> (Invariant, Variant) raise {
  let terms : Array[Term] = []
  let mut variant = Variant::{ items: [] }
  while self.at_keyword(Invariant) || self.at_keyword(Variant) {
    if self.at_keyword(Invariant) {
      terms.push(self.parse_loop_invariant())
    } else {
      variant = variant_union(variant, self.parse_variant_clause())
    }
  }
  ({ terms, }, variant)
}

///|
fn Parser::parse_loop_body(self : Parser) -> Expr raise {
  if self.at_keyword(Done) {
    make_expr(Etuple([]), self.empty_span_at_cursor())
  } else {
    self.parse_seq_expr()
  }
}

///|
fn Parser::parse_while_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(While)
  self.enter_nesting(opening.span)
  let result = try {
    let condition = self.parse_seq_expr()
    let do_token = self.expect_keyword(Do)
    let (invariant, variant) = self.parse_loop_annotation()
    let body = self.parse_loop_body()
    ignore(self.expect_keyword(Done))
    let span = self.span_from(mark)
    let continue_ident = Ident::{
      name: continue_label,
      attributes: [],
      span: do_token.span,
    }
    let break_ident = Ident::{
      name: break_label,
      attributes: [],
      span: do_token.span,
    }
    let loop_expression = make_expr(
      Ewhile(
        condition,
        invariant,
        variant,
        optional_exception(continue_ident, MaskVisible, body),
      ),
      span,
    )
    make_expr(Eoptexn(break_ident, MaskVisible, loop_expression), span)
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
priv enum ForHead {
  CountedForHead(Ident)
  IteratorForHead(Pattern)
}

///|
fn Parser::parse_counted_for_head(self : Parser) -> ForHead raise {
  let ident = self.parse_var_binder_ident()
  ignore(self.expect_symbol(Equal))
  CountedForHead(ident)
}

///|
fn Parser::parse_iterator_for_head(self : Parser) -> ForHead raise {
  let pattern = self.parse_pattern()
  ignore(self.expect_keyword(In))
  IteratorForHead(pattern)
}

///|
fn Parser::parse_counted_for_tail(
  self : Parser,
  mark : Int,
  ident : Ident,
) -> Expr raise {
  let from = self.parse_seq_expr()
  let direction = if self.consume_keyword(To) is Some(_) {
    ForDirection::To
  } else {
    ignore(self.expect_keyword(Downto))
    DownTo
  }
  let to = self.parse_seq_expr()
  let do_token = self.expect_keyword(Do)
  let invariant_terms : Array[Term] = []
  while self.at_keyword(Invariant) {
    invariant_terms.push(self.parse_loop_invariant())
  }
  let body = self.parse_loop_body()
  ignore(self.expect_keyword(Done))
  let span = self.span_from(mark)
  let continue_ident = Ident::{
    name: continue_label,
    attributes: [],
    span: do_token.span,
  }
  let break_ident = Ident::{
    name: break_label,
    attributes: [],
    span: do_token.span,
  }
  let loop_expression = make_expr(
    Efor(
      ident,
      from,
      direction,
      to,
      { terms: invariant_terms },
      optional_exception(continue_ident, MaskVisible, body),
    ),
    span,
  )
  make_expr(Eoptexn(break_ident, MaskVisible, loop_expression), span)
}

///|
fn iterator_qualid(path : QualId, name : Bytes) -> QualId {
  Qdot(path, { name, attributes: [], span: path.full_span() })
}

///|
fn Parser::parse_iterator_for_tail(
  self : Parser,
  mark : Int,
  pattern : Pattern,
) -> Expr raise {
  let collection = self.parse_seq_expr()
  ignore(self.expect_keyword(With))
  let iterator_module = self.parse_uqualid()
  let iterator = if self.consume_keyword(As) is Some(_) {
    self.parse_lident(false, true)
  } else {
    { name: b"it", attributes: [], span: self.empty_span_at_cursor() }
  }
  let do_token = self.expect_keyword(Do)
  let (invariant, variant) = self.parse_loop_annotation()
  let body = self.parse_loop_body()
  ignore(self.expect_keyword(Done))
  let span = self.span_from(mark)
  let synth = (desc : ExprDesc) => make_expr(desc, span)
  let next = synth(
    Eidapp(iterator_qualid(iterator_module, b"next"), [
      synth(Eident(Qident(iterator))),
    ]),
  )
  let let_body = synth(
    simplify_expr_pattern_let(RKnone, next, pattern, body, span),
  )
  let continue_ident = Ident::{
    name: continue_label,
    attributes: [],
    span: do_token.span,
  }
  let break_ident = Ident::{
    name: break_label,
    attributes: [],
    span: do_token.span,
  }
  let while_body = optional_exception(continue_ident, MaskVisible, let_body)
  let while_expression = synth(
    Ewhile(synth(Etrue), invariant, variant, while_body),
  )
  let caught_break = synth(Eoptexn(break_ident, MaskVisible, while_expression))
  let done_case = ExceptionBranch::{
    exception: iterator_qualid(iterator_module, b"Done"),
    pattern: None,
    body: make_expr(Etuple([]), body.span),
  }
  let matched = synth(Ematch(caught_break, [], [done_case]))
  let create = synth(
    Eidapp(iterator_qualid(iterator_module, b"create"), [collection]),
  )
  synth(Elet(iterator, false, RKnone, create, matched))
}

///|
fn Parser::parse_for_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(For)
  self.enter_nesting(opening.span)
  let result = try {
    let head = parse_alternative(
      self,
      parser => parser.parse_counted_for_head(),
      parser => parser.parse_iterator_for_head(),
    )
    match head {
      CountedForHead(ident) => self.parse_counted_for_tail(mark, ident)
      IteratorForHead(pattern) => self.parse_iterator_for_tail(mark, pattern)
    }
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_if_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(If)
  self.enter_nesting(opening.span)
  let result = try {
    let condition = self.parse_seq_expr()
    ignore(self.expect_keyword(Then))
    let consequent = self.parse_contract_expr()
    let alternative = if self.consume_keyword(Else) is Some(_) {
      self.parse_contract_expr()
    } else {
      make_expr(Etuple([]), self.span_from(mark))
    }
    make_expr(Eif(condition, consequent, alternative), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_raise_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  ignore(self.expect_keyword(Raise))
  let (exception, argument) = if self.consume_symbol(LeftPar) is Some(opening) {
    self.enter_nesting(opening.span)
    let pair = try {
      let exception = self.parse_uqualid()
      let argument = if starts_expr_arg(self) {
        Some(self.parse_expr_arg())
      } else {
        None
      }
      ignore(self.expect_symbol(RightPar))
      (exception, argument)
    } catch {
      error => {
        self.leave_nesting()
        raise error
      }
    }
    self.leave_nesting()
    pair
  } else {
    let exception = self.parse_uqualid()
    let argument = if starts_expr_arg(self) {
      Some(self.parse_expr_arg())
    } else {
      None
    }
    (exception, argument)
  }
  make_expr(Eraise(exception, argument), self.span_from(mark))
}

///|
fn Parser::parse_return_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let token = self.expect_keyword(Return)
  // Menhir gives RETURN higher precedence than declaration-shaped LET, VAL,
  // and EXCEPTION. In those conflicts the optional return value is empty.
  let value = if self.at_keyword(Let) ||
    self.at_keyword(Val) ||
    self.at_keyword(Exception) {
    None
  } else if starts_single_expr(self) {
    Some(self.parse_contract_expr())
  } else {
    None
  }
  let ident = Ident::{ name: return_label, attributes: [], span: token.span }
  make_expr(Eraise(Qident(ident), value), self.span_from(mark))
}

///|
fn Parser::parse_loop_jump_expr(
  self : Parser,
  keyword : Keyword,
  suffix : Bytes,
) -> Expr raise {
  let mark = self.mark()
  let token = self.expect_keyword(keyword)
  let ident = if starts_uident_kind(self.peek_kind_n(0)) {
    append_control_suffix(self.parse_uident(false), suffix)
  } else {
    { name: suffix, attributes: [], span: token.span }
  }
  make_expr(Eraise(Qident(ident), None), self.span_from(mark))
}

///|
fn Parser::parse_try_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Try)
  self.enter_nesting(opening.span)
  let result = try {
    let body = self.parse_seq_expr()
    ignore(self.expect_keyword(With))
    ignore(self.consume_symbol(Bar))
    let handlers : Array[ExceptionBranch] = [self.parse_exception_expr_branch()]
    while self.consume_symbol(Bar) is Some(_) {
      handlers.push(self.parse_exception_expr_branch())
    }
    ignore(self.expect_keyword(End))
    make_expr(Ematch(body, [], handlers), self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_assertion_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let token = self.advance()
  let (fallback, kind) = match token.kind {
    Keyword(Assert) => (b"Assert", AssertionKind::Assert)
    Keyword(Assume) => (b"Assume", Assume)
    Keyword(Check) => (b"Check", Check)
    _ => return self.fail_syntax("assertion")
  }
  let name = if self.at_symbol(LeftBrc) {
    None
  } else {
    Some(self.parse_ident_nq())
  }
  let term = self.parse_spec_term_block()
  make_expr(
    Eassert(kind, named_term(name, fallback, term)),
    self.span_from(mark),
  )
}

///|
fn Parser::parse_label_expr(self : Parser) -> Expr raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Label)
  self.enter_nesting(opening.span)
  let result = try {
    let label = parse_attrs_ident(self, parser => parser.parse_uident(false))
    ignore(self.expect_keyword(In))
    let body = self.parse_seq_expr()
    { ..label_over_loop(label, body), span: self.span_from(mark) }
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_control_expr(self : Parser) -> Expr raise {
  if self.at_keyword(If) {
    return self.parse_if_expr()
  }
  if self.at_keyword(Let) {
    return self.parse_let_expr()
  }
  if self.at_keyword(Fun) {
    return self.parse_anonymous_function()
  }
  if self.at_keyword(Any) {
    return self.parse_any_expr()
  }
  if self.at_keyword(Val) {
    return self.parse_val_expr()
  }
  if self.at_keyword(Match) {
    return self.parse_match_expr()
  }
  if self.at_keyword(Exception) {
    return self.parse_local_exception()
  }
  if self.at_keyword(Label) {
    return self.parse_label_expr()
  }
  if self.at_keyword(While) {
    return self.parse_while_expr()
  }
  if self.at_keyword(For) {
    return self.parse_for_expr()
  }
  if self.consume_keyword(Absurd) is Some(token) {
    return make_expr(Eabsurd, token.span)
  }
  if self.at_keyword(Raise) {
    return self.parse_raise_expr()
  }
  if self.at_keyword(Return) {
    return self.parse_return_expr()
  }
  if self.at_keyword(Break) {
    return self.parse_loop_jump_expr(Break, break_label)
  }
  if self.at_keyword(Continue) {
    return self.parse_loop_jump_expr(Continue, continue_label)
  }
  if self.at_keyword(Try) {
    return self.parse_try_expr()
  }
  if self.consume_keyword(Ghost) is Some(token) {
    let inner = self.parse_single_expr()
    return make_expr(Eghost(inner), token.span.join(inner.span))
  }
  if starts_assertion(self) {
    return self.parse_assertion_expr()
  }
  self.fail_syntax("program expression")
}

///|
fn parse_expr_entry(
  input : BytesView,
  filename? : BytesView = b"<expr-test>",
) -> Expr raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_seq_expr())
}

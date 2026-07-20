// Pratt term parser and term grammar productions.

///|
fn make_term(desc : TermDesc, span : Span) -> Term {
  { desc, span }
}

///|
fn QualId::last_ident(self : QualId) -> Ident {
  match self {
    Qident(ident) => ident
    Qdot(_, ident) => ident
  }
}

///|
fn qualid_can_start_term_dot(path : QualId) -> Bool {
  let ident = path.last_ident()
  !ident.name.is_empty() &&
  is_ascii_lower(ident.name[0]) &&
  notation_decode(ident.name) is SNword(_)
}

///|
fn starts_term_block(parser : Parser) -> Bool {
  parser.at_symbol(LeftPar) ||
  parser.at_symbol(LeftBrc) ||
  parser.at_keyword(Begin)
}

///|
fn starts_term_arg(parser : Parser) -> Bool {
  starts_ident(parser) ||
  parser.at_symbol(Amp) ||
  parser.peek_kind_n(0)
  is Some(Integer(_) | Real(_) | StringToken(_) | OpPref(_)) ||
  parser.at_keyword(True) ||
  parser.at_keyword(False) ||
  parser.at_keyword(Begin) ||
  parser.at_symbol(LeftBrc) ||
  parser.at_symbol(LeftSqBar)
}

///|
fn starts_prefix_operator(parser : Parser) -> Bool {
  parser.peek_kind_n(0)
  is Some(Op1(_) | Op2(_) | Op3(_) | Op4(_) | Symbol(Lt | Gt | Minus))
}

///|
fn starts_single_term(parser : Parser) -> Bool {
  starts_term_arg(parser) ||
  starts_attribute(parser) ||
  starts_prefix_operator(parser) ||
  parser.at_keyword(Not) ||
  parser.at_keyword(Old) ||
  parser.at_keyword(If) ||
  parser.at_keyword(Let) ||
  parser.at_keyword(Match) ||
  parser.at_keyword(Forall) ||
  parser.at_keyword(Exists) ||
  parser.at_keyword(Fun) ||
  parser.at_keyword(Epsilon)
}

///|
fn Parser::parse_term_field(self : Parser) -> (QualId, Term) raise {
  let field = self.parse_lqualid()
  ignore(self.expect_symbol(Equal))
  (field, self.parse_term())
}

///|
fn starts_term_field(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true)
}

///|
fn Parser::parse_term_record_desc(self : Parser) -> TermDesc raise {
  Trecord(
    parse_semicolon_list1(
      self,
      parser => starts_term_field(parser),
      parser => parser.parse_term_field(),
      expected="record field",
    ),
  )
}

///|
fn Parser::parse_term_update_desc(self : Parser) -> TermDesc raise {
  let base = self.parse_term_arg()
  ignore(self.expect_keyword(With))
  let fields = parse_semicolon_list1(
    self,
    parser => starts_term_field(parser),
    parser => parser.parse_term_field(),
    expected="record update field",
  )
  Tupdate(base, fields)
}

///|
fn Parser::parse_term_block(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.peek()
  guard starts_term_block(self) else { self.fail_syntax("term block") }
  ignore(self.advance())
  self.enter_nesting(opening.span)
  let term = try {
    let desc = if opening.kind is Keyword(Begin) {
      if self.consume_keyword(End) is Some(_) {
        Ttuple([])
      } else {
        let inner = self.parse_term()
        ignore(self.expect_keyword(End))
        inner.desc
      }
    } else if opening.kind is Symbol(LeftPar) {
      if self.consume_symbol(RightPar) is Some(_) {
        Ttuple([])
      } else {
        let inner = self.parse_term()
        ignore(self.expect_symbol(RightPar))
        inner.desc
      }
    } else {
      let desc = parse_alternative(
        self,
        // `{ term_arg with ... }` conflicts locally with a field whose name
        // starts like a term argument. Only the token index is restored.
        parser => parser.parse_term_update_desc(),
        parser => parser.parse_term_record_desc(),
      )
      ignore(self.expect_symbol(RightBrc))
      desc
    }
    make_term(desc, self.span_from(mark))
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  term
}

///|
fn Parser::parse_scoped_term_block(self : Parser) -> Term raise {
  let mark = self.mark()
  let path = self.parse_uqualid()
  ignore(self.expect_symbol(Dot))
  guard starts_term_block(self) else { self.fail_syntax("term block") }
  let block = self.parse_term_block()
  make_term(Tscope(path, block), self.span_from(mark))
}

///|
fn Parser::parse_term_qualid(self : Parser) -> (Term, Bool) raise {
  let mark = self.mark()
  let path = self.parse_qualid()
  (
    make_term(Tident(path), self.span_from(mark)),
    qualid_can_start_term_dot(path),
  )
}

///|
fn Parser::parse_term_fun_literal(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.expect_symbol(LeftSqBar)
  self.enter_nesting(opening.span)
  let result = try {
    let (mappings, default) = parse_alternative(
      self,
      parser => {
        parse_mapping_list_with_default(
          parser,
          parser => starts_single_term(parser),
          parser => parser.parse_term(),
          expected="function literal mapping",
        )
      },
      parser => {
        let values = parse_semicolon_list1(
          parser,
          parser => starts_single_term(parser),
          parser => parser.parse_term(),
          expected="function literal value",
        )
        (indexed_term_values(values), None)
      },
    )
    let closing = self.expect_symbol(BarRightSq)
    desugar_term_function_literal(opening.span, closing.span, mappings, default)
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  ignore(mark)
  result
}

///|
priv struct TermArgResult {
  term : Term
  dot_eligible : Bool
}

///|
fn Parser::parse_term_arg_atom(self : Parser) -> TermArgResult raise {
  let mark = self.mark()
  let token = self.peek()
  match token.kind {
    Integer(constant) => {
      ignore(self.advance())
      {
        term: make_term(Tconst(ConstInt(constant)), token.span),
        dot_eligible: false,
      }
    }
    Real(constant) => {
      ignore(self.advance())
      {
        term: make_term(Tconst(ConstReal(constant)), token.span),
        dot_eligible: false,
      }
    }
    StringToken(bytes) => {
      ignore(self.advance())
      {
        term: make_term(Tconst(ConstStr(bytes)), token.span),
        dot_eligible: false,
      }
    }
    Keyword(True) => {
      ignore(self.advance())
      { term: make_term(Ttrue, token.span), dot_eligible: false }
    }
    Keyword(False) => {
      ignore(self.advance())
      { term: make_term(Tfalse, token.span), dot_eligible: false }
    }
    OpPref(_) => {
      let operator = self.parse_oppref()
      let argument = self.parse_term_arg_atom()
      {
        term: make_term(
          Tidapp(Qident(operator), [argument.term]),
          self.span_from(mark),
        ),
        dot_eligible: argument.dot_eligible,
      }
    }
    Symbol(Amp) => {
      ignore(self.advance())
      let path = self.parse_qualid()
      {
        term: make_term(Tasref(path), self.span_from(mark)),
        dot_eligible: false,
      }
    }
    Symbol(LeftSqBar) =>
      { term: self.parse_term_fun_literal(), dot_eligible: false }
    Symbol(LeftPar) => {
      let (term, dot_eligible) = parse_alternative(
        self,
        // A parenthesized symbolic identifier and a parenthesized term share
        // the same opening token.
        parser => parser.parse_term_qualid(),
        parser => (parser.parse_term_block(), true),
      )
      { term, dot_eligible }
    }
    Keyword(Begin) | Symbol(LeftBrc) =>
      { term: self.parse_term_block(), dot_eligible: true }
    Uident(_) | CoreUident(_) => {
      let (term, dot_eligible) = parse_alternative(
        self,
        // `M.(...)`/`M.{...}` conflicts with a qualified identifier prefix.
        parser => (parser.parse_scoped_term_block(), true),
        parser => parser.parse_term_qualid(),
      )
      { term, dot_eligible }
    }
    _ => {
      let (term, dot_eligible) = self.parse_term_qualid()
      { term, dot_eligible }
    }
  }
}

///|
fn mixfix_term_call(
  base : Term,
  opening_span : Span,
  closing_span : Span,
  name : Bytes,
  arguments : Array[Term],
) -> Term {
  let operator = Ident::{ name, attributes: [], span: opening_span }
  make_term(
    Tidapp(Qident(operator), [base] + arguments),
    base.span.join(closing_span),
  )
}

///|
fn Parser::parse_term_index(self : Parser, base : Term) -> Term raise {
  let opening = self.expect_symbol(LeftSq)
  self.enter_nesting(opening.span)
  let result = try {
    if self.consume_symbol(DotDot) is Some(_) {
      let upper = self.parse_term()
      let (suffix, closing_span) = parse_rightsq(self)
      mixfix_term_call(base, opening.span, closing_span, op_lcut(suffix), [
        upper,
      ])
    } else {
      let first = self.parse_term()
      if self.consume_symbol(LArrow) is Some(_) {
        let value = self.parse_term()
        let (suffix, closing_span) = parse_rightsq(self)
        mixfix_term_call(base, opening.span, closing_span, op_update(suffix), [
          first, value,
        ])
      } else if self.consume_symbol(DotDot) is Some(_) {
        if self.peek_kind_n(0) is Some(Symbol(RightSq) | RightSqQuote(_)) {
          let (suffix, closing_span) = parse_rightsq(self)
          mixfix_term_call(base, opening.span, closing_span, op_rcut(suffix), [
            first,
          ])
        } else {
          let upper = self.parse_term()
          let (suffix, closing_span) = parse_rightsq(self)
          mixfix_term_call(base, opening.span, closing_span, op_cut(suffix), [
            first, upper,
          ])
        }
      } else {
        let (suffix, closing_span) = parse_rightsq(self)
        mixfix_term_call(base, opening.span, closing_span, op_get(suffix), [
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
fn Parser::parse_term_arg_result(self : Parser) -> TermArgResult raise {
  let mut result = self.parse_term_arg_atom()
  while true {
    if result.dot_eligible && self.consume_symbol(Dot) is Some(_) {
      let field_mark = self.mark()
      let field = self.parse_lqualid_rich()
      result = {
        term: make_term(
          Tidapp(field, [result.term]),
          result.term.span.join(self.span_from(field_mark)),
        ),
        dot_eligible: true,
      }
      continue
    }
    if self.at_symbol(LeftSq) {
      result = { term: self.parse_term_index(result.term), dot_eligible: true }
      continue
    }
    break
  }
  result
}

///|
fn Parser::parse_term_arg(self : Parser) -> Term raise {
  self.parse_term_arg_result().term
}

///|
fn Parser::parse_term_application(self : Parser) -> (Term, Bool) raise {
  let first = self.parse_term_arg_result()
  let mut term = first.term
  let mut applied = false
  while starts_term_arg(self) {
    let argument = self.parse_term_arg()
    term = make_term(Tapply(term, argument), term.span.join(argument.span))
    applied = true
  }
  (term, applied)
}

///|
fn break_term_relation_chain(term : Term) -> Term {
  match term.desc {
    Tinfix(left, operator, right) =>
      { ..term, desc: Tinnfix(left, operator, right) }
    Tbinop(left, operator, right) =>
      { ..term, desc: Tbinnop(left, operator, right) }
    _ => term
  }
}

///|
fn Parser::parse_signed_term_numeral(self : Parser) -> Term raise {
  let mark = self.mark()
  ignore(self.expect_symbol(Minus))
  ignore(signed_numeral_binding_power())
  let token = self.peek()
  let constant = match token.kind {
    Integer(constant) => ConstInt(constant.negated())
    Real(constant) => ConstReal(constant.negated())
    _ => return self.fail_syntax("numeric literal")
  }
  ignore(self.advance())
  make_term(Tconst(constant), self.span_from(mark))
}

///|
fn Parser::parse_if_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.expect_keyword(If)
  self.enter_nesting(opening.span)
  let result = try {
    let condition = self.parse_term()
    ignore(self.expect_keyword(Then))
    let consequent = self.parse_term()
    ignore(self.expect_keyword(Else))
    let alternative = self.parse_term()
    make_term(Tif(condition, consequent, alternative), self.span_from(mark))
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
priv enum TermLetHead {
  PatternLetHead(Pattern)
  NamedLetHead(Ident, Array[Binder], Span?)
}

///|
fn Parser::parse_pattern_let_head(self : Parser) -> TermLetHead raise {
  let pattern = self.parse_pattern()
  ignore(self.expect_symbol(Equal))
  PatternLetHead(pattern)
}

///|
fn Parser::parse_named_let_head(self : Parser) -> TermLetHead raise {
  let ident = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let binder_start = if starts_binder_or_param(self) {
    Some(self.peek().span)
  } else {
    None
  }
  let binders = if binder_start is Some(_) { self.parse_binders() } else { [] }
  ignore(self.expect_symbol(Equal))
  NamedLetHead(ident, binders, binder_start)
}

///|
fn Parser::parse_let_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Let)
  self.enter_nesting(opening.span)
  let result = try {
    let head = parse_alternative(
      self,
      // `let f = ...` is a pattern let, while `let f x = ...` and symbolic
      // names use the logic-function production. The choice commits at `=`.
      parser => parser.parse_pattern_let_head(),
      parser => parser.parse_named_let_head(),
    )
    let value = self.parse_term()
    ignore(self.expect_keyword(In))
    let body = self.parse_term()
    let desc = match head {
      PatternLetHead(pattern) => unfold_term_pattern_let(pattern, value, body)
      NamedLetHead(ident, binders, binder_start) => {
        let bound_value = if binder_start is Some(start) {
          make_term(
            Tquant(DTlambda, binders, [], value),
            start.join(value.span),
          )
        } else {
          value
        }
        Tlet(ident, bound_value, body)
      }
    }
    make_term(desc, self.span_from(mark))
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
fn Parser::parse_term_match_case(self : Parser) -> (Pattern, Term) raise {
  let pattern = self.parse_pattern()
  ignore(self.expect_symbol(Arrow))
  (pattern, self.parse_term())
}

///|
fn Parser::parse_match_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Match)
  self.enter_nesting(opening.span)
  let result = try {
    let scrutinee = self.parse_term()
    ignore(self.expect_keyword(With))
    let cases = parse_bar_list1(
      self,
      parser => starts_pattern(parser),
      parser => parser.parse_term_match_case(),
      expected="match case",
    )
    ignore(self.expect_keyword(End))
    make_term(Tcase(scrutinee, cases), self.span_from(mark))
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
fn Parser::parse_quant_var_group(self : Parser) -> Array[Binder] raise {
  guard starts_binder_slot(self) else {
    self.fail_syntax("quantified variable")
  }
  let slots : Array[BinderSlot] = []
  while starts_binder_slot(self) {
    slots.push(self.parse_binder_slot())
  }
  let binder_type = if self.at_symbol(Colon) {
    Some(self.parse_cast())
  } else {
    None
  }
  let binders : Array[Binder] = []
  for slot in slots {
    binders.push(make_binder(slot.span, slot.ident, false, binder_type))
  }
  binders
}

///|
fn Parser::parse_quant_vars(self : Parser) -> Array[Binder] raise {
  let binders = self.parse_quant_var_group()
  while self.consume_symbol(Comma) is Some(_) {
    binders.push_iter(self.parse_quant_var_group().iter())
  }
  binders
}

///|
fn Parser::parse_trigger_group(self : Parser) -> Array[Term] raise {
  parse_comma_list1(
    self,
    parser => starts_single_term(parser),
    parser => parser.parse_single_term(),
    expected="trigger term",
  )
}

///|
fn Parser::parse_triggers(self : Parser) -> Array[Array[Term]] raise {
  guard self.consume_symbol(LeftSq) is Some(opening) else { return [] }
  self.enter_nesting(opening.span)
  let result = try {
    // Unlike bar_list1, trigger groups reject a leading `|` and an empty list.
    guard starts_single_term(self) else { self.fail_syntax("trigger term") }
    let groups : Array[Array[Term]] = [self.parse_trigger_group()]
    while self.consume_symbol(Bar) is Some(_) {
      guard starts_single_term(self) else { self.fail_syntax("trigger term") }
      groups.push(self.parse_trigger_group())
    }
    ignore(self.expect_symbol(RightSq))
    groups
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
fn Parser::parse_quantified_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.advance()
  let quantifier = match opening.kind {
    Keyword(Forall) => DTforall
    Keyword(Exists) => DTexists
    _ => return self.fail_syntax("quantifier")
  }
  self.enter_nesting(opening.span)
  let result = try {
    let binders = self.parse_quant_vars()
    let triggers = self.parse_triggers()
    ignore(self.expect_symbol(Dot))
    let body = self.parse_term()
    make_term(Tquant(quantifier, binders, triggers, body), self.span_from(mark))
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
fn Parser::parse_lambda_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let opening = self.expect_keyword(Fun)
  self.enter_nesting(opening.span)
  let result = try {
    let binders = self.parse_binders()
    ignore(self.expect_symbol(Arrow))
    let body = self.parse_term()
    make_term(Tquant(DTlambda, binders, [], body), self.span_from(mark))
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
fn Parser::parse_term_prefix(self : Parser) -> Term raise {
  let mark = self.mark()
  if starts_attribute(self) {
    let attribute = parse_attribute(self)
    let colon_binding = match pratt_binding(Symbol(Colon), false) {
      Some((binding, _)) => binding
      None => abort("term cast must have a Pratt binding")
    }
    let inner = self.parse_single_term_bp(colon_binding)
    return make_term(Tattr(attribute, inner), self.span_from(mark))
  }
  if self.consume_keyword(Not) is Some(_) {
    let inner = self.parse_single_term_bp(negation_binding_power())
    return make_term(Tnot(inner), self.span_from(mark))
  }
  if self.consume_keyword(Old) is Some(keyword) {
    let binding = match pratt_binding(Keyword(Old), false) {
      Some((binding, _)) => binding
      None => abort("old must have a Pratt binding")
    }
    let inner = self.parse_single_term_bp(binding + 1)
    if self.at_keyword(At) {
      self.fail_syntax("parentheses around an `old` term before `at`")
    }
    let label = Ident::{ name: old_label, attributes: [], span: keyword.span }
    return make_term(Tat(inner, label), self.span_from(mark))
  }
  if self.at_symbol(Minus) && self.peek_kind_n(1) is Some(Integer(_) | Real(_)) {
    return self.parse_signed_term_numeral()
  }
  if starts_prefix_operator(self) {
    let operator = self.parse_prefix_op()
    let operand = self.parse_single_term_bp(ordinary_prefix_binding_power())
    return make_term(Tidapp(Qident(operator), [operand]), self.span_from(mark))
  }
  if self.at_keyword(If) {
    return self.parse_if_term()
  }
  if self.at_keyword(Let) {
    return self.parse_let_term()
  }
  if self.at_keyword(Match) {
    return self.parse_match_term()
  }
  if self.at_keyword(Forall) || self.at_keyword(Exists) {
    return self.parse_quantified_term()
  }
  if self.at_keyword(Fun) {
    return self.parse_lambda_term()
  }
  if self.consume_keyword(Epsilon) is Some(token) {
    return fail_with_diagnostic(
      make_parse_diagnostic(UnsupportedEpsilon, token.span, actual=token.actual),
    )
  }
  let (term, applied) = self.parse_term_application()
  ignore(postfix_binding_power())
  ignore(tight_prefix_binding_power())
  if applied {
    term
  } else {
    break_term_relation_chain(term)
  }
}

///|
fn Parser::parse_term_logic_operator(self : Parser) -> BinaryLogicOp raise {
  let token = self.advance()
  match token.kind {
    Symbol(Arrow) => DTimplies
    Symbol(LRArrow) => DTiff
    Symbol(Or) => DTor
    Symbol(BarBar) => DTorAsym
    Symbol(And) => DTand
    Symbol(AmpAmp) => DTandAsym
    Keyword(By) => DTby
    Keyword(So) => DTso
    _ => self.fail_syntax("logical operator")
  }
}

///|
fn Parser::parse_single_term_bp(
  self : Parser,
  minimum_binding : Int,
) -> Term raise {
  let mut left = self.parse_term_prefix()
  let mut last_nonassoc = -1
  while true {
    if self.at_symbol(Comma) {
      break
    }
    let binding = if self.peek_kind_n(0) is Some(kind) {
      pratt_binding(kind, false)
    } else {
      None
    }
    guard binding is Some((power, associativity)) && power >= minimum_binding else {
      break
    }
    if self.at_keyword(Old) {
      break
    }
    if associativity is PrattNonassoc && last_nonassoc == power {
      self.fail_syntax("non-associative operator")
    }
    if self.at_symbol(Colon) {
      let ty = self.parse_cast()
      left = make_term(
        Tcast(left, ty),
        left.span.join(self.span_from(self.index - 1)),
      )
      last_nonassoc = power
      continue
    }
    if self.consume_keyword(At) is Some(_) {
      let label = self.parse_uident(false)
      left = make_term(Tat(left, label), left.span.join(label.span))
      last_nonassoc = power
      continue
    }
    let right_binding = if associativity is PrattRight {
      power
    } else {
      power + 1
    }
    if self.at_symbol(Arrow) ||
      self.at_symbol(LRArrow) ||
      self.at_symbol(Or) ||
      self.at_symbol(BarBar) ||
      self.at_symbol(And) ||
      self.at_symbol(AmpAmp) ||
      self.at_keyword(By) ||
      self.at_keyword(So) {
      let operator = self.parse_term_logic_operator()
      let right = self.parse_single_term_bp(right_binding)
      left = make_term(
        Tbinop(left, operator, right),
        left.span.join(right.span),
      )
    } else if self.peek_kind_n(0)
      is Some(Op1(_) | Symbol(Equal | LtGt | Lt | Gt)) {
      let operator = self.parse_infix_op_1()
      let right = self.parse_single_term_bp(right_binding)
      left = make_term(
        Tinfix(left, operator, right),
        left.span.join(right.span),
      )
    } else if self.peek_kind_n(0)
      is Some(Op2(_) | Op3(_) | Op4(_) | Symbol(Minus)) {
      let operator = self.parse_infix_op_234()
      let right = self.parse_single_term_bp(right_binding)
      left = make_term(
        Tidapp(Qident(operator), [left, right]),
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
fn Parser::parse_single_term(self : Parser) -> Term raise {
  self.parse_single_term_bp(0)
}

///|
fn Parser::parse_term(self : Parser) -> Term raise {
  let mark = self.mark()
  let first = self.parse_single_term()
  guard self.consume_symbol(Comma) is Some(_) else { return first }
  let elements : Array[Term] = [first]
  guard starts_single_term(self) else { self.fail_syntax("term") }
  elements.push(self.parse_single_term())
  while self.consume_symbol(Comma) is Some(_) {
    guard starts_single_term(self) else { self.fail_syntax("term") }
    elements.push(self.parse_single_term())
  }
  make_term(Ttuple(elements), self.span_from(mark))
}

///|
fn parse_term_entry(
  input : BytesView,
  filename? : BytesView = b"<term-test>",
) -> Term raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_term())
}

///|
fn parse_term_list_entry(
  input : BytesView,
  filename? : BytesView = b"<term-list-test>",
) -> Array[Term] raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => {
    parse_comma_list1(
      parser,
      parser => starts_single_term(parser),
      parser => parser.parse_single_term(),
      expected="term",
    )
  })
}

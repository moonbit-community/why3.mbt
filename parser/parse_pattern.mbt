// WhyML pattern and let-pattern grammar productions.

///|
fn make_pattern(desc : PatternDesc, span : Span) -> Pattern {
  { desc, span }
}

///|
fn starts_pat_arg(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), false) ||
  parser.at_symbol(Underscore) ||
  parser.at_symbol(Amp) ||
  parser.at_symbol(LeftPar) ||
  parser.at_symbol(LeftBrc)
}

///|
fn starts_pattern(parser : Parser) -> Bool {
  starts_pat_arg(parser) || parser.at_keyword(Ghost)
}

///|
fn Parser::parse_pattern_var(self : Parser) -> Pattern raise {
  let mark = self.mark()
  let ident = self.parse_var_binder_ident()
  make_pattern(Pvar(ident), self.span_from(mark))
}

///|
fn Parser::parse_pattern_field(self : Parser) -> (QualId, Pattern) raise {
  let field = self.parse_lqualid()
  ignore(self.expect_symbol(Equal))
  (field, self.parse_pattern())
}

///|
fn starts_pattern_field(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true)
}

///|
fn Parser::parse_pat_block(self : Parser) -> Pattern raise {
  let mark = self.mark()
  if self.consume_symbol(LeftPar) is Some(opening) {
    self.enter_nesting(opening.span)
    let pattern = try {
      if self.consume_symbol(RightPar) is Some(_) {
        make_pattern(Ptuple([]), self.span_from(mark))
      } else {
        let inner = self.parse_pattern()
        ignore(self.expect_symbol(RightPar))
        make_pattern(Pparen(inner), self.span_from(mark))
      }
    } catch {
      error => {
        self.leave_nesting()
        raise error
      }
    }
    self.leave_nesting()
    return pattern
  }
  let opening = self.expect_symbol(LeftBrc)
  self.enter_nesting(opening.span)
  let fields = parse_semicolon_list1(
    self,
    parser => starts_pattern_field(parser),
    parser => parser.parse_pattern_field(),
    expected="record pattern field",
  ) catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  ignore(self.expect_symbol(RightBrc)) catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  make_pattern(Prec(fields), self.span_from(mark))
}

///|
fn Parser::parse_pat_arg(self : Parser) -> Pattern raise {
  let mark = self.mark()
  if self.consume_symbol(Underscore) is Some(_) {
    return make_pattern(Pwild, self.span_from(mark))
  }
  if self.at_symbol(Amp) || starts_plain_lident_kind(self.peek_kind_n(0), false) {
    return self.parse_pattern_var()
  }
  if starts_uident_kind(self.peek_kind_n(0)) {
    let path = self.parse_uqualid()
    if self.consume_symbol(Dot) is Some(_) {
      guard self.at_symbol(LeftPar) || self.at_symbol(LeftBrc) else {
        self.fail_syntax("pattern block")
      }
      let inner = self.parse_pat_block()
      return make_pattern(Pscope(path, inner), self.span_from(mark))
    }
    return make_pattern(Papp(path, []), self.span_from(mark))
  }
  self.parse_pat_block()
}

///|
fn Parser::parse_pat_constructor(self : Parser) -> Pattern raise {
  guard starts_uident_kind(self.peek_kind_n(0)) else {
    return self.parse_pat_arg()
  }
  let mark = self.mark()
  let path = self.parse_uqualid()
  if self.consume_symbol(Dot) is Some(_) {
    guard self.at_symbol(LeftPar) || self.at_symbol(LeftBrc) else {
      self.fail_syntax("pattern block")
    }
    let inner = self.parse_pat_block()
    return make_pattern(Pscope(path, inner), self.span_from(mark))
  }
  let arguments : Array[Pattern] = []
  while starts_pat_arg(self) {
    arguments.push(self.parse_pat_arg())
  }
  make_pattern(Papp(path, arguments), self.span_from(mark))
}

///|
fn Parser::parse_pattern_as_binder(self : Parser) -> (Ident, Bool) raise {
  let ghost = self.consume_keyword(Ghost) is Some(_)
  let pattern = self.parse_pattern_var()
  guard pattern.desc is Pvar(ident) else {
    self.fail_syntax("pattern variable")
  }
  (ident, ghost)
}

///|
fn Parser::parse_pat_wrapped(
  self : Parser,
  minimum_binding : Int,
  allow_prefix_ghost : Bool,
) -> Pattern raise {
  let mark = self.mark()
  let mut left = if allow_prefix_ghost && self.consume_keyword(Ghost) is Some(_) {
    let inner = self.parse_pat_wrapped(2, true)
    make_pattern(Pghost(inner), self.span_from(mark))
  } else {
    self.parse_pat_constructor()
  }
  let mut seen_as = false
  let mut seen_cast = false
  while true {
    if minimum_binding <= 1 && self.at_keyword(As) {
      if seen_as {
        self.fail_syntax("single `as` pattern wrapper")
      }
      ignore(self.advance())
      let (ident, ghost) = self.parse_pattern_as_binder()
      left = make_pattern(Pas(left, ident, ghost), self.span_from(mark))
      seen_as = true
      continue
    }
    if minimum_binding <= 3 && self.at_symbol(Colon) {
      if seen_cast {
        self.fail_syntax("single pattern cast")
      }
      let ty = self.parse_cast()
      left = make_pattern(Pcast(left, ty), self.span_from(mark))
      seen_cast = true
      continue
    }
    break
  }
  left
}

///|
fn Parser::parse_pat_conj(
  self : Parser,
  allow_initial_ghost : Bool,
) -> Pattern raise {
  let mark = self.mark()
  let first = self.parse_pat_wrapped(0, allow_initial_ghost)
  guard self.consume_symbol(Comma) is Some(_) else { return first }
  let elements : Array[Pattern] = [first]
  guard starts_pattern(self) else { self.fail_syntax("pattern") }
  elements.push(self.parse_pat_wrapped(0, true))
  while self.consume_symbol(Comma) is Some(_) {
    guard starts_pattern(self) else { self.fail_syntax("pattern") }
    elements.push(self.parse_pat_wrapped(0, true))
  }
  make_pattern(Ptuple(elements), self.span_from(mark))
}

///|
fn Parser::parse_pattern(self : Parser) -> Pattern raise {
  let mark = self.mark()
  let left = self.parse_pat_conj(true)
  if self.consume_symbol(Bar) is Some(_) {
    make_pattern(Por(left, self.parse_pattern()), self.span_from(mark))
  } else {
    left
  }
}

///|
fn Parser::parse_let_pattern(self : Parser) -> Pattern raise {
  let mark = self.mark()
  let left = self.parse_pat_conj(false)
  if self.consume_symbol(Bar) is Some(_) {
    make_pattern(Por(left, self.parse_pattern()), self.span_from(mark))
  } else {
    left
  }
}

// WhyML specification grammar productions.

///|
fn QualId::full_span(self : QualId) -> Span {
  match self {
    Qident(ident) => ident.span
    Qdot(prefix, ident) => prefix.full_span().join(ident.span)
  }
}

///|
fn named_term(name : Ident?, fallback : Bytes, term : Term) -> Term {
  let name = if name is Some(ident) { ident.name } else { fallback }
  make_term(Tattr(Text(b"hyp_name:" + name), term), term.span)
}

///|
fn variant_union(first : Variant, second : Variant) -> Variant raise ParseError {
  if first.items.is_empty() {
    return second
  }
  if second.items.is_empty() {
    return first
  }
  fail_with_diagnostic(
    make_parse_diagnostic(DuplicateVariant, second.items[0].0.span),
  )
}

///|
fn spec_union(first : Spec, second : Spec) -> Spec raise ParseError {
  {
    preconditions: first.preconditions + second.preconditions,
    postconditions: first.postconditions + second.postconditions,
    exceptional_postconditions: first.exceptional_postconditions +
    second.exceptional_postconditions,
    reads: first.reads + second.reads,
    writes: first.writes + second.writes,
    aliases: first.aliases + second.aliases,
    variant: variant_union(first.variant, second.variant),
    check_reads_writes: first.check_reads_writes || second.check_reads_writes,
    diverges: first.diverges || second.diverges,
    partial: first.partial || second.partial,
  }
}

///|
fn starts_spec(parser : Parser) -> Bool {
  parser.at_keyword(Requires) ||
  parser.at_keyword(Ensures) ||
  parser.at_keyword(Returns) ||
  parser.at_keyword(Raises) ||
  parser.at_keyword(Reads) ||
  parser.at_keyword(Writes) ||
  parser.at_keyword(Alias) ||
  parser.at_keyword(Diverges) ||
  parser.at_keyword(Variant)
}

///|
fn Parser::parse_optional_spec_name(self : Parser) -> Ident? raise {
  if self.at_symbol(LeftBrc) {
    None
  } else {
    Some(self.parse_ident_nq())
  }
}

///|
fn Parser::parse_spec_term_block(self : Parser) -> Term raise {
  ignore(self.expect_symbol(LeftBrc))
  let term = self.parse_term()
  ignore(self.expect_symbol(RightBrc))
  term
}

///|
fn Parser::parse_spec_match_case(self : Parser) -> (Pattern, Term) raise {
  let pattern = self.parse_pattern()
  ignore(self.expect_symbol(Arrow))
  (pattern, self.parse_term())
}

///|
fn Parser::parse_spec_match_cases(
  self : Parser,
) -> Array[(Pattern, Term)] raise {
  parse_bar_list1(
    self,
    parser => starts_pattern(parser),
    parser => parser.parse_spec_match_case(),
    expected="postcondition branch",
  )
}

///|
fn Parser::parse_arrow_raise(self : Parser) -> (QualId, (Pattern, Term)?) raise {
  let exception = self.parse_uqualid()
  let exception_span = exception.full_span()
  if self.consume_symbol(Arrow) is Some(_) {
    let unit_pattern = make_pattern(Ptuple([]), exception_span)
    return (exception, Some((unit_pattern, self.parse_term())))
  }
  let pattern = self.parse_pat_arg()
  ignore(self.expect_symbol(Arrow))
  (exception, Some((pattern, self.parse_term())))
}

///|
fn Parser::parse_arrow_raises(
  self : Parser,
) -> Array[(QualId, (Pattern, Term)?)] raise {
  parse_bar_list1(
    self,
    parser => starts_uident_kind(parser.peek_kind_n(0)),
    parser => parser.parse_arrow_raise(),
    expected="exception postcondition",
  )
}

///|
fn Parser::parse_exception_symbols(
  self : Parser,
) -> Array[(QualId, (Pattern, Term)?)] raise {
  let symbols = parse_comma_list1(
    self,
    parser => starts_uident_kind(parser.peek_kind_n(0)),
    parser => parser.parse_uqualid(),
    expected="exception symbol",
  )
  let result : Array[(QualId, (Pattern, Term)?)] = []
  for symbol in symbols {
    result.push((symbol, None))
  }
  result
}

///|
fn starts_lqualid(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true)
}

///|
fn Parser::parse_spec_alias(self : Parser) -> (Term, Term) raise {
  let left = self.parse_single_term()
  ignore(self.expect_keyword(With))
  (left, self.parse_single_term())
}

///|
fn Parser::parse_single_variant(self : Parser) -> (Term, QualId?) raise {
  let term = self.parse_single_term()
  let relation = if self.consume_keyword(With) is Some(_) {
    Some(self.parse_lqualid())
  } else {
    None
  }
  (term, relation)
}

///|
fn Parser::parse_variant_clause(self : Parser) -> Variant raise {
  ignore(self.expect_keyword(Variant))
  let name = self.parse_optional_spec_name()
  ignore(self.expect_symbol(LeftBrc))
  let items = parse_comma_list1(
    self,
    parser => starts_single_term(parser),
    parser => parser.parse_single_variant(),
    expected="variant term",
  )
  ignore(self.expect_symbol(RightBrc))
  let named : Array[(Term, QualId?)] = []
  for item in items {
    named.push((named_term(name, b"Variant", item.0), item.1))
  }
  { items: named }
}

///|
fn Parser::parse_named_invariant(self : Parser, fallback : Bytes) -> Term raise {
  ignore(self.expect_keyword(Invariant))
  let name = self.parse_optional_spec_name()
  named_term(name, fallback, self.parse_spec_term_block())
}

///|
fn Parser::parse_loop_invariant(self : Parser) -> Term raise {
  self.parse_named_invariant(b"LoopInvariant")
}

///|
fn Parser::parse_type_invariant(self : Parser) -> Term raise {
  self.parse_named_invariant(b"TypeInvariant")
}

///|
fn Parser::parse_single_spec(self : Parser) -> Spec raise {
  if self.consume_keyword(Requires) is Some(_) {
    let name = self.parse_optional_spec_name()
    let term = self.parse_spec_term_block()
    return {
      ..Spec::empty(),
      preconditions: [named_term(name, b"Requires", term)],
    }
  }
  if self.consume_keyword(Ensures) is Some(_) {
    let name = self.parse_optional_spec_name()
    ignore(self.expect_symbol(LeftBrc))
    let term = self.parse_term()
    ignore(self.expect_symbol(RightBrc))
    let result_ident = Ident::{
      name: b"result",
      attributes: [],
      span: term.span,
    }
    let result_pattern = make_pattern(Pvar(result_ident), term.span)
    return {
      ..Spec::empty(),
      postconditions: [
        {
          span: term.span,
          branches: [(result_pattern, named_term(name, b"Ensures", term))],
        },
      ],
    }
  }
  if self.consume_keyword(Returns) is Some(_) {
    ignore(self.expect_symbol(LeftBrc))
    let branches_mark = self.mark()
    let branches = self.parse_spec_match_cases()
    let branches_span = self.span_from(branches_mark)
    ignore(self.expect_symbol(RightBrc))
    return {
      ..Spec::empty(),
      postconditions: [{ span: branches_span, branches }],
    }
  }
  if self.consume_keyword(Raises) is Some(_) {
    ignore(self.expect_symbol(LeftBrc))
    let branches_mark = self.mark()
    let branches = parse_alternative(
      self,
      // Both `raises { E -> ... }` and `raises { E, F }` begin in uqualid.
      parser => parser.parse_arrow_raises(),
      parser => parser.parse_exception_symbols(),
    )
    let branches_span = self.span_from(branches_mark)
    ignore(self.expect_symbol(RightBrc))
    return {
      ..Spec::empty(),
      exceptional_postconditions: [{ span: branches_span, branches }],
    }
  }
  if self.consume_keyword(Reads) is Some(_) {
    ignore(self.expect_symbol(LeftBrc))
    let reads = parse_comma_list0(self, parser => starts_lqualid(parser), parser => {
      parser.parse_lqualid()
    })
    ignore(self.expect_symbol(RightBrc))
    return { ..Spec::empty(), reads, check_reads_writes: true }
  }
  if self.consume_keyword(Writes) is Some(_) {
    ignore(self.expect_symbol(LeftBrc))
    let writes = parse_comma_list0(self, parser => starts_single_term(parser), parser => {
      parser.parse_single_term()
    })
    ignore(self.expect_symbol(RightBrc))
    return { ..Spec::empty(), writes, check_reads_writes: true }
  }
  if self.consume_keyword(Alias) is Some(_) {
    ignore(self.expect_symbol(LeftBrc))
    let aliases = parse_comma_list0(
      self,
      parser => starts_single_term(parser),
      parser => parser.parse_spec_alias(),
    )
    ignore(self.expect_symbol(RightBrc))
    return { ..Spec::empty(), aliases, check_reads_writes: true }
  }
  if self.consume_keyword(Diverges) is Some(_) {
    return { ..Spec::empty(), diverges: true }
  }
  if self.at_keyword(Variant) {
    return { ..Spec::empty(), variant: self.parse_variant_clause() }
  }
  self.fail_syntax("specification clause")
}

///|
fn Parser::parse_spec(self : Parser) -> Spec raise {
  let mut result = Spec::empty()
  while starts_spec(self) {
    result = spec_union(result, self.parse_single_spec())
  }
  result
}

///|
priv struct ReturnInfo {
  pattern : Pattern
  return_type : Pty
  mask : Mask
}

///|
fn Parser::parse_return_ident(self : Parser) -> Pattern raise {
  let mark = self.mark()
  if self.consume_symbol(Underscore) is Some(_) {
    let span = self.span_from(mark)
    return make_pattern(Pvar(anonymous_ident(span)), span)
  }
  let ident = parse_attrs_ident(self, parser => parser.parse_lident(true, false))
  let ident = {
    ..ident,
    attributes: [Text(unused_variable_attribute)] + ident.attributes,
  }
  make_pattern(Pvar(ident), self.span_from(mark))
}

///|
fn Parser::parse_return_cast(self : Parser) -> ReturnInfo raise {
  let ghost = self.consume_keyword(Ghost) is Some(_)
  let pattern = self.parse_return_ident()
  let return_type = self.parse_cast()
  { pattern, return_type, mask: if ghost { MaskGhost } else { MaskVisible } }
}

///|
fn Parser::parse_named_return_group(self : Parser) -> ReturnInfo raise {
  let mark = self.mark()
  ignore(self.expect_symbol(LeftPar))
  let first = self.parse_return_cast()
  if self.consume_symbol(Comma) is None {
    ignore(self.expect_symbol(RightPar))
    return first
  }
  let items : Array[ReturnInfo] = [first]
  items.push(self.parse_return_cast())
  while self.consume_symbol(Comma) is Some(_) {
    items.push(self.parse_return_cast())
  }
  ignore(self.expect_symbol(RightPar))
  let patterns : Array[Pattern] = []
  let types : Array[Pty] = []
  let masks : Array[Mask] = []
  for item in items {
    patterns.push(item.pattern)
    types.push(item.return_type)
    masks.push(item.mask)
  }
  {
    pattern: make_pattern(Ptuple(patterns), self.span_from(mark)),
    return_type: PTtuple(types),
    mask: MaskTuple(masks),
  }
}

///|
fn Parser::parse_mixed_return_tuple(self : Parser) -> ReturnInfo raise {
  ignore(self.expect_symbol(LeftPar))
  let types : Array[Pty] = []
  let masks : Array[Mask] = []
  let mut saw_ghost = false
  while true {
    let ghost = self.consume_keyword(Ghost) is Some(_)
    saw_ghost = saw_ghost || ghost
    types.push(self.parse_ty())
    masks.push(if ghost { MaskGhost } else { MaskVisible })
    guard self.consume_symbol(Comma) is Some(_) else { break }
  }
  ignore(self.expect_symbol(RightPar))
  guard saw_ghost else { self.fail_syntax("mixed visible/ghost return tuple") }
  let placeholder = Span::empty(self.peek().span.start)
  if types.length() == 1 {
    {
      pattern: make_pattern(Pwild, placeholder),
      return_type: types[0],
      mask: MaskGhost,
    }
  } else {
    {
      pattern: make_pattern(Pwild, placeholder),
      return_type: PTtuple(types),
      mask: MaskTuple(masks),
    }
  }
}

///|
fn Parser::parse_generic_return(self : Parser) -> ReturnInfo raise {
  let mark = self.mark()
  if self.at_symbol(LeftPar) {
    let mixed = parse_alternative(
      self,
      parser => parser.parse_mixed_return_tuple(),
      parser => {
        let return_type = parser.parse_ty()
        {
          pattern: make_pattern(Pwild, parser.span_from(mark)),
          return_type,
          mask: MaskVisible,
        }
      },
    )
    return { ..mixed, pattern: make_pattern(Pwild, self.span_from(mark)) }
  }
  let ghost = self.consume_keyword(Ghost) is Some(_)
  let return_type = self.parse_ty()
  {
    pattern: make_pattern(Pwild, self.span_from(mark)),
    return_type,
    mask: if ghost {
      MaskGhost
    } else {
      MaskVisible
    },
  }
}

///|
fn Parser::parse_return_named(self : Parser) -> ReturnInfo raise {
  if self.at_symbol(LeftPar) {
    return parse_alternative(
      self,
      // `(x : t)` and `(t)` share their opening parenthesis.
      parser => parser.parse_named_return_group(),
      parser => parser.parse_generic_return(),
    )
  }
  self.parse_generic_return()
}

///|
fn Parser::parse_return_opt(self : Parser) -> (Pattern, Pty?, Mask) raise {
  guard self.consume_symbol(Colon) is Some(_) else {
    return (make_pattern(Pwild, self.empty_span_at_cursor()), None, MaskVisible)
  }
  let result = self.parse_return_named()
  (result.pattern, Some(result.return_type), result.mask)
}

///|
fn apply_return(pattern : Pattern, spec : Spec) -> Spec {
  if pattern.desc is Pwild {
    return spec
  }
  let postconditions : Array[PostCondition] = []
  for post in spec.postconditions {
    if post.branches.length() == 1 &&
      post.branches[0].0.desc is Pvar(ident) &&
      ident.name == b"result" &&
      post.span == ident.span {
      postconditions.push({ ..post, branches: [(pattern, post.branches[0].1)] })
    } else {
      postconditions.push(post)
    }
  }
  { ..spec, postconditions, }
}

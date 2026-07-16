// Identifier, notation, attribute, and qualified-name grammar.

///|
priv enum Notation {
  SNword(Bytes)
  SNinfix(Bytes)
  SNtight(Bytes)
  SNprefix(Bytes)
  SNget(Bytes)
  SNset(Bytes)
  SNupdate(Bytes)
  SNcut(Bytes)
  SNlcut(Bytes)
  SNrcut(Bytes)
}

///|
fn op_infix(operator : Bytes) -> Bytes {
  b"infix " + operator
}

///|
fn op_prefix(operator : Bytes) -> Bytes {
  b"prefix " + operator
}

///|
fn op_get(suffix : Bytes) -> Bytes {
  b"mixfix []" + suffix
}

///|
fn op_set(suffix : Bytes) -> Bytes {
  b"mixfix []<-" + suffix
}

///|
fn op_update(suffix : Bytes) -> Bytes {
  b"mixfix [<-]" + suffix
}

///|
fn op_cut(suffix : Bytes) -> Bytes {
  b"mixfix [..]" + suffix
}

///|
fn op_lcut(suffix : Bytes) -> Bytes {
  b"mixfix [.._]" + suffix
}

///|
fn op_rcut(suffix : Bytes) -> Bytes {
  b"mixfix [_..]" + suffix
}

///|
fn notation_left_space(operator : Bytes) -> Bytes {
  if !operator.is_empty() && operator[0] == b'*' {
    b" "
  } else {
    b""
  }
}

///|
fn notation_right_space(operator : Bytes) -> Bytes {
  if !operator.is_empty() && operator[operator.length() - 1] == b'*' {
    b" "
  } else {
    b""
  }
}

///|
fn Notation::render(self : Notation) -> Bytes {
  match self {
    SNword(word) => word
    SNinfix(operator) =>
      b"(" +
      notation_left_space(operator) +
      operator +
      notation_right_space(operator) +
      b")"
    SNtight(operator) => b"(" + operator + notation_right_space(operator) + b")"
    SNprefix(operator) =>
      b"(" + notation_left_space(operator) + operator + b"_)"
    SNget(suffix) => b"([]" + suffix + b")"
    SNset(suffix) => b"([]" + suffix + b"<-)"
    SNupdate(suffix) => b"([<-]" + suffix + b")"
    SNcut(suffix) => b"([..]" + suffix + b")"
    SNlcut(suffix) => b"([.._]" + suffix + b")"
    SNrcut(suffix) => b"([_..]" + suffix + b")"
  }
}

///|
fn is_tight_operator_tail(byte : Byte) -> Bool {
  byte == b'!' ||
  byte == b'$' ||
  byte == b'&' ||
  byte == b'?' ||
  byte == b'@' ||
  byte == b'^' ||
  byte == b'.' ||
  byte == b':' ||
  byte == b'|' ||
  byte == b'#'
}

///|
fn find_closing_bracket(name : Bytes, start : Int) -> Int? {
  let mut index = start
  while index < name.length() {
    if name[index] == b']' {
      return Some(index)
    }
    index = index + 1
  }
  None
}

///|
/// Byte-for-byte port of Why3 1.7.2's `Ident.sn_decode`.
fn notation_decode(name : Bytes) -> Notation {
  let length = name.length()
  if length <= 6 {
    return SNword(name)
  }
  if name[5] != b' ' && name[6] != b' ' {
    return SNword(name)
  }
  let kind_start = if name.view(end=6) == b"infix " {
    6
  } else if name.view(end=6) == b"prefix" {
    7
  } else if name.view(end=6) == b"mixfix" {
    match find_closing_bracket(name, 7) {
      Some(index) => index + 1
      None => 0
    }
  } else {
    0
  }
  if kind_start == 0 {
    return SNword(name)
  }
  let mut operator_end = kind_start
  while operator_end < length && is_operator_byte(name[operator_end]) {
    operator_end = operator_end + 1
  }
  let mut quote_end = operator_end
  while quote_end < length && name[quote_end] == b'\'' {
    quote_end = quote_end + 1
  }
  let notation_end = if quote_end == length {
    quote_end
  } else if quote_end == operator_end || name[quote_end] == b'_' {
    quote_end
  } else {
    quote_end - 1
  }
  if operator_end == kind_start && kind_start < 8 {
    return SNword(name)
  }
  let decoded = if kind_start == 6 {
    SNinfix(name.view(start=6, end=notation_end).to_owned())
  } else if kind_start == 7 {
    let operator = name.view(start=7, end=notation_end).to_owned()
    let mut tight = !operator.is_empty() &&
      (operator[0] == b'!' || operator[0] == b'?')
    let mut index = 1
    while tight && index < operator_end - 7 {
      tight = is_tight_operator_tail(operator[index])
      index = index + 1
    }
    if tight {
      SNtight(operator)
    } else {
      SNprefix(operator)
    }
  } else {
    let suffix = if operator_end < notation_end {
      name.view(start=operator_end, end=notation_end).to_owned()
    } else {
      b""
    }
    let shape = name.view(start=8, end=operator_end)
    if shape == b"]" {
      SNget(suffix)
    } else if shape == b"]<-" {
      SNset(suffix)
    } else if shape == b"<-]" {
      SNupdate(suffix)
    } else if shape == b"..]" {
      SNcut(suffix)
    } else if shape == b".._]" {
      SNlcut(suffix)
    } else if shape == b"_..]" {
      SNrcut(suffix)
    } else {
      return SNword(
        if notation_end == length {
          name
        } else {
          name.view(end=notation_end).to_owned()
        },
      )
    }
  }
  if notation_end == length {
    decoded
  } else if name[notation_end] != b'\'' && name[notation_end] != b'_' {
    SNword(name)
  } else {
    SNword(
      decoded.render() + name.view(start=notation_end, end=length).to_owned(),
    )
  }
}

///|
fn token_ident(token : LocatedToken, name : Bytes) -> Ident {
  { name, attributes: [], span: token.span }
}

///|
fn[A] fail_reserved_core(token : LocatedToken) -> A raise ParseError {
  fail_with_diagnostic(
    make_parse_diagnostic(
      ReservedCoreIdentifier,
      token.span,
      actual=token.actual,
    ),
  )
}

///|
fn starts_uident_kind(kind : TokenKind?) -> Bool {
  kind is Some(Uident(_) | CoreUident(_))
}

///|
fn starts_plain_lident_kind(kind : TokenKind?, allow_ref : Bool) -> Bool {
  match kind {
    Some(Lident(_) | CoreLident(_)) => true
    Some(Keyword(Float | Range)) => true
    Some(Keyword(Ref)) => allow_ref
    _ => false
  }
}

///|
fn Parser::parse_uident(self : Parser, nonqualified : Bool) -> Ident raise {
  let token = self.peek()
  match token.kind {
    Uident(name) => {
      ignore(self.advance())
      token_ident(token, name)
    }
    CoreUident(name) => {
      ignore(self.advance())
      if nonqualified {
        fail_reserved_core(token)
      } else {
        token_ident(token, name)
      }
    }
    _ => self.fail_syntax("uppercase identifier")
  }
}

///|
fn Parser::parse_lident(
  self : Parser,
  nonqualified : Bool,
  allow_ref : Bool,
) -> Ident raise {
  let token = self.peek()
  match token.kind {
    Lident(name) => {
      ignore(self.advance())
      token_ident(token, name)
    }
    CoreLident(name) => {
      ignore(self.advance())
      if nonqualified {
        fail_reserved_core(token)
      } else {
        token_ident(token, name)
      }
    }
    Keyword(Float) => {
      ignore(self.advance())
      token_ident(token, b"float")
    }
    Keyword(Range) => {
      ignore(self.advance())
      token_ident(token, b"range")
    }
    Keyword(Ref) if allow_ref => {
      ignore(self.advance())
      token_ident(token, b"ref")
    }
    _ => self.fail_syntax("lowercase identifier")
  }
}

///|
fn parse_attribute(parser : Parser) -> Attribute raise {
  let token = parser.peek()
  match token.kind {
    AttributeToken(attribute) => {
      ignore(parser.advance())
      Text(attribute)
    }
    PositionToken(position) => {
      ignore(parser.advance())
      Position(position)
    }
    _ => parser.fail_syntax("attribute")
  }
}

///|
fn starts_attribute(parser : Parser) -> Bool {
  parser.peek_kind_n(0) is Some(AttributeToken(_) | PositionToken(_))
}

///|
fn parse_attributes(parser : Parser) -> Array[Attribute] raise {
  let attributes : Array[Attribute] = []
  while starts_attribute(parser) {
    attributes.push(parse_attribute(parser))
  }
  attributes
}

///|
fn Ident::add_attributes(self : Ident, attributes : Array[Attribute]) -> Ident {
  { ..self, attributes: self.attributes + attributes }
}

///|
fn parse_attrs_ident(
  parser : Parser,
  parse_ident : (Parser) -> Ident raise,
) -> Ident raise {
  let ident = parse_ident(parser)
  ident.add_attributes(parse_attributes(parser))
}

///|
fn parse_op_symbol(parser : Parser) -> (Bytes, Span) raise {
  let token = parser.peek()
  let name = match token.kind {
    Op1(name) | Op2(name) | Op3(name) | Op4(name) => name
    Symbol(Lt) => b"<"
    Symbol(Gt) => b">"
    _ => return parser.fail_syntax("operator symbol")
  }
  ignore(parser.advance())
  (name, token.span)
}

///|
fn Parser::parse_oppref(self : Parser) -> Ident raise {
  let token = self.peek()
  match token.kind {
    OpPref(operator) => {
      ignore(self.advance())
      token_ident(token, op_prefix(operator))
    }
    _ => self.fail_syntax("tight prefix operator")
  }
}

///|
fn Parser::parse_prefix_op(self : Parser) -> Ident raise {
  let token = self.peek()
  if token.kind is Symbol(Minus) {
    ignore(self.advance())
    return token_ident(token, op_prefix(b"-"))
  }
  let (operator, span) = parse_op_symbol(self)
  { name: op_prefix(operator), attributes: [], span }
}

///|
fn Parser::parse_infix_op_1(self : Parser) -> Ident raise {
  let token = self.peek()
  let operator = match token.kind {
    Op1(operator) => operator
    Symbol(Equal) => b"="
    Symbol(LtGt) => b"<>"
    Symbol(Lt) => b"<"
    Symbol(Gt) => b">"
    _ => return self.fail_syntax("level-1 infix operator")
  }
  ignore(self.advance())
  token_ident(token, op_infix(operator))
}

///|
fn Parser::parse_infix_op_234(self : Parser) -> Ident raise {
  let token = self.peek()
  let operator = match token.kind {
    Op2(operator) | Op3(operator) | Op4(operator) => operator
    Symbol(Minus) => b"-"
    _ => return self.fail_syntax("level-2/3/4 infix operator")
  }
  ignore(self.advance())
  token_ident(token, op_infix(operator))
}

///|
fn parse_rightsq(parser : Parser) -> (Bytes, Span) raise {
  let token = parser.peek()
  match token.kind {
    Symbol(RightSq) => {
      ignore(parser.advance())
      (b"", token.span)
    }
    RightSqQuote(suffix) => {
      ignore(parser.advance())
      (suffix, token.span)
    }
    _ => parser.fail_syntax("]")
  }
}

///|
fn parse_mixfix_operator(
  parser : Parser,
  opening : LocatedToken,
) -> (Bytes, Span) raise {
  if parser.consume_symbol(LArrow) is Some(_) {
    let (suffix, closing_span) = parse_rightsq(parser)
    return (op_update(suffix), opening.span.join(closing_span))
  }
  if parser.consume_symbol(DotDot) is Some(_) {
    let left_cut = parser.consume_symbol(Underscore) is Some(_)
    let (suffix, closing_span) = parse_rightsq(parser)
    return (
      if left_cut {
        op_lcut(suffix)
      } else {
        op_cut(suffix)
      },
      opening.span.join(closing_span),
    )
  }
  if parser.consume_symbol(Underscore) is Some(_) {
    ignore(parser.expect_symbol(DotDot))
    let (suffix, closing_span) = parse_rightsq(parser)
    return (op_rcut(suffix), opening.span.join(closing_span))
  }
  let (suffix, closing_span) = parse_rightsq(parser)
  if parser.consume_symbol(LArrow) is Some(arrow) {
    (op_set(suffix), opening.span.join(arrow.span))
  } else {
    (op_get(suffix), opening.span.join(closing_span))
  }
}

///|
fn parse_lident_op_string(parser : Parser) -> (Bytes, Span) raise {
  let first = parser.peek()
  match first.kind {
    Symbol(LeftSq) => {
      ignore(parser.advance())
      parse_mixfix_operator(parser, first)
    }
    Symbol(Equal) => {
      ignore(parser.advance())
      (op_infix(b"="), first.span)
    }
    Symbol(Minus) => {
      ignore(parser.advance())
      match parser.consume_symbol(Underscore) {
        Some(underscore) => (op_prefix(b"-"), first.span.join(underscore.span))
        None => (op_infix(b"-"), first.span)
      }
    }
    OpPref(operator) => {
      ignore(parser.advance())
      let span = match parser.consume_symbol(Underscore) {
        Some(underscore) => first.span.join(underscore.span)
        None => first.span
      }
      (op_prefix(operator), span)
    }
    _ => {
      let (operator, span) = parse_op_symbol(parser)
      match parser.consume_symbol(Underscore) {
        Some(underscore) => (op_prefix(operator), span.join(underscore.span))
        None => (op_infix(operator), span)
      }
    }
  }
}

///|
fn Parser::parse_lident_op(self : Parser, nonqualified : Bool) -> Ident raise {
  let opening = self.expect_symbol(LeftPar)
  let (name, inner_span) = parse_lident_op_string(self)
  let closing = self.peek()
  match closing.kind {
    Symbol(RightPar) => {
      ignore(self.advance())
      { name, attributes: [], span: inner_span }
    }
    RightParUscore(suffix) => {
      ignore(self.advance())
      {
        name: name + suffix,
        attributes: [],
        span: opening.span.join(closing.span),
      }
    }
    RightParQuote(suffix) => {
      ignore(self.advance())
      if nonqualified {
        fail_with_diagnostic(
          make_parse_diagnostic(
            ReservedCoreIdentifier,
            opening.span.join(closing.span),
            actual=closing.actual,
          ),
        )
      } else {
        {
          name: name + suffix,
          attributes: [],
          span: opening.span.join(closing.span),
        }
      }
    }
    _ => self.fail_syntax(")")
  }
}

///|
fn Parser::parse_ident(self : Parser) -> Ident raise {
  match self.peek_kind_n(0) {
    Some(Uident(_) | CoreUident(_)) => self.parse_uident(false)
    Some(Symbol(LeftPar)) => self.parse_lident_op(false)
    _ => self.parse_lident(false, true)
  }
}

///|
fn Parser::parse_ident_nq(self : Parser) -> Ident raise {
  match self.peek_kind_n(0) {
    Some(Uident(_) | CoreUident(_)) => self.parse_uident(true)
    Some(Symbol(LeftPar)) => self.parse_lident_op(true)
    _ => self.parse_lident(true, false)
  }
}

///|
fn Parser::parse_lident_rich(self : Parser) -> Ident raise {
  if self.at_symbol(LeftPar) {
    self.parse_lident_op(true)
  } else {
    self.parse_lident(true, false)
  }
}

///|
fn qualid_from_segments(segments : Array[Ident]) -> QualId {
  let mut result = Qident(segments[0])
  for index = 1; index < segments.length(); index = index + 1 {
    result = Qdot(result, segments[index])
  }
  result
}

///|
fn Parser::parse_uqualid(self : Parser) -> QualId raise {
  let segments : Array[Ident] = [self.parse_uident(false)]
  while self.at_symbol(Dot) && starts_uident_kind(self.peek_kind_n(1)) {
    ignore(self.advance())
    segments.push(self.parse_uident(false))
  }
  qualid_from_segments(segments)
}

///|
fn Parser::parse_qualid(self : Parser) -> QualId raise {
  if !starts_uident_kind(self.peek_kind_n(0)) {
    return Qident(self.parse_ident())
  }
  let segments : Array[Ident] = [self.parse_uident(false)]
  while self.consume_symbol(Dot) is Some(_) {
    if starts_uident_kind(self.peek_kind_n(0)) {
      segments.push(self.parse_uident(false))
    } else {
      segments.push(self.parse_ident())
      return qualid_from_segments(segments)
    }
  }
  qualid_from_segments(segments)
}

///|
fn Parser::parse_lqualid(self : Parser) -> QualId raise {
  if !starts_uident_kind(self.peek_kind_n(0)) {
    return Qident(self.parse_lident(false, true))
  }
  let segments : Array[Ident] = [self.parse_uident(false)]
  while true {
    ignore(self.expect_symbol(Dot))
    if starts_uident_kind(self.peek_kind_n(0)) {
      segments.push(self.parse_uident(false))
    } else {
      segments.push(self.parse_lident(false, true))
      return qualid_from_segments(segments)
    }
  }
  abort("unreachable lowercase qualified identifier state")
}

///|
fn Parser::parse_lqualid_rich(self : Parser) -> QualId raise {
  if !starts_uident_kind(self.peek_kind_n(0)) {
    return Qident(self.parse_lident_rich())
  }
  let segments : Array[Ident] = [self.parse_uident(false)]
  while true {
    ignore(self.expect_symbol(Dot))
    if starts_uident_kind(self.peek_kind_n(0)) {
      segments.push(self.parse_uident(false))
    } else {
      segments.push(self.parse_lident_rich())
      return qualid_from_segments(segments)
    }
  }
  abort("unreachable rich qualified identifier state")
}

///|
fn Parser::parse_sident(self : Parser) -> (Ident, Bool) raise {
  let token = self.peek()
  match token.kind {
    Uident(_) | CoreUident(_) => (self.parse_uident(false), true)
    StringToken(name) => {
      ignore(self.advance())
      (token_ident(token, name), false)
    }
    _ => (self.parse_lident(false, true), false)
  }
}

///|
fn Parser::parse_squalid(self : Parser) -> (QualId, Bool) raise {
  let (first, initially_uppercase) = self.parse_sident()
  let mut last_uppercase = initially_uppercase
  let segments : Array[Ident] = [first]
  while self.consume_symbol(Dot) is Some(_) {
    let (segment, uppercase) = self.parse_sident()
    segments.push(segment)
    last_uppercase = uppercase
  }
  (qualid_from_segments(segments), last_uppercase)
}

///|
fn Parser::parse_tqualid(self : Parser) -> QualId raise {
  let (qualid, last_uppercase) = self.parse_squalid()
  guard last_uppercase else { self.fail_syntax("uppercase identifier") }
  qualid
}

///|
fn Parser::parse_quote_lident(self : Parser) -> Ident raise {
  let token = self.peek()
  match token.kind {
    QuoteLident(name) => {
      ignore(self.advance())
      token_ident(token, name)
    }
    _ => self.fail_syntax("quoted type variable")
  }
}

///|
fn[A] finish_internal_entry(
  parser : Parser,
  parse_entry : (Parser) -> A raise,
) -> A raise ParseError {
  try {
    let result = parse_entry(parser)
    parser.expect_eof()
    result
  } catch {
    SyntaxFailure(failure) => raise ParseError(failure.to_diagnostic())
    ParseError(diagnostic) => raise ParseError(diagnostic)
    _ => abort("unexpected internal parser error")
  }
}

///|
fn starts_ident(parser : Parser) -> Bool {
  starts_uident_kind(parser.peek_kind_n(0)) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), true) ||
  parser.at_symbol(LeftPar)
}

///|
fn parse_qualid_entry(
  input : BytesView,
  filename? : BytesView = b"<qualid-test>",
) -> QualId raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_qualid())
}

///|
fn parse_qualid_list_entry(
  input : BytesView,
  filename? : BytesView = b"<qualid-list-test>",
) -> Array[QualId] raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => {
    parse_comma_list1(
      parser,
      parser => starts_ident(parser),
      parser => parser.parse_qualid(),
      expected="qualified identifier",
    )
  })
}

///|
fn parse_ident_list_entry(
  input : BytesView,
  filename? : BytesView = b"<ident-list-test>",
) -> Array[Ident] raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => {
    parse_comma_list1(
      parser,
      parser => starts_ident(parser),
      parser => parser.parse_ident(),
      expected="identifier",
    )
  })
}

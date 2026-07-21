// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn is_ascii_lower(byte : Byte) -> Bool {
  byte >= b'a' && byte <= b'z'
}

///|
fn is_ascii_upper(byte : Byte) -> Bool {
  byte >= b'A' && byte <= b'Z'
}

///|
fn is_ascii_alpha(byte : Byte) -> Bool {
  is_ascii_lower(byte) || is_ascii_upper(byte)
}

///|
fn is_decimal_digit(byte : Byte) -> Bool {
  byte >= b'0' && byte <= b'9'
}

///|
fn is_octal_digit(byte : Byte) -> Bool {
  byte >= b'0' && byte <= b'7'
}

///|
fn is_binary_digit(byte : Byte) -> Bool {
  byte == b'0' || byte == b'1'
}

///|
fn is_hexadecimal_digit(byte : Byte) -> Bool {
  is_decimal_digit(byte) ||
  (byte >= b'a' && byte <= b'f') ||
  (byte >= b'A' && byte <= b'F')
}

///|
fn is_identifier_digit(byte : Byte) -> Bool {
  is_decimal_digit(byte) || byte == b'_'
}

///|
fn is_space(byte : Byte) -> Bool {
  byte == b' ' || byte == b'\t' || byte == b'\r'
}

///|
fn is_op1_byte(byte : Byte) -> Bool {
  byte == b'=' || byte == b'<' || byte == b'>' || byte == b'~'
}

///|
fn is_op2_byte(byte : Byte) -> Bool {
  byte == b'+' || byte == b'-'
}

///|
fn is_op3_byte(byte : Byte) -> Bool {
  byte == b'*' || byte == b'/' || byte == b'\\' || byte == b'%'
}

///|
fn is_op4_byte(byte : Byte) -> Bool {
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
fn is_operator_byte(byte : Byte) -> Bool {
  is_op1_byte(byte) ||
  is_op2_byte(byte) ||
  is_op3_byte(byte) ||
  is_op4_byte(byte)
}

///|
fn scan_decimal_digits(input : BytesView, start : Int) -> Int {
  let mut index = start
  while index < input.length() && is_decimal_digit(input[index]) {
    index = index + 1
  }
  index
}

///|
fn scan_radix_digits(
  input : BytesView,
  start : Int,
  radix : Int,
  underscores : Bool,
) -> Int {
  let mut index = start
  while index < input.length() {
    let byte = input[index]
    let digit = match radix {
      2 => is_binary_digit(byte)
      8 => is_octal_digit(byte)
      10 => is_decimal_digit(byte)
      16 => is_hexadecimal_digit(byte)
      _ => false
    }
    if digit || (underscores && byte == b'_') {
      index = index + 1
    } else {
      break
    }
  }
  index
}

///|
/// Returns the longest endpoint of Why3's `suffix` regexp. If the suffix ends
/// in a quote run followed by an ASCII letter, the last quote can instead
/// begin a `core_suffix`; that boundary is returned separately.
fn scan_identifier_suffix(input : BytesView, start : Int) -> (Int, Int?) {
  let mut index = start
  while index < input.length() {
    if is_ascii_alpha(input[index]) || is_identifier_digit(input[index]) {
      index = index + 1
      continue
    }
    if input[index] == b'\'' {
      while index < input.length() && input[index] == b'\'' {
        index = index + 1
      }
      if index < input.length() && is_identifier_digit(input[index]) {
        index = index + 1
        continue
      }
      if index < input.length() && is_ascii_alpha(input[index]) {
        return (index, Some(index - 1))
      }
      return (index, None)
    }
    break
  }
  (index, None)
}

///|
fn scan_identifier_body(input : BytesView, after_initial : Int) -> (Int, Bool) {
  let (ordinary_end, boundary) = scan_identifier_suffix(input, after_initial)
  guard boundary is Some(core_start) else { return (ordinary_end, false) }
  (scan_core_identifier_tail(input, core_start), true)
}

///|
fn scan_core_identifier_tail(input : BytesView, core_start : Int) -> Int {
  let mut next_core_start = core_start
  let mut result = core_start + 2
  let mut finished = false
  while !finished {
    let (suffix_end, next_boundary) = scan_identifier_suffix(
      input,
      next_core_start + 2,
    )
    result = suffix_end
    if next_boundary is Some(next) {
      next_core_start = next
    } else {
      finished = true
    }
  }
  result
}

///|
fn scan_identifier(cursor : LexerCursor) -> LocatedToken? {
  let start = cursor.index
  guard cursor.peek() is Some(first) else { return None }
  if !(is_ascii_lower(first) || is_ascii_upper(first) || first == b'_') {
    return None
  }
  let (end, core) = scan_identifier_body(cursor.input, start + 1)
  let text = cursor.view(start, end).to_owned()
  cursor.advance_raw(end - start)
  let kind = if core {
    if is_ascii_lower(first) || first == b'_' {
      CoreLident(text)
    } else {
      CoreUident(text)
    }
  } else if first == b'_' && end == start + 1 {
    Symbol(Underscore)
  } else if is_ascii_lower(first) || first == b'_' {
    if keyword_of(text) is Some(keyword) {
      Keyword(keyword)
    } else {
      Lident(text)
    }
  } else {
    Uident(text)
  }
  Some(located_token(kind, cursor.current_span()))
}

///|
fn scan_quote_lident(cursor : LexerCursor) -> LocatedToken? {
  let start = cursor.index
  guard cursor.peek() is Some(byte) &&
    byte == b'\'' &&
    cursor.peek(offset=1) is Some(first) &&
    is_ascii_lower(first) else {
    return None
  }
  let (end, _) = scan_identifier_suffix(cursor.input, start + 2)
  let payload = cursor.view(start + 1, end).to_owned()
  cursor.advance_raw(end - start)
  Some(located_token(QuoteLident(payload), cursor.current_span()))
}

///|
priv enum NumericForm {
  DecimalInteger(Int, Int)
  HexInteger(Int, Int)
  OctalInteger(Int, Int)
  BinaryInteger(Int, Int)
  DecimalReal(Int, Int, Int, Int, Int, Int)
  HexReal(Int, Int, Int, Int, Int, Int)
}

///|
priv struct NumericCandidate {
  matched_end : Int
  consumed_end : Int
  priority : Int
  form : NumericForm
}

///|
fn choose_numeric_candidate(
  current : NumericCandidate?,
  candidate : NumericCandidate,
) -> NumericCandidate? {
  if current is Some(previous) {
    if candidate.matched_end > previous.matched_end ||
      (
        candidate.matched_end == previous.matched_end &&
        candidate.priority < previous.priority
      ) {
      Some(candidate)
    } else {
      current
    }
  } else {
    Some(candidate)
  }
}

///|
fn exponent_end(input : BytesView, marker : Int, hexadecimal : Bool) -> Int? {
  if marker >= input.length() ||
    (if hexadecimal {
      input[marker] != b'p' && input[marker] != b'P'
    } else {
      input[marker] != b'e' && input[marker] != b'E'
    }) {
    return None
  }
  let mut index = marker + 1
  if index < input.length() && (input[index] == b'+' || input[index] == b'-') {
    index = index + 1
  }
  let digits_end = scan_decimal_digits(input, index)
  if digits_end == index {
    None
  } else {
    Some(digits_end)
  }
}

///|
fn signed_exponent(
  input : BytesView,
  start : Int,
  end : Int,
  span : Span,
) -> Int64 raise ParseError {
  if start == end {
    return 0L
  }
  let mut digits_start = start
  let mut negative = false
  if input[digits_start] == b'+' || input[digits_start] == b'-' {
    negative = input[digits_start] == b'-'
    digits_start = digits_start + 1
  }
  let value = parse_bigint_digits(input[digits_start:end], 10, span)
  checked_ocaml_int(if negative { -value } else { value }, span)
}

///|
fn scan_number(cursor : LexerCursor) -> LocatedToken? raise ParseError {
  let input = cursor.input
  let start = cursor.index
  let mut best : NumericCandidate? = None
  let decimal_end = scan_decimal_digits(input, start)
  if decimal_end > start {
    let separated_end = scan_radix_digits(input, start, 10, true)
    best = choose_numeric_candidate(best, {
      matched_end: separated_end,
      consumed_end: separated_end,
      priority: 0,
      form: DecimalInteger(start, separated_end),
    })
    if decimal_end + 1 < input.length() &&
      input[decimal_end] == b'.' &&
      input[decimal_end + 1] == b'.' {
      best = choose_numeric_candidate(best, {
        matched_end: decimal_end + 2,
        consumed_end: decimal_end,
        priority: 4,
        form: DecimalInteger(start, decimal_end),
      })
    }
    if exponent_end(input, decimal_end, false) is Some(end) {
      best = choose_numeric_candidate(best, {
        matched_end: end,
        consumed_end: end,
        priority: 6,
        form: DecimalReal(
          start,
          decimal_end,
          decimal_end,
          decimal_end,
          decimal_end + 1,
          end,
        ),
      })
    }
  }
  if decimal_end > start &&
    decimal_end < input.length() &&
    input[decimal_end] == b'.' {
    let fraction_start = decimal_end + 1
    let fraction_end = scan_decimal_digits(input, fraction_start)
    let (matched_end, exponent_start, exponent_finish) = if exponent_end(
        input, fraction_end, false,
      )
      is Some(end) {
      (end, fraction_end + 1, end)
    } else {
      (fraction_end, fraction_end, fraction_end)
    }
    best = choose_numeric_candidate(best, {
      matched_end,
      consumed_end: matched_end,
      priority: 6,
      form: DecimalReal(
        start, decimal_end, fraction_start, fraction_end, exponent_start, exponent_finish,
      ),
    })
  }
  if start < input.length() && input[start] == b'.' {
    let fraction_start = start + 1
    let fraction_end = scan_decimal_digits(input, fraction_start)
    if fraction_end > fraction_start {
      let (matched_end, exponent_start, exponent_finish) = if exponent_end(
          input, fraction_end, false,
        )
        is Some(end) {
        (end, fraction_end + 1, end)
      } else {
        (fraction_end, fraction_end, fraction_end)
      }
      best = choose_numeric_candidate(best, {
        matched_end,
        consumed_end: matched_end,
        priority: 6,
        form: DecimalReal(
          start, start, fraction_start, fraction_end, exponent_start, exponent_finish,
        ),
      })
    }
  }
  if start + 2 <= input.length() &&
    input[start] == b'0' &&
    (input[start + 1] == b'x' || input[start + 1] == b'X') {
    let digits_start = start + 2
    let hexadecimal_end = scan_radix_digits(input, digits_start, 16, false)
    let separated_end = scan_radix_digits(input, digits_start, 16, true)
    if hexadecimal_end > digits_start {
      best = choose_numeric_candidate(best, {
        matched_end: separated_end,
        consumed_end: separated_end,
        priority: 1,
        form: HexInteger(digits_start, separated_end),
      })
      if hexadecimal_end + 1 < input.length() &&
        input[hexadecimal_end] == b'.' &&
        input[hexadecimal_end + 1] == b'.' {
        best = choose_numeric_candidate(best, {
          matched_end: hexadecimal_end + 2,
          consumed_end: hexadecimal_end,
          priority: 5,
          form: HexInteger(digits_start, hexadecimal_end),
        })
      }
      if exponent_end(input, hexadecimal_end, true) is Some(end) {
        best = choose_numeric_candidate(best, {
          matched_end: end,
          consumed_end: end,
          priority: 6,
          form: HexReal(
            digits_start,
            hexadecimal_end,
            hexadecimal_end,
            hexadecimal_end,
            hexadecimal_end + 1,
            end,
          ),
        })
      }
      if hexadecimal_end < input.length() && input[hexadecimal_end] == b'.' {
        let fraction_start = hexadecimal_end + 1
        let fraction_end = scan_radix_digits(input, fraction_start, 16, false)
        let (matched_end, exponent_start, exponent_finish) = if exponent_end(
            input, fraction_end, true,
          )
          is Some(end) {
          (end, fraction_end + 1, end)
        } else {
          (fraction_end, fraction_end, fraction_end)
        }
        best = choose_numeric_candidate(best, {
          matched_end,
          consumed_end: matched_end,
          priority: 6,
          form: HexReal(
            digits_start, hexadecimal_end, fraction_start, fraction_end, exponent_start,
            exponent_finish,
          ),
        })
      }
    } else if digits_start < input.length() && input[digits_start] == b'.' {
      let fraction_start = digits_start + 1
      let fraction_end = scan_radix_digits(input, fraction_start, 16, false)
      if fraction_end > fraction_start {
        let (matched_end, exponent_start, exponent_finish) = if exponent_end(
            input, fraction_end, true,
          )
          is Some(end) {
          (end, fraction_end + 1, end)
        } else {
          (fraction_end, fraction_end, fraction_end)
        }
        best = choose_numeric_candidate(best, {
          matched_end,
          consumed_end: matched_end,
          priority: 6,
          form: HexReal(
            digits_start, digits_start, fraction_start, fraction_end, exponent_start,
            exponent_finish,
          ),
        })
      }
    }
  }
  if start + 2 <= input.length() &&
    input[start] == b'0' &&
    (input[start + 1] == b'o' || input[start + 1] == b'O') {
    let digits_start = start + 2
    let end = scan_radix_digits(input, digits_start, 8, true)
    if end > digits_start && is_octal_digit(input[digits_start]) {
      best = choose_numeric_candidate(best, {
        matched_end: end,
        consumed_end: end,
        priority: 2,
        form: OctalInteger(digits_start, end),
      })
    }
  }
  if start + 2 <= input.length() &&
    input[start] == b'0' &&
    (input[start + 1] == b'b' || input[start + 1] == b'B') {
    let digits_start = start + 2
    let end = scan_radix_digits(input, digits_start, 2, true)
    if end > digits_start && is_binary_digit(input[digits_start]) {
      best = choose_numeric_candidate(best, {
        matched_end: end,
        consumed_end: end,
        priority: 3,
        form: BinaryInteger(digits_start, end),
      })
    }
  }
  guard best is Some(candidate) else { return None }
  let span = {
    start: cursor.position,
    end: cursor.position.advance_raw(candidate.consumed_end - start),
  }
  let kind = match candidate.form {
    DecimalInteger(digit_start, digit_end) =>
      Integer(make_int_constant(ILitDec, input[digit_start:digit_end], span~))
    HexInteger(digit_start, digit_end) =>
      Integer(make_int_constant(ILitHex, input[digit_start:digit_end], span~))
    OctalInteger(digit_start, digit_end) =>
      Integer(make_int_constant(ILitOct, input[digit_start:digit_end], span~))
    BinaryInteger(digit_start, digit_end) =>
      Integer(make_int_constant(ILitBin, input[digit_start:digit_end], span~))
    DecimalReal(int_start, int_end, frac_start, frac_end, exp_start, exp_end) => {
      let exponent = signed_exponent(input, exp_start, exp_end, span)
      Real(
        make_real_constant(
          10,
          input[int_start:int_end],
          input[frac_start:frac_end],
          exponent,
          span~,
        ),
      )
    }
    HexReal(int_start, int_end, frac_start, frac_end, exp_start, exp_end) => {
      let exponent = signed_exponent(input, exp_start, exp_end, span)
      Real(
        make_real_constant(
          16,
          input[int_start:int_end],
          input[frac_start:frac_end],
          exponent,
          span~,
        ),
      )
    }
  }
  cursor.advance_raw(candidate.consumed_end - start)
  Some(located_token(kind, cursor.current_span()))
}

///|
priv struct TokenCandidate {
  matched_end : Int
  consumed_end : Int
  priority : Int
  kind : TokenKind
}

///|
fn choose_token_candidate(
  current : TokenCandidate?,
  candidate : TokenCandidate,
) -> TokenCandidate? {
  if current is Some(previous) {
    if candidate.matched_end > previous.matched_end ||
      (
        candidate.matched_end == previous.matched_end &&
        candidate.priority < previous.priority
      ) {
      Some(candidate)
    } else {
      current
    }
  } else {
    Some(candidate)
  }
}

///|
fn bytes_at(input : BytesView, start : Int, text : BytesView) -> Bool {
  if start + text.length() > input.length() {
    return false
  }
  for offset = 0; offset < text.length(); offset = offset + 1 {
    if input[start + offset] != text[offset] {
      return false
    }
  }
  true
}

///|
fn symbol_candidate(
  current : TokenCandidate?,
  input : BytesView,
  start : Int,
  text : BytesView,
  symbol : Symbol,
  priority : Int,
) -> TokenCandidate? {
  if bytes_at(input, start, text) {
    choose_token_candidate(current, {
      matched_end: start + text.length(),
      consumed_end: start + text.length(),
      priority,
      kind: Symbol(symbol),
    })
  } else {
    current
  }
}

///|
fn scan_operator_or_symbol(cursor : LexerCursor) -> LocatedToken? {
  let input = cursor.input
  let start = cursor.index
  let mut best : TokenCandidate? = None
  // The first two candidates model Lexlib.backjump: longest-match selection
  // sees the whole lexeme, while the emitted token ends before the jump.
  if bytes_at(input, start, b"(*)") {
    best = choose_token_candidate(best, {
      matched_end: start + 3,
      consumed_end: start + 1,
      priority: 0,
      kind: Symbol(LeftPar),
    })
  }
  best = symbol_candidate(best, input, start, b",", Comma, 10)
  best = symbol_candidate(best, input, start, b"(", LeftPar, 11)
  best = symbol_candidate(best, input, start, b")", RightPar, 12)
  best = symbol_candidate(best, input, start, b"{", LeftBrc, 13)
  best = symbol_candidate(best, input, start, b"}", RightBrc, 14)
  best = symbol_candidate(best, input, start, b":", Colon, 15)
  best = symbol_candidate(best, input, start, b";", Semicolon, 16)
  best = symbol_candidate(best, input, start, b"->", Arrow, 17)
  if bytes_at(input, start, b"->'") {
    best = choose_token_candidate(best, {
      matched_end: start + 3,
      consumed_end: start + 2,
      priority: 18,
      kind: Symbol(Arrow),
    })
  }
  best = symbol_candidate(best, input, start, b"<-", LArrow, 19)
  best = symbol_candidate(best, input, start, b"<->", LRArrow, 20)
  best = symbol_candidate(best, input, start, b"&&", AmpAmp, 21)
  best = symbol_candidate(best, input, start, b"||", BarBar, 22)
  best = symbol_candidate(best, input, start, b"/\\", And, 23)
  best = symbol_candidate(best, input, start, b"\\/", Or, 24)
  best = symbol_candidate(best, input, start, b".", Dot, 25)
  best = symbol_candidate(best, input, start, b"..", DotDot, 26)
  best = symbol_candidate(best, input, start, b"&", Amp, 27)
  best = symbol_candidate(best, input, start, b"|", Bar, 28)
  best = symbol_candidate(best, input, start, b"<", Lt, 29)
  best = symbol_candidate(best, input, start, b">", Gt, 30)
  best = symbol_candidate(best, input, start, b"<>", LtGt, 31)
  best = symbol_candidate(best, input, start, b"=", Equal, 32)
  best = symbol_candidate(best, input, start, b"=>", EqualArrow, 33)
  best = symbol_candidate(best, input, start, b"-", Minus, 34)
  best = symbol_candidate(best, input, start, b"[", LeftSq, 35)
  best = symbol_candidate(best, input, start, b"]", RightSq, 36)
  if start < input.length() && input[start] == b']' {
    let mut end = start + 1
    while end < input.length() && input[end] == b'\'' {
      end = end + 1
    }
    if end > start + 1 {
      best = choose_token_candidate(best, {
        matched_end: end,
        consumed_end: end,
        priority: 37,
        kind: RightSqQuote(input[start + 1:end].to_owned()),
      })
    }
  }
  if start + 2 < input.length() &&
    input[start] == b')' &&
    input[start + 1] == b'\'' &&
    is_ascii_alpha(input[start + 2]) {
    let (end, _) = scan_identifier_body(input, start + 3)
    best = choose_token_candidate(best, {
      matched_end: end,
      consumed_end: end,
      priority: 38,
      kind: RightParQuote(input[start + 1:end].to_owned()),
    })
  }
  if start + 2 < input.length() &&
    input[start] == b')' &&
    input[start + 1] == b'_' &&
    is_ascii_alpha(input[start + 2]) {
    let (end, _) = scan_identifier_body(input, start + 3)
    best = choose_token_candidate(best, {
      matched_end: end,
      consumed_end: end,
      priority: 39,
      kind: RightParUscore(input[start + 1:end].to_owned()),
    })
  }
  best = symbol_candidate(best, input, start, b"[|", LeftSqBar, 40)
  best = symbol_candidate(best, input, start, b"|]", BarRightSq, 41)
  if start < input.length() && (input[start] == b'!' || input[start] == b'?') {
    let mut end = start + 1
    while end < input.length() && is_op4_byte(input[end]) {
      end = end + 1
    }
    while end < input.length() && input[end] == b'\'' {
      end = end + 1
    }
    best = choose_token_candidate(best, {
      matched_end: end,
      consumed_end: end,
      priority: 50,
      kind: OpPref(input[start:end].to_owned()),
    })
  }
  let mut all_end = start
  let mut has_op1 = false
  while all_end < input.length() && is_operator_byte(input[all_end]) {
    has_op1 = has_op1 || is_op1_byte(input[all_end])
    all_end = all_end + 1
  }
  if has_op1 {
    while all_end < input.length() && input[all_end] == b'\'' {
      all_end = all_end + 1
    }
    best = choose_token_candidate(best, {
      matched_end: all_end,
      consumed_end: all_end,
      priority: 51,
      kind: Op1(input[start:all_end].to_owned()),
    })
  }
  let mut op2_end = start
  let mut has_op2 = false
  while op2_end < input.length() &&
        (
          is_op2_byte(input[op2_end]) ||
          is_op3_byte(input[op2_end]) ||
          is_op4_byte(input[op2_end])
        ) {
    has_op2 = has_op2 || is_op2_byte(input[op2_end])
    op2_end = op2_end + 1
  }
  if has_op2 {
    while op2_end < input.length() && input[op2_end] == b'\'' {
      op2_end = op2_end + 1
    }
    best = choose_token_candidate(best, {
      matched_end: op2_end,
      consumed_end: op2_end,
      priority: 52,
      kind: Op2(input[start:op2_end].to_owned()),
    })
  }
  let mut op3_end = start
  let mut has_op3 = false
  while op3_end < input.length() &&
        (is_op3_byte(input[op3_end]) || is_op4_byte(input[op3_end])) {
    has_op3 = has_op3 || is_op3_byte(input[op3_end])
    op3_end = op3_end + 1
  }
  if has_op3 {
    while op3_end < input.length() && input[op3_end] == b'\'' {
      op3_end = op3_end + 1
    }
    best = choose_token_candidate(best, {
      matched_end: op3_end,
      consumed_end: op3_end,
      priority: 53,
      kind: Op3(input[start:op3_end].to_owned()),
    })
  }
  let mut op4_end = start
  while op4_end < input.length() && is_op4_byte(input[op4_end]) {
    op4_end = op4_end + 1
  }
  if op4_end > start {
    best = choose_token_candidate(best, {
      matched_end: op4_end,
      consumed_end: op4_end,
      priority: 54,
      kind: Op4(input[start:op4_end].to_owned()),
    })
  }
  guard best is Some(candidate) else { return None }
  cursor.advance_raw(candidate.consumed_end - start)
  Some(located_token(candidate.kind, cursor.current_span()))
}

///|
fn escaped_ascii(byte : Byte) -> Byte? {
  match byte {
    b'\\' => Some(b'\\')
    b'n' => Some(b'\n')
    b'r' => Some(b'\r')
    b't' => Some(b'\t')
    b'b' => Some(b'\b')
    b'\'' => Some(b'\'')
    b'"' => Some(b'"')
    _ => None
  }
}

///|
fn three_decimal_escape(input : BytesView, start : Int) -> Byte? {
  if start + 3 > input.length() ||
    !is_decimal_digit(input[start]) ||
    !is_decimal_digit(input[start + 1]) ||
    !is_decimal_digit(input[start + 2]) {
    return None
  }
  let value = (input[start].to_int() - b'0'.to_int()) * 100 +
    (input[start + 1].to_int() - b'0'.to_int()) * 10 +
    (input[start + 2].to_int() - b'0'.to_int())
  if value <= 255 {
    Some(value.to_byte())
  } else {
    None
  }
}

///|
fn two_hex_escape(input : BytesView, start : Int) -> Byte? {
  if start + 2 > input.length() {
    return None
  }
  guard digit_value(input[start]) is Some(high) &&
    high < 16 &&
    digit_value(input[start + 1]) is Some(low) &&
    low < 16 else {
    return None
  }
  Some((high * 16 + low).to_byte())
}

///|
fn three_octal_escape(input : BytesView, start : Int) -> Byte? {
  if start + 3 > input.length() ||
    input[start] < b'0' ||
    input[start] > b'3' ||
    !is_octal_digit(input[start + 1]) ||
    !is_octal_digit(input[start + 2]) {
    return None
  }
  let value = (input[start].to_int() - b'0'.to_int()) * 64 +
    (input[start + 1].to_int() - b'0'.to_int()) * 8 +
    (input[start + 2].to_int() - b'0'.to_int())
  Some(value.to_byte())
}

///|
fn scan_string(cursor : LexerCursor) -> LocatedToken raise ParseError {
  cursor.advance_raw(1)
  let output : Array[Byte] = []
  while true {
    guard cursor.peek() is Some(byte) else {
      fail_with_diagnostic(
        make_parse_diagnostic(UnterminatedString, cursor.empty_span()),
      )
    }
    if byte == b'"' {
      cursor.advance_raw(1)
      return located_token(
        StringToken(Bytes::from_array(output)),
        cursor.current_span(),
      )
    }
    if byte == b'\\' {
      let escape_start = cursor.position
      let after_slash = cursor.index + 1
      if after_slash >= cursor.input.length() {
        // No two-byte escape rule matches. Lexlib accepts the raw printable
        // backslash, then reports unterminated string at EOF.
        output.push(b'\\')
        cursor.advance_raw(1)
        continue
      }
      let mut newline_end = after_slash
      while newline_end < cursor.input.length() &&
            cursor.input[newline_end] == b'\r' {
        newline_end = newline_end + 1
      }
      if newline_end < cursor.input.length() &&
        cursor.input[newline_end] == b'\n' {
        cursor.advance_raw(1)
        cursor.advance_newline(newline_end - after_slash + 1)
        while cursor.peek() is Some(space) && (space == b' ' || space == b'\t') {
          cursor.advance_raw(1)
        }
        continue
      }
      if three_decimal_escape(cursor.input, after_slash) is Some(value) {
        output.push(value)
        cursor.advance_raw(4)
        continue
      }
      if cursor.input[after_slash] == b'x' {
        if two_hex_escape(cursor.input, after_slash + 1) is Some(value) {
          output.push(value)
          cursor.advance_raw(4)
          continue
        }
      }
      if cursor.input[after_slash] == b'o' {
        if three_octal_escape(cursor.input, after_slash + 1) is Some(value) {
          output.push(value)
          cursor.advance_raw(5)
          continue
        }
      }
      if escaped_ascii(cursor.input[after_slash]) is Some(value) {
        output.push(value)
        cursor.advance_raw(2)
        continue
      } else {
        cursor.advance_raw(2)
        fail_with_diagnostic(
          make_parse_diagnostic(IllegalEscape, {
            start: escape_start,
            end: cursor.position,
          }),
        )
      }
    }
    if byte >= b' ' && byte <= b'~' {
      output.push(byte)
      cursor.advance_raw(1)
      continue
    }
    let illegal_start = cursor.position
    cursor.advance_raw(1)
    fail_with_diagnostic(
      make_parse_diagnostic(
        IllegalStringByte,
        { start: illegal_start, end: cursor.position },
        actual="byte {byte.to_int()}",
      ),
    )
  }
  abort("unreachable string scanner state")
}

///|
fn skip_spaces_at(input : BytesView, start : Int) -> Int {
  let mut index = start
  while index < input.length() && is_space(input[index]) {
    index = index + 1
  }
  index
}

///|
fn decimal_range(input : BytesView, start : Int) -> (Int, Int)? {
  let end = scan_decimal_digits(input, start)
  if end == start {
    None
  } else {
    Some((start, end))
  }
}

///|
fn malformed_directive_span(cursor : LexerCursor) -> Span {
  let mut end = cursor.index
  while end < cursor.input.length() && cursor.input[end] != b'\n' {
    if cursor.input[end] == b']' {
      end = end + 1
      break
    }
    end = end + 1
  }
  {
    start: cursor.position,
    end: cursor.position.advance_raw(end - cursor.index),
  }
}

///|
fn[A] fail_invalid_directive(cursor : LexerCursor) -> A raise ParseError {
  fail_with_diagnostic(
    make_parse_diagnostic(
      InvalidPositionDirective,
      malformed_directive_span(cursor),
    ),
  )
}

///|
fn directive_number_span(cursor : LexerCursor, start : Int, end : Int) -> Span {
  {
    start: cursor.position.advance_raw(start - cursor.index),
    end: cursor.position.advance_raw(end - cursor.index),
  }
}

///|
fn parse_directive_number(
  cursor : LexerCursor,
  start : Int,
  end : Int,
  line : Bool,
) -> Int64 raise ParseError {
  let span = directive_number_span(cursor, start, end)
  let value = parse_bigint_digits(cursor.input[start:end], 10, span)
  if line {
    checked_why3_line(value, span)
  } else {
    checked_directive_number(value, span)
  }
}

///|
priv enum DirectiveResult {
  DirectiveSkipped
  DirectiveToken(LocatedToken)
}

///|
fn scan_line_directive(
  cursor : LexerCursor,
) -> DirectiveResult raise ParseError {
  let input = cursor.input
  let start = cursor.index
  let mut index = skip_spaces_at(input, start + 3)
  let mut filename : Bytes? = None
  if index < input.length() && input[index] == b'"' {
    index = index + 1
    let filename_start = index
    while index < input.length() &&
          input[index] != b'"' &&
          input[index] != b'\n' &&
          input[index] != b'\r' {
      index = index + 1
    }
    if index >= input.length() || input[index] != b'"' {
      return fail_invalid_directive(cursor)
    }
    filename = Some(input[filename_start:index].to_owned())
    index = skip_spaces_at(input, index + 1)
  }
  guard decimal_range(input, index) is Some((line_start, line_end)) else {
    return fail_invalid_directive(cursor)
  }
  index = skip_spaces_at(input, line_end)
  guard decimal_range(input, index) is Some((column_start, column_end)) else {
    return fail_invalid_directive(cursor)
  }
  index = skip_spaces_at(input, column_end)
  if index >= input.length() || input[index] != b']' {
    return fail_invalid_directive(cursor)
  }
  let end = index + 1
  let line = parse_directive_number(cursor, line_start, line_end, false)
  let column = parse_directive_number(cursor, column_start, column_end, false)
  cursor.advance_raw(end - start)
  cursor.switch_logical_location(filename, line, column)
  DirectiveSkipped
}

///|
fn scan_position_directive(
  cursor : LexerCursor,
) -> DirectiveResult raise ParseError {
  let input = cursor.input
  let start = cursor.index
  let mut index = skip_spaces_at(input, start + 2)
  if index >= input.length() || input[index] != b'"' {
    return fail_invalid_directive(cursor)
  }
  index = index + 1
  let filename_start = index
  while index < input.length() &&
        input[index] != b'"' &&
        input[index] != b'\n' &&
        input[index] != b'\r' {
    index = index + 1
  }
  if index >= input.length() || input[index] != b'"' {
    return fail_invalid_directive(cursor)
  }
  let filename = input[filename_start:index].to_owned()
  index = skip_spaces_at(input, index + 1)
  let ranges : Array[(Int, Int)] = []
  for _ in 0..<4 {
    guard decimal_range(input, index) is Some(range) else {
      return fail_invalid_directive(cursor)
    }
    ranges.push(range)
    index = skip_spaces_at(input, range.1)
  }
  if index >= input.length() || input[index] != b']' {
    return fail_invalid_directive(cursor)
  }
  let end = index + 1
  let begin_line = parse_directive_number(
    cursor,
    ranges[0].0,
    ranges[0].1,
    true,
  )
  let begin_column = parse_directive_number(
    cursor,
    ranges[1].0,
    ranges[1].1,
    false,
  )
  let end_line = parse_directive_number(cursor, ranges[2].0, ranges[2].1, true)
  let end_column = parse_directive_number(
    cursor,
    ranges[3].0,
    ranges[3].1,
    false,
  )
  let (begin_line, begin_column) = why3_decode_line_column(
    begin_line, begin_column,
  )
  let (end_line, end_column) = why3_decode_line_column(end_line, end_column)
  let physical_start = cursor.position
  cursor.advance_raw(end - start)
  let physical_end = cursor.position
  let position = Span::{
    start: {
      filename,
      byte_offset: physical_start.byte_offset,
      line: begin_line,
      column: begin_column,
    },
    end: {
      filename,
      byte_offset: physical_end.byte_offset,
      line: end_line,
      column: end_column,
    },
  }
  DirectiveToken(located_token(PositionToken(position), cursor.current_span()))
}

///|
fn scan_attribute(cursor : LexerCursor) -> DirectiveResult raise ParseError {
  let input = cursor.input
  let start = cursor.index
  let label_start = skip_spaces_at(input, start + 2)
  let mut end = label_start
  while end < input.length() && input[end] != b']' && input[end] != b'\n' {
    end = end + 1
  }
  if end >= input.length() || input[end] != b']' {
    return fail_invalid_directive(cursor)
  }
  let mut label_end = end
  while label_end > label_start && input[label_end - 1] == b' ' {
    label_end = label_end - 1
  }
  if label_end == label_start {
    return fail_invalid_directive(cursor)
  }
  let label = input[label_start:label_end]
  cursor.advance_raw(end + 1 - start)
  cursor.adjust_attribute_label(label)
  DirectiveToken(
    located_token(AttributeToken(label.to_owned()), cursor.current_span()),
  )
}

///|
fn comment_newline_length(cursor : LexerCursor) -> Int? {
  let mut end = cursor.index
  while end < cursor.input.length() && cursor.input[end] == b'\r' {
    end = end + 1
  }
  if end < cursor.input.length() && cursor.input[end] == b'\n' {
    Some(end - cursor.index + 1)
  } else {
    None
  }
}

///|
fn skip_comment(cursor : LexerCursor) -> Unit raise ParseError {
  let opener = Span::{
    start: cursor.position,
    end: cursor.position.advance_raw(2),
  }
  cursor.comment_depth = 1
  cursor.advance_raw(2)
  while cursor.comment_depth > 0 {
    if cursor.at_end() {
      fail_with_diagnostic(make_parse_diagnostic(UnterminatedComment, opener))
    }
    if cursor.starts_with(b"(*)") {
      cursor.advance_raw(3)
      continue
    }
    if cursor.starts_with(b"*)") {
      cursor.advance_raw(2)
      cursor.comment_depth = cursor.comment_depth - 1
      continue
    }
    if cursor.starts_with(b"(*") {
      cursor.advance_raw(2)
      cursor.comment_depth = cursor.comment_depth + 1
      continue
    }
    if comment_newline_length(cursor) is Some(length) {
      cursor.advance_newline(length)
      continue
    }
    cursor.advance_comment_byte()
  }
}

///|
fn scan_next_token(cursor : LexerCursor) -> LocatedToken raise ParseError {
  while true {
    cursor.mark_token_start()
    if cursor.at_end() {
      return located_token(Eof, cursor.empty_span())
    }
    if cursor.peek() is Some(byte) && byte == b'\n' {
      cursor.advance_newline(1)
      continue
    }
    if cursor.peek() is Some(byte) && is_space(byte) {
      while cursor.peek() is Some(space) && is_space(space) {
        cursor.advance_raw(1)
      }
      continue
    }
    if cursor.starts_with(b"[##") {
      match scan_line_directive(cursor) {
        DirectiveSkipped => continue
        DirectiveToken(token) => return token
      }
    }
    if cursor.starts_with(b"[#") {
      match scan_position_directive(cursor) {
        DirectiveToken(token) => return token
        DirectiveSkipped => continue
      }
    }
    if cursor.starts_with(b"[@") {
      match scan_attribute(cursor) {
        DirectiveToken(token) => return token
        DirectiveSkipped => continue
      }
    }
    if cursor.starts_with(b"(*") && !cursor.starts_with(b"(*)") {
      skip_comment(cursor)
      continue
    }
    break
  }
  cursor.mark_token_start()
  if cursor.peek() is Some(byte) && byte == b'"' {
    return scan_string(cursor)
  }
  if scan_identifier(cursor) is Some(token) {
    return token
  }
  if cursor.peek() is Some(byte) && (is_decimal_digit(byte) || byte == b'.') {
    if scan_number(cursor) is Some(token) {
      return token
    }
  }
  if scan_quote_lident(cursor) is Some(token) {
    return token
  }
  if scan_operator_or_symbol(cursor) is Some(token) {
    return token
  }
  guard cursor.peek() is Some(_) else {
    return located_token(Eof, cursor.empty_span())
  }
  let start = cursor.position
  cursor.advance_raw(1)
  fail_with_diagnostic(
    make_parse_diagnostic(
      IllegalCharacter,
      { start, end: cursor.position },
      actual="byte {byte.to_int()}",
    ),
  )
}

///|
priv struct LazyLexer {
  cursor : LexerCursor
  cache : Array[LexItem]
  mut terminal : Bool
  mut scan_count : Int
  mut commit_count : Int
  mut cache_push_count : Int
}

///|
fn LazyLexer::new(input : BytesView, filename : BytesView) -> LazyLexer {
  {
    cursor: LexerCursor::new(input, filename),
    cache: [],
    terminal: false,
    scan_count: 0,
    commit_count: 0,
    cache_push_count: 0,
  }
}

///|
fn LazyLexer::scan_one(self : LazyLexer) -> LexItem {
  self.scan_count = self.scan_count + 1
  Token(scan_next_token(self.cursor)) catch {
    ParseError(diagnostic) => DeferredLexError(diagnostic)
  }
}

///|
fn LazyLexer::ensure(self : LazyLexer, index : Int) -> LexItem {
  while self.cache.length() <= index && !self.terminal {
    let item = self.scan_one()
    self.cache.push(item)
    self.cache_push_count = self.cache_push_count + 1
    if item is DeferredLexError(_) || item is Token({ kind: Eof, .. }) {
      self.terminal = true
    }
  }
  if index < self.cache.length() {
    self.cache[index]
  } else {
    self.cache[self.cache.length() - 1]
  }
}

///|
fn LazyLexer::committed(
  self : LazyLexer,
  index : Int,
) -> LocatedToken raise ParseError {
  self.commit_count = self.commit_count + 1
  match self.ensure(index) {
    Token(token) => token
    DeferredLexError(diagnostic) => raise ParseError(diagnostic)
  }
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum SmtTokenKind {
  LeftParenthesis
  RightParenthesis
  Atom
  QuotedSymbol
  StringLiteral
} derive(Eq, Debug)

///|
pub(all) struct SmtToken {
  kind : SmtTokenKind
  bytes : Bytes
  start : Int
  end : Int
} derive(Eq, Debug)

///|
fn smt_space(byte : Byte) -> Bool {
  byte == b' ' || byte == b'\t' || byte == b'\r' || byte == b'\n'
}

///|
fn smt_atom_delimiter(byte : Byte) -> Bool {
  smt_space(byte) || byte == b'(' || byte == b')' || byte == b';'
}

///|
fn lex_quoted_symbol(input : BytesView, start : Int) -> Int raise PrinterError {
  let mut index = start + 1
  while index < input.length() {
    let byte = input[index]
    if byte == b'|' {
      return index + 1
    }
    if byte == b'\\' || byte == b'\x00' || byte == b'\r' || byte == b'\n' {
      fail_printer(
        InvalidSmtToken,
        "invalid character in SMT-LIB quoted symbol",
      )
    }
    index = index + 1
  }
  fail_printer(InvalidSmtToken, "unterminated SMT-LIB quoted symbol")
}

///|
fn lex_string_literal(input : BytesView, start : Int) -> Int raise PrinterError {
  let mut index = start + 1
  while index < input.length() {
    if input[index] == b'"' {
      if index + 1 < input.length() && input[index + 1] == b'"' {
        index = index + 2
        continue
      }
      return index + 1
    }
    if input[index] == b'\x00' {
      fail_printer(InvalidSmtToken, "NUL is not valid in an SMT-LIB string")
    }
    index = index + 1
  }
  fail_printer(InvalidSmtToken, "unterminated SMT-LIB string")
}

///|
pub fn lex_smt_tokens(input : BytesView) -> Array[SmtToken] raise PrinterError {
  let result : Array[SmtToken] = []
  let mut index = 0
  while index < input.length() {
    let byte = input[index]
    if smt_space(byte) {
      index = index + 1
      continue
    }
    if byte == b';' {
      while index < input.length() && input[index] != b'\n' {
        index = index + 1
      }
      continue
    }
    let start = index
    let (kind, end) = match byte {
      b'(' => (LeftParenthesis, index + 1)
      b')' => (RightParenthesis, index + 1)
      b'|' => (QuotedSymbol, lex_quoted_symbol(input, index))
      b'"' => (StringLiteral, lex_string_literal(input, index))
      _ => {
        while index < input.length() && !smt_atom_delimiter(input[index]) {
          if input[index] == b'\x00' {
            fail_printer(InvalidSmtToken, "NUL is not valid in an SMT token")
          }
          index = index + 1
        }
        if index == start {
          fail_printer(InvalidSmtToken, "empty SMT token")
        }
        (Atom, index)
      }
    }
    result.push({ kind, bytes: input[start:end].to_owned(), start, end })
    index = end
  }
  result
}

///|
struct NormalizedSmtTokens {
  tokens : Array[Bytes]
}

///|
pub fn NormalizedSmtTokens::tokens(
  self : NormalizedSmtTokens,
) -> ArrayView[Bytes] {
  self.tokens[:]
}

///|
fn generated_token(stage : @identity.GeneratedStage, ordinal : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"$generated[")
  output.write_bytes(stage.canonical_name())
  output.write_bytes(b"][")
  output.write_string_utf8(ordinal.to_string())
  output.write_byte(b']')
  output.to_bytes()
}

///|
fn generated_ordinal(
  stages : Array[(@identity.GeneratedStage, Map[@identity.SemanticId, Int])],
  stage : @identity.GeneratedStage,
  semantic_id : @identity.SemanticId,
) -> Int {
  for entry in stages {
    if entry.0 == stage {
      match entry.1.get(semantic_id) {
        Some(ordinal) => return ordinal
        None => {
          let ordinal = entry.1.length()
          entry.1[semantic_id] = ordinal
          return ordinal
        }
      }
    }
  }
  let identifiers : Map[@identity.SemanticId, Int] = Map([])
  identifiers[semantic_id] = 0
  stages.push((stage, identifiers))
  0
}

///|
pub fn normalize_smt_query(
  query : SmtQuery,
) -> NormalizedSmtTokens raise PrinterError {
  let occurrences : Map[Int, PrintedIdentifier] = Map([])
  for occurrence in query.identifiers {
    if occurrence.start < 0 ||
      occurrence.end <= occurrence.start ||
      occurrence.end > query.bytes.length() ||
      occurrences.contains(occurrence.start) {
      fail_printer(
        InvalidIdentifierOccurrence,
        "invalid or duplicate printed identifier occurrence",
      )
    }
    occurrences[occurrence.start] = occurrence
  }
  let generated : Array[
    (@identity.GeneratedStage, Map[@identity.SemanticId, Int]),
  ] = []
  let normalized : Array[Bytes] = []
  let matched : Map[Int, Unit] = Map([])
  for token in lex_smt_tokens(query.bytes) {
    match occurrences.get(token.start) {
      None => normalized.push(token.bytes)
      Some(occurrence) => {
        if occurrence.end != token.end || token.kind != Atom {
          fail_printer(
            InvalidIdentifierOccurrence,
            "printed identifier does not align with one simple SMT token",
          )
        }
        matched[token.start] = ()
        match occurrence.origin.kind().view() {
          GeneratedKind(stage) =>
            normalized.push(
              generated_token(
                stage,
                generated_ordinal(generated, stage, occurrence.semantic_id),
              ),
            )
          UserKind | SnapshotKind => normalized.push(token.bytes)
        }
      }
    }
  }
  if matched.length() != occurrences.length() {
    fail_printer(
      InvalidIdentifierOccurrence,
      "printed identifier occurrence is hidden by whitespace or a comment",
    )
  }
  { tokens: normalized }
}

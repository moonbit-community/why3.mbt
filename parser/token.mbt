///|
priv enum Keyword {
  Abstract
  Absurd
  Alias
  Any
  As
  Assert
  Assume
  At
  Axiom
  Begin
  Break
  By
  Check
  Clone
  Coinductive
  Constant
  Continue
  Diverges
  Do
  Done
  Downto
  Else
  End
  Ensures
  Epsilon
  Exception
  Exists
  Export
  False
  For
  Forall
  Fun
  Function
  Ghost
  Goal
  If
  Import
  In
  Inductive
  Invariant
  Label
  Lemma
  Let
  Match
  Meta
  Module
  Mutable
  Not
  Old
  Partial
  Predicate
  Private
  Pure
  Raise
  Raises
  Reads
  Rec
  Requires
  Return
  Returns
  Scope
  So
  Then
  Theory
  To
  True
  Try
  Type
  Use
  Val
  Variant
  While
  With
  Writes
  Float
  Range
  Ref
} derive(Eq)

///|
priv enum Symbol {
  And
  Arrow
  EqualArrow
  Amp
  Bar
  Colon
  Comma
  Dot
  DotDot
  Equal
  Lt
  Gt
  LtGt
  Minus
  LeftPar
  LeftSq
  LeftSqBar
  LArrow
  LRArrow
  Or
  RightPar
  RightSq
  BarRightSq
  Underscore
  AmpAmp
  BarBar
  LeftBrc
  RightBrc
  Semicolon
} derive(Eq)

///|
priv enum TokenKind {
  Lident(Bytes)
  CoreLident(Bytes)
  Uident(Bytes)
  CoreUident(Bytes)
  Integer(IntConstant)
  Op1(Bytes)
  Op2(Bytes)
  Op3(Bytes)
  Op4(Bytes)
  OpPref(Bytes)
  Real(RealConstant)
  StringToken(Bytes)
  AttributeToken(Bytes)
  PositionToken(Span)
  QuoteLident(Bytes)
  RightSqQuote(Bytes)
  RightParQuote(Bytes)
  RightParUscore(Bytes)
  Keyword(Keyword)
  Symbol(Symbol)
  Eof
} derive(Eq)

///|
priv struct LocatedToken {
  kind : TokenKind
  span : Span
  actual : String
}

///|
priv enum LexItem {
  Token(LocatedToken)
  DeferredLexError(ParseDiagnostic)
}

///|
fn ascii_token_actual(category : String, text : Bytes) -> String {
  // Identifier and operator payloads are produced exclusively by ASCII
  // automata. The total decoder avoids introducing an error effect here.
  "\{category} `\{@utf8.decode_lossy(text)}`"
}

///|
fn TokenKind::actual(self : TokenKind) -> String {
  match self {
    Lident(text) => ascii_token_actual("lowercase identifier", text)
    CoreLident(text) => ascii_token_actual("core lowercase identifier", text)
    Uident(text) => ascii_token_actual("uppercase identifier", text)
    CoreUident(text) => ascii_token_actual("core uppercase identifier", text)
    Integer(_) => "integer literal"
    Op1(text) => ascii_token_actual("level-1 operator", text)
    Op2(text) => ascii_token_actual("level-2 operator", text)
    Op3(text) => ascii_token_actual("level-3 operator", text)
    Op4(text) => ascii_token_actual("level-4 operator", text)
    OpPref(text) => ascii_token_actual("prefix operator", text)
    Real(_) => "real literal"
    StringToken(_) => "string literal"
    AttributeToken(_) => "attribute"
    PositionToken(_) => "position attribute"
    QuoteLident(text) => ascii_token_actual("quoted lowercase identifier", text)
    RightSqQuote(text) => ascii_token_actual("right bracket suffix", text)
    RightParQuote(text) =>
      ascii_token_actual("right parenthesis quote suffix", text)
    RightParUscore(text) =>
      ascii_token_actual("right parenthesis underscore suffix", text)
    Keyword(keyword) => keyword.spelling()
    Symbol(symbol) => symbol.spelling()
    Eof => "end of input"
  }
}

///|
fn located_token(kind : TokenKind, span : Span) -> LocatedToken {
  { actual: kind.actual(), kind, span }
}

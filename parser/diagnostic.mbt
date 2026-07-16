///|
/// Stable classes for lexical, syntactic, and parsing-time semantic errors.
pub(all) enum ParseErrorKind {
  InvalidUtf16
  IllegalCharacter
  UnterminatedComment
  UnterminatedString
  IllegalEscape
  IllegalStringByte
  InvalidNumericLiteral
  InvalidPositionDirective
  UnexpectedToken
  UnexpectedEof
  NestingTooDeep
  NumericOverflow
  DuplicateVariant
  InvalidAssignment
  InvalidParallelAssignment
  GhostPartialConflict
  InvalidPartialDeclaration
  DoubleReference
  AnonymousReference
  UndeterminedParameterType
  IllegalKindQualifier
  RestrictedAnySpec
  ReservedCoreIdentifier
  UnsupportedEpsilon
  NestedModule
} derive(Debug, Eq)

///|
/// A public diagnostic that does not expose private lexer or parser types.
pub(all) struct ParseDiagnostic {
  kind : ParseErrorKind
  span : Span
  actual : String?
  expected : Array[String]
  message : String
} derive(Debug, Eq)

///|
/// The checked error raised by every public parser entry point.
pub(all) suberror ParseError {
  ParseError(ParseDiagnostic)
} derive(Debug, Eq)

///|
fn stable_expected(expected : Array[String]) -> Array[String] {
  let unique : Array[String] = []
  for item in expected {
    if !unique.contains(item) {
      unique.push(item)
    }
  }
  unique
}

///|
fn diagnostic_message(
  kind : ParseErrorKind,
  actual : String?,
  expected : Array[String],
) -> String {
  match kind {
    InvalidUtf16 => "invalid UTF-16 source text"
    IllegalCharacter =>
      match actual {
        Some(actual) => "illegal character: \{actual}"
        None => "illegal character"
      }
    UnterminatedComment => "unterminated comment"
    UnterminatedString => "unterminated string literal"
    IllegalEscape => "illegal string escape"
    IllegalStringByte => "illegal byte in string literal"
    InvalidNumericLiteral => "invalid numeric literal"
    InvalidPositionDirective => "invalid source position directive"
    UnexpectedToken => {
      let token = match actual {
        Some(actual) => actual
        None => "token"
      }
      if expected.is_empty() {
        "unexpected \{token}"
      } else {
        "unexpected \{token}; expected \{expected.join(", ")}"
      }
    }
    UnexpectedEof =>
      if expected.is_empty() {
        "unexpected end of input"
      } else {
        "unexpected end of input; expected \{expected.join(", ")}"
      }
    NestingTooDeep => "maximum parser nesting depth exceeded"
    NumericOverflow => "numeric value is outside the Why3 64-bit parser range"
    DuplicateVariant => "multiple variant clauses are not allowed"
    InvalidAssignment => "invalid assignment target"
    InvalidParallelAssignment => "invalid parallel assignment"
    GhostPartialConflict => "ghost and partial modifiers cannot be combined"
    InvalidPartialDeclaration => "this expression cannot be declared partial"
    DoubleReference => "this variable is already a reference"
    AnonymousReference => "anonymous parameters cannot be references"
    UndeterminedParameterType => "cannot determine the type of the parameter"
    IllegalKindQualifier => "illegal kind qualifier"
    RestrictedAnySpec => "this specification clause is not allowed on any"
    ReservedCoreIdentifier => "reserved core identifier cannot be user-defined"
    UnsupportedEpsilon =>
      "epsilon terms are not supported by concrete WhyML syntax"
    NestedModule => "trying to open a module inside another module"
  }
}

///|
fn make_parse_diagnostic(
  kind : ParseErrorKind,
  span : Span,
  actual? : String,
  expected? : Array[String] = [],
) -> ParseDiagnostic {
  let expected = stable_expected(expected)
  {
    kind,
    span,
    actual,
    expected,
    message: diagnostic_message(kind, actual, expected),
  }
}

///|
fn[A] fail_with_diagnostic(diagnostic : ParseDiagnostic) -> A raise ParseError {
  raise ParseError(diagnostic)
}

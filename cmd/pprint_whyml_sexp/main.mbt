///|
extern "C" fn exit_process(code : Int) -> Unit = "exit"

///|
fn path_is_valid_utf16(path : StringView) -> Bool {
  let mut index = 0
  while index < path.length() {
    let code = path.unsafe_get(index).to_int()
    if code >= 0xd800 && code <= 0xdbff {
      if index + 1 >= path.length() {
        return false
      }
      let trailing = path.unsafe_get(index + 1).to_int()
      if trailing < 0xdc00 || trailing > 0xdfff {
        return false
      }
      index = index + 2
    } else if code >= 0xdc00 && code <= 0xdfff {
      return false
    } else {
      index = index + 1
    }
  }
  true
}

///|
fn parse_error_kind_name(kind : @parser.ParseErrorKind) -> String {
  match kind {
    InvalidUtf16 => "InvalidUtf16"
    IllegalCharacter => "IllegalCharacter"
    UnterminatedComment => "UnterminatedComment"
    UnterminatedString => "UnterminatedString"
    IllegalEscape => "IllegalEscape"
    IllegalStringByte => "IllegalStringByte"
    InvalidNumericLiteral => "InvalidNumericLiteral"
    InvalidPositionDirective => "InvalidPositionDirective"
    UnexpectedToken => "UnexpectedToken"
    UnexpectedEof => "UnexpectedEof"
    NestingTooDeep => "NestingTooDeep"
    NumericOverflow => "NumericOverflow"
    DuplicateVariant => "DuplicateVariant"
    InvalidAssignment => "InvalidAssignment"
    InvalidParallelAssignment => "InvalidParallelAssignment"
    GhostPartialConflict => "GhostPartialConflict"
    InvalidPartialDeclaration => "InvalidPartialDeclaration"
    DoubleReference => "DoubleReference"
    AnonymousReference => "AnonymousReference"
    UndeterminedParameterType => "UndeterminedParameterType"
    IllegalKindQualifier => "IllegalKindQualifier"
    RestrictedAnySpec => "RestrictedAnySpec"
    ReservedCoreIdentifier => "ReservedCoreIdentifier"
    UnsupportedEpsilon => "UnsupportedEpsilon"
    NestedModule => "NestedModule"
  }
}

///|
async fn fail_pprinter(message : String) -> Unit {
  @stdio.stderr.write("pprint_whyml_sexp: " + message + "\n")
  exit_process(1)
}

///|
async fn report_parse_error(diagnostic : @parser.ParseDiagnostic) -> Unit {
  let start = diagnostic.span.start
  let end = diagnostic.span.end
  fail_pprinter(
    "parse error " +
    parse_error_kind_name(diagnostic.kind) +
    " " +
    start.line.to_string() +
    ":" +
    start.column.to_string() +
    "-" +
    end.line.to_string() +
    ":" +
    end.column.to_string() +
    ": " +
    diagnostic.message,
  )
}

///|
async fn main {
  let arguments = @env.args()
  if arguments.length() != 2 {
    fail_pprinter("expected exactly one fixture path")
    return
  }
  let path = arguments[1]
  if !path_is_valid_utf16(path[:]) {
    fail_pprinter("fixture path is not valid UTF-16")
    return
  }
  let source = @fs.read_file(path).binary() catch {
    _ => {
      fail_pprinter("cannot read fixture")
      return
    }
  }
  let filename = @utf8.encode(path)
  let file = @parser.parse_mlw_file(source, filename~) catch {
    ParseError(diagnostic) => {
      report_parse_error(diagnostic)
      return
    }
  }
  @stdio.stdout.write(sexp_of_mlw_file(file).render())
}

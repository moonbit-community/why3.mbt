// Minimal Sexplib-compatible tree and Why3-compatible atom encoding for pprint_whyml_sexp.

///|
priv enum Sexp {
  Atom(Bytes)
  List(Array[Sexp])
} derive(Debug, Eq)

///|
fn sexp_atom(value : Bytes) -> Sexp {
  Atom(value)
}

///|
fn sexp_atom_string(value : String) -> Sexp {
  Atom(@utf8.encode(value))
}

///|
fn sexp_list(items : Array[Sexp]) -> Sexp {
  List(items)
}

///|
fn sexp_variant(name : String, arguments : Array[Sexp]) -> Sexp {
  if arguments.is_empty() {
    sexp_atom_string(name)
  } else {
    let items = [sexp_atom_string(name)]
    for argument in arguments {
      items.push(argument)
    }
    sexp_list(items)
  }
}

///|
fn[A] sexp_array(values : Array[A], project : (A) -> Sexp) -> Sexp {
  let items = []
  for value in values {
    items.push(project(value))
  }
  sexp_list(items)
}

///|
fn[A] sexp_option(value : A?, project : (A) -> Sexp) -> Sexp {
  if value is Some(value) {
    sexp_list([project(value)])
  } else {
    sexp_list([])
  }
}

///|
fn sexp_bool(value : Bool) -> Sexp {
  sexp_atom_string(if value { "true" } else { "false" })
}

///|
fn sexp_int64(value : Int64) -> Sexp {
  sexp_atom_string(value.to_string())
}

///|
fn sexp_bigint(value : BigInt) -> Sexp {
  sexp_atom_string(value.to_string())
}

///|
fn[A, B] sexp_pair(
  pair : (A, B),
  first : (A) -> Sexp,
  second : (B) -> Sexp,
) -> Sexp {
  sexp_list([first(pair.0), second(pair.1)])
}

///|
fn sexp_record(fields : Array[(String, Sexp)]) -> Sexp {
  sexp_array(fields, field => sexp_list([sexp_atom_string(field.0), field.1]))
}

///|
fn ascii_digit(value : Int) -> Char {
  match value {
    0 => '0'
    1 => '1'
    2 => '2'
    3 => '3'
    4 => '4'
    5 => '5'
    6 => '6'
    7 => '7'
    8 => '8'
    9 => '9'
    _ => abort("decimal digit outside 0..9")
  }
}

///|
fn write_decimal_escape(builder : StringBuilder, value : Int) -> Unit {
  builder.write_char('\\')
  builder.write_char(ascii_digit(value / 100))
  builder.write_char(ascii_digit(value / 10 % 10))
  builder.write_char(ascii_digit(value % 10))
}

///|
fn is_simple_atom(value : Bytes) -> Bool {
  if value.is_empty() {
    return false
  }
  for byte in value {
    let code = byte.to_int()
    if !((code >= 0x41 && code <= 0x5a) ||
      (code >= 0x61 && code <= 0x7a) ||
      (code >= 0x30 && code <= 0x39) ||
      code == 0x5f ||
      code == 0x2d) {
      return false
    }
  }
  true
}

///|
fn write_atom(builder : StringBuilder, value : Bytes) -> Unit {
  if is_simple_atom(value) {
    for byte in value {
      guard byte.to_int().to_char() is Some(char) else {
        abort("simple S-expression atom must be ASCII")
      }
      builder.write_char(char)
    }
    return
  }
  builder.write_char('"')
  for byte in value {
    let code = byte.to_int()
    match code {
      0x22 => builder.write_string("\\\"")
      0x5c => builder.write_string("\\\\")
      0x0a => builder.write_string("\\n")
      0x0d => builder.write_string("\\r")
      0x09 => builder.write_string("\\t")
      0x08 => builder.write_string("\\b")
      code if code >= 0x20 && code < 0x7f => {
        guard code.to_char() is Some(char) else {
          abort("printable S-expression atom byte must be ASCII")
        }
        builder.write_char(char)
      }
      code => write_decimal_escape(builder, code)
    }
  }
  builder.write_char('"')
}

// Encoding and Ptree-projection checks for pprint_whyml_sexp.

///|
test "sexp emitter: conservative simple atoms and structural spacing" {
  assert_eq(sexp_atom(b"abc-XYZ_09").render(), "abc-XYZ_09")
  assert_eq(sexp_atom(b"").render(), "\"\"")
  assert_eq(sexp_atom(b"a+b").render(), "\"a+b\"")
  assert_eq(
    sexp_list([sexp_atom(b"a"), sexp_list([sexp_atom(b"b"), sexp_atom(b"c")])]).render(),
    "(a (b c))",
  )
}

///|
test "sexp emitter: Why3 string escaping preserves every byte" {
  let bytes = Bytes::from_array([
    0x00, 0x08, 0x09, 0x0a, 0x0d, 0x1f, 0x20, 0x22, 0x5c, 0x7e, 0x7f, 0xa1, 0xff,
  ])
  assert_eq(
    sexp_atom(bytes).render(),
    "\"\\000\\b\\t\\n\\r\\031 \\\"\\\\~\\127\\161\\255\"",
  )
}

///|
test "sexp builder: options, records, and variants follow Sexplib shapes" {
  let absent : Int64? = None
  assert_eq(sexp_option(absent, sexp_int64).render(), "()")
  assert_eq(sexp_option(Some(7L), sexp_int64).render(), "(7)")
  assert_eq(sexp_variant("Ttrue", []).render(), "Ttrue")
  assert_eq(
    sexp_variant("Tapply", [sexp_atom(b"x"), sexp_atom(b"y")]).render(),
    "(Tapply x y)",
  )
  assert_eq(
    sexp_record([("id_str", sexp_atom(b"x")), ("id_ats", sexp_list([]))]).render(),
    "((id_str x) (id_ats ()))",
  )
}

///|
test "sexp emitter: Why3 hv boxes break every separator when over margin" {
  let long = sexp_atom(
    b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  )
  assert_eq(
    sexp_list([sexp_atom(b"head"), long, sexp_atom(b"tail")]).render(),
    (
      #|(head
      #|  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
      #|  tail)
    ),
  )
}

///|
test "Ptree projection: a position directive may change the end filename" {
  let source = b"goal g : true /\\ [## \"other.mlw\" 10 20] false"
  let file = @parser.parse_mlw_file(source, filename=b"before.mlw")
  assert_eq(
    sexp_of_mlw_file(file).render(),
    (
      #|(Decls
      #|  ((Dprop
      #|     Pgoal
      #|     ((id_str g) (id_ats ()) (id_loc ("before.mlw" 1 5 1 6)))
      #|     ((term_desc
      #|        (Tbinop
      #|          ((term_desc Ttrue) (term_loc ("before.mlw" 1 9 1 13)))
      #|          DTand
      #|          ((term_desc Tfalse) (term_loc ("other.mlw" 10 21 10 26)))))
      #|       (term_loc ("before.mlw" 1 9 10 26))))))
    ),
  )
}

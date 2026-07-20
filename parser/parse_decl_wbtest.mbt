///|
fn declaration_test_span(offset : Int) -> Span {
  let at = SourcePos::{
    filename: b"decl.mlw",
    byte_offset: offset,
    line: 1L,
    column: offset.to_int64(),
  }
  Span::empty(at)
}

///|
fn declaration_test_ident(name : Bytes, offset : Int) -> Ident {
  { name, attributes: [], span: declaration_test_span(offset) }
}

///|
test "AST common enums: every upstream constructor is representable" {
  assert_eq([DTand, DTandAsym, DTor, DTorAsym, DTimplies, DTiff, DTby, DTso], [
    DTand,
    DTandAsym,
    DTor,
    DTorAsym,
    DTimplies,
    DTiff,
    DTby,
    DTso,
  ])
  assert_eq([DTforall, DTexists, DTlambda], [DTforall, DTexists, DTlambda])
  assert_eq([RKnone, RKlocal, RKfunc, RKpred, RKlemma], [
    RKnone,
    RKlocal,
    RKfunc,
    RKpred,
    RKlemma,
  ])
  let assertion_kinds : Array[AssertionKind] = [Assert, Assume, Check]
  assert_eq(assertion_kinds, [Assert, Assume, Check])
  let for_directions : Array[ForDirection] = [To, DownTo]
  assert_eq(for_directions, [To, DownTo])
  assert_eq([MaskVisible, MaskTuple([MaskGhost]), MaskGhost], [
    MaskVisible,
    MaskTuple([MaskGhost]),
    MaskGhost,
  ])
  assert_eq([Ind, Coind], [Ind, Coind])
  assert_eq([Plemma, Paxiom, Pgoal], [Plemma, Paxiom, Pgoal])
  assert_eq([Public, Private, Abstract], [Public, Private, Abstract])
  let module_kinds : Array[ModuleKind] = [Theory, Module]
  assert_eq(module_kinds, [Theory, Module])
}

///|
test "AST declarations: exact numeric and arbitrary-byte payloads" {
  let span = declaration_test_span(0)
  let type_name = declaration_test_ident(b"bounded", 0)
  let type_decl = TypeDecl::{
    span,
    ident: type_name,
    params: [],
    visibility: Public,
    mutable: false,
    invariant: { terms: [] },
    witness: None,
    definition: TDrange(
      BigInt::from_string("-999999999999999999999999"),
      BigInt::from_string("999999999999999999999999"),
    ),
  }
  let meta = Dmeta(declaration_test_ident(b"meta\xff", 1), [
    Mstr(b"\xff"),
    Mint(OCAML_INT_MAX),
  ])
  let file = Decls([Dtype([type_decl]), meta])
  guard file
    is Decls(
      [Dtype([{ definition: TDrange(lower, upper), .. }]), Dmeta(_, args)]
    ) else {
    fail("unexpected declaration tree")
  }
  assert_eq(lower.to_string(), "-999999999999999999999999")
  assert_eq(upper.to_string(), "999999999999999999999999")
  assert_true(args[0] is Mstr(bytes) && bytes == b"\xff")
  assert_true(args[1] is Mint(4611686018427387903L))
}

///|
test "AST file: complete nested tree derives Debug and Eq" {
  assert_eq(MlwFile::empty(), Modules([]))
  let span = declaration_test_span(0)
  let x = declaration_test_ident(b"x", 1)
  let qx = Qident(x)
  let unit_type = PTtuple([])
  let wildcard = Pattern::{ desc: Pwild, span }
  let binder = Binder::{
    span,
    ident: Some(x),
    ghost: false,
    binder_type: Some(unit_type),
  }
  let truth = Term::{ desc: Ttrue, span }
  let spec = Spec::{
    preconditions: [truth],
    postconditions: [{ span, branches: [(wildcard, truth)] }],
    exceptional_postconditions: [
      { span, branches: [(qx, Some((wildcard, truth)))] },
    ],
    reads: [qx],
    writes: [truth],
    aliases: [(truth, truth)],
    variant: { items: [(truth, Some(qx))] },
    check_reads_writes: true,
    diverges: true,
    partial: true,
  }
  let body = Expr::{ desc: Econst(ConstStr(b"\xff")), span }
  let function_def = FunctionDef::{
    name: declaration_test_ident(b"f", 2),
    ghost: true,
    kind: RKlemma,
    binders: [binder],
    return_type: Some(unit_type),
    return_pattern: wildcard,
    mask: MaskTuple([MaskVisible, MaskGhost]),
    spec,
    body,
  }
  let module_name = declaration_test_ident(b"Implementation", 3)
  let interface = Qdot(
    Qident(declaration_test_ident(b"Library", 4)),
    declaration_test_ident(b"Interface", 5),
  )
  let module_ = MlwModule::{
    kind: Module,
    name: module_name,
    interface: Some(interface),
    declarations: [
      Drec([function_def]),
      Dprop(Plemma, declaration_test_ident(b"G", 6), truth),
      Dscope(span, true, declaration_test_ident(b"S", 7), [Duseexport(qx)]),
    ],
    span,
  }
  let file = Modules([module_])
  assert_eq(file, Modules([module_]))
  let rendered = to_repr(file).to_string()
  assert_true(rendered.has_prefix("Modules("))
}

///|
fn declaration_parse_error(input : BytesView) -> ParseDiagnostic {
  try parse_decl_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected declaration parser error")
  }
}

///|
fn parse_meta_decl_test(input : BytesView) -> Decl raise ParseError {
  let parser = Parser::new(input, filename=b"<meta-decl-test>")
  finish_internal_entry(parser, parser => parser.parse_meta_decl())
}

///|
fn parse_use_clone_decl_test(input : BytesView) -> Decl raise ParseError {
  let parser = Parser::new(input, filename=b"<use-clone-test>")
  finish_internal_entry(parser, parser => parser.parse_use_clone_decl())
}

///|
test "type declarations preserve algebraic parameters, visibility, and spans" {
  let declaration = parse_decl_entry(
    b"type tree 'a = private mutable | Leaf 'a | Node tree tree",
  )
  guard declaration is Dtype([type_declaration]) else {
    fail("expected one type declaration")
  }
  assert_eq(type_declaration.ident.name, b"tree")
  assert_eq(type_declaration.params.length(), 1)
  assert_eq(type_declaration.params[0].name, b"a")
  assert_true(type_declaration.visibility is Private)
  assert_true(type_declaration.mutable)
  guard type_declaration.definition is TDalgebraic([leaf, node]) else {
    fail("expected two algebraic cases")
  }
  assert_eq(leaf.ident.name, b"Leaf")
  assert_eq(leaf.params.length(), 1)
  assert_true(leaf.params[0].param_type is PTtyvar({ name: b"a", .. }))
  assert_eq(node.ident.name, b"Node")
  assert_eq(node.params.length(), 2)
  assert_eq(type_declaration.span.start.byte_offset, 5)
  assert_eq(type_declaration.span.end.byte_offset, 57)
}

///|
test "record fields retain mutable, ghost, and the two reference encodings" {
  let declaration = parse_decl_entry(
    b"type cell = abstract mutable { ghost mutable ref contents : int; &view : bool; plain : int } invariant Stable { true } by 0",
  )
  guard declaration is Dtype([type_declaration]) else {
    fail("expected record type declaration")
  }
  assert_true(type_declaration.visibility is Abstract)
  assert_true(type_declaration.mutable)
  guard type_declaration.definition is TDrecord([contents, view, plain]) else {
    fail("expected three record fields")
  }
  assert_true(contents.mutable)
  assert_true(contents.ghost)
  assert_true(
    contents.field_type is PTref([PTtyapp(Qident({ name: b"int", .. }), [])]),
  )
  assert_true(is_reference_ident(contents.ident))
  assert_false(view.mutable)
  assert_false(view.ghost)
  assert_true(view.field_type is PTtyapp(Qident({ name: b"bool", .. }), []))
  assert_true(is_reference_ident(view.ident))
  assert_false(is_reference_ident(plain.ident))
  assert_eq(type_declaration.invariant.terms.length(), 1)
  assert_true(
    type_declaration.witness is Some({ desc: Econst(ConstInt(_)), .. }),
  )
}

///|
test "unmodified record fields inherit the preceding delimiter end position" {
  let declaration = parse_decl_entry(b"type r = { x : int; y : int }")
  guard declaration is Dtype([{ definition: TDrecord([x, y]), .. }]) else {
    fail("expected two record fields")
  }
  assert_eq(x.span.start.byte_offset, 10)
  assert_eq(x.span.start.line, 1L)
  assert_eq(x.span.start.column, 10L)
  assert_eq(y.span.start.byte_offset, 19)
  assert_eq(y.span.start.line, 1L)
  assert_eq(y.span.start.column, 19L)
}

///|
test "abstract, scoped alias, range, and float type definitions are distinct" {
  assert_true(
    parse_decl_entry(b"type opaque")
    is Dtype([{ visibility: Abstract, definition: TDrecord([]), .. }]),
  )
  assert_true(
    parse_decl_entry(b"type renamed = private M.t")
    is Dtype(
      [
        {
          visibility: Private,
          definition: TDalias(
            PTtyapp(Qdot(Qident({ name: b"M", .. }), { name: b"t", .. }), [])
          ),
          ..,
        },
      ]
    ),
  )
  let numeric = parse_decl_entry(
    b"type bounded = < range -999999999999999999999 999999999999999999999 > with ieee = < float 11 53 >",
  )
  guard numeric is Dtype([bounded, ieee]) else {
    fail("expected range and float declarations")
  }
  guard bounded.definition is TDrange(lower, upper) else {
    fail("expected range type")
  }
  assert_eq(lower.to_string(), "-999999999999999999999")
  assert_eq(upper.to_string(), "999999999999999999999")
  assert_true(ieee.definition is TDfloat(11L, 53L))
}

///|
test "logic declarations enforce main forms and retain with-clause locations" {
  let constant = parse_decl_entry(b"constant zero : int = 0")
  assert_true(
    constant
    is Dlogic(
      [
        {
          ident: { name: b"zero", .. },
          params: [],
          return_type: Some(PTtyapp(Qident({ name: b"int", .. }), [])),
          definition: Some({ desc: Tconst(ConstInt(_)), .. }),
          ..,
        },
      ]
    ),
  )
  let function = parse_decl_entry(
    b"function f (x : int) : int = x with relation (x : int) = true",
  )
  guard function is Dlogic([first, second]) else {
    fail("expected a function group")
  }
  assert_eq(first.ident.name, b"f")
  assert_eq(first.params.length(), 1)
  assert_true(first.return_type is Some(_))
  assert_eq(second.ident.name, b"relation")
  assert_true(second.return_type is None)
  assert_eq(second.span.start.byte_offset, 31)
  assert_eq(second.span.end.byte_offset, 61)
  assert_true(
    parse_decl_entry(b"predicate p (x : int) = true")
    is Dlogic(
      [{ return_type: None, definition: Some({ desc: Ttrue, .. }), .. }]
    ),
  )
  assert_true(
    declaration_parse_error(b"constant bad x : int").kind is UnexpectedToken,
  )
  assert_true(
    declaration_parse_error(b"predicate bad : int").kind is UnexpectedToken,
  )
}

///|
test "inductive groups and proposition kinds retain exact declaration data" {
  let declaration = parse_decl_entry(
    b"inductive even int = Zero : true | Step : true with odd int = Odd : true",
  )
  guard declaration is Dind(Ind, [even, odd]) else {
    fail("expected mutually inductive declarations")
  }
  assert_eq(even.ident.name, b"even")
  assert_eq(even.params.length(), 1)
  assert_eq(even.cases.length(), 2)
  assert_eq(even.cases[0].ident.name, b"Zero")
  assert_eq(odd.cases.length(), 1)
  assert_true(
    parse_decl_entry(b"coinductive stream int")
    is Dind(Coind, [{ cases: [], .. }]),
  )
  guard parse_decl_entry(b"axiom Sound : true") is Dprop(Paxiom, axiom, _) else {
    fail("expected axiom")
  }
  assert_true(
    axiom.attributes is [Text(attribute)] && attribute == user_axiom_attribute,
  )
  assert_true(parse_decl_entry(b"lemma L : true") is Dprop(Plemma, _, _))
  assert_true(parse_decl_entry(b"goal G : true") is Dprop(Pgoal, _, _))
}

///|
test "program declarations distinguish routines, constants, references, and recursion" {
  let declared = parse_decl_entry(
    b"val function f (x : int) : int requires { true }",
  )
  guard declared is Dlet({ name: b"f", .. }, false, RKfunc, any) else {
    fail("expected declared function")
  }
  assert_true(
    any.desc is Eany([_], RKnone, Some(_), { desc: Pwild, .. }, MaskVisible, _),
  )
  assert_true(
    parse_decl_entry(b"val ghost predicate p (x : int)")
    is Dlet(
      { name: b"p", .. },
      true,
      RKpred,
      { desc: Eany([_], _, _, _, _, _), .. }
    ),
  )
  let reference = parse_decl_entry(b"val ref state : int")
  guard reference is Dlet(name, false, RKnone, value) else {
    fail("expected reference declaration")
  }
  assert_true(is_reference_ident(name))
  assert_true(
    value.desc
    is Eapply({ desc: Eref, .. }, { desc: Eany([], _, _, _, _, _), .. }),
  )
  let symbolic = parse_decl_entry(b"let &slot : int = 1")
  guard symbolic is Dlet(slot, false, RKnone, slot_value) else {
    fail("expected symbolic constant definition")
  }
  assert_true(is_reference_ident(slot))
  assert_true(slot_value.desc is Ecast(_, _))
  let recursive = parse_decl_entry(
    b"let rec f (x : int) : int = x with partial g (y : int) : int = y",
  )
  guard recursive is Drec([f, g]) else {
    fail("expected recursive declaration group")
  }
  assert_eq(f.name.name, b"f")
  assert_false(f.spec.partial)
  assert_eq(g.name.name, b"g")
  assert_true(g.spec.partial)
  assert_true(
    declaration_parse_error(b"val function ref x : int").kind is UnexpectedToken,
  )
  assert_true(declaration_parse_error(b"let &x y = y").kind is UnexpectedToken)
}

///|
test "exception declarations cover omitted, ghost, and mixed return masks" {
  assert_true(
    parse_decl_entry(b"exception Empty")
    is Dexn({ name: b"Empty", .. }, PTtuple([]), MaskVisible),
  )
  assert_true(
    parse_decl_entry(b"exception Hidden ghost int")
    is Dexn({ name: b"Hidden", .. }, PTtyapp(_, []), MaskGhost),
  )
  assert_true(
    parse_decl_entry(b"exception Mixed (int, ghost bool)")
    is Dexn(_, PTtuple([_, _]), MaskTuple([MaskVisible, MaskGhost])),
  )
}

///|
test "meta declarations preserve every argument category and checked integers" {
  assert_true(parse_meta_decl_test(b"meta empty()") is Dmeta(_, []))
  assert_true(parse_meta_decl_test(b"meta \"x\" ()") is Dmeta(_, []))
  let declaration = parse_meta_decl_test(
    b"meta \"raw\" type int, constant c, function f, predicate p, axiom A, lemma L, goal G, val v, \"bytes\", 4611686018427387903",
  )
  guard declaration
    is Dmeta(
      { name: b"raw", .. },
      [
        Mty(_),
        Mfs(_),
        Mfs(_),
        Mps(_),
        Max(_),
        Mlm(_),
        Mgl(_),
        Mval(_),
        Mstr(bytes),
        Mint(maximum),
      ]
    ) else {
    fail("expected complete meta argument list")
  }
  assert_eq(bytes, b"bytes")
  assert_eq(maximum, OCAML_INT_MAX)
  guard parse_meta_decl_test(b"meta \"\\xFF\" \"\\xFF\"")
    is Dmeta({ name, .. }, [Mstr(payload)]) else {
    fail("expected arbitrary-byte meta name and argument")
  }
  assert_eq(name, b"\xff")
  assert_eq(payload, b"\xff")
  let parenthesized = Parser::new(b"meta m(type int)")
  let parenthesized_error = try
    finish_internal_entry(parenthesized, parser => parser.parse_meta_decl())
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected parenthesized meta argument error")
  }
  assert_true(parenthesized_error.kind is UnexpectedToken)
  let overflowing = Parser::new(b"meta m 4611686018427387904")
  let overflow_error = try
    finish_internal_entry(overflowing, parser => parser.parse_meta_decl())
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected meta integer overflow")
  }
  assert_true(overflow_error.kind is NumericOverflow)
}

///|
test "clone substitutions cover implicit, explicit, symbol, and proposition forms" {
  let declaration = parse_use_clone_decl_test(
    b"clone export Source with type t 'a = list 'a, type u, constant c = d, function f, predicate p = q, val x = y, exception E = F, axiom A, lemma ., goal G",
  )
  guard declaration is Dcloneexport(_, path, substitutions) else {
    fail("expected clone export")
  }
  assert_eq(path.last_ident().name, b"Source")
  assert_eq(substitutions.length(), 10)
  assert_true(substitutions[0] is CStsym(_, [{ name: b"a", .. }], _))
  assert_true(
    substitutions[1] is CStsym(source, [], PTtyapp(target, [])) &&
    source == target,
  )
  assert_true(substitutions[2] is CSfsym(_, _))
  assert_true(substitutions[3] is CSfsym(source, target) && source == target)
  assert_true(substitutions[4] is CSpsym(_, _))
  assert_true(substitutions[5] is CSvsym(_, _))
  assert_true(substitutions[6] is CSxsym(_, _))
  assert_true(substitutions[7] is CSaxiom(_))
  assert_true(substitutions[8] is CSprop(Plemma))
  assert_true(substitutions[9] is CSgoal(_))
  let bad = Parser::new(b"clone export M with type t 'a")
  let diagnostic = try
    finish_internal_entry(bad, parser => parser.parse_use_clone_decl())
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected malformed clone substitution")
  }
  assert_true(diagnostic.kind is UnexpectedEof)
  let proposition_rhs = Parser::new(b"clone export M with axiom A = B")
  let proposition_error = try
    finish_internal_entry(proposition_rhs, parser => {
      parser.parse_use_clone_decl()
    })
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected proposition substitution RHS error")
  }
  assert_true(proposition_error.kind is UnexpectedToken)
}

///|
test "use and clone declaration variants retain import and renaming flags" {
  assert_true(
    parse_use_clone_decl_test(b"use export Library")
    is Duseexport(Qident({ name: b"Library", .. })),
  )
  let used = parse_use_clone_decl_test(b"use import A as Local, B")
  guard used is Duseimport(_, true, [(a, Some(renaming)), (b, None)]) else {
    fail("expected imported use list")
  }
  assert_eq(a.last_ident().name, b"A")
  assert_eq(renaming.name, b"Local")
  assert_eq(b.last_ident().name, b"B")
  let cloned = parse_use_clone_decl_test(
    b"clone import Source as Local with val source = target",
  )
  guard cloned
    is Dcloneimport(_, true, source, Some(renaming), [CSvsym(from, to)]) else {
    fail("expected imported clone")
  }
  assert_eq(source.last_ident().name, b"Source")
  assert_eq(renaming.name, b"Local")
  assert_eq(from.last_ident().name, b"source")
  assert_eq(to.last_ident().name, b"target")
}

///|
fn mlw_file_parse_error(input : BytesView) -> ParseDiagnostic {
  try parse_mlw_file_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected WhyML file parser error")
  }
}

///|
test "file state starts empty and preserves multiple module head extensions" {
  assert_eq(parse_mlw_file_entry(b""), Modules([]))
  let source = b"theory T [@tag] end module M : Library.Interface end"
  let file = parse_mlw_file_entry(source, filename=b"modules.mlw")
  guard file is Modules([theory, module_]) else {
    fail("expected theory and module")
  }
  assert_true(theory.kind is Theory)
  assert_eq(theory.name.name, b"T")
  assert_true(
    theory.name.attributes is [Text(attribute)] && attribute == b"tag",
  )
  assert_true(theory.interface is None)
  assert_eq(theory.declarations, [])
  assert_eq(theory.span.start.byte_offset, 0)
  assert_eq(theory.span.end.byte_offset, 19)
  assert_eq(theory.span.start.filename, b"modules.mlw")
  assert_true(module_.kind is Module)
  assert_eq(module_.name.name, b"M")
  guard module_.interface is Some(interface) else {
    fail("expected module interface")
  }
  assert_eq(interface.last_ident().name, b"Interface")
  assert_eq(module_.span.start.byte_offset, 20)
  assert_eq(module_.span.end.byte_offset, source.length())
}

///|
test "module declarations include imports, use, meta, pure, program, and scopes" {
  let source = b"module M scope import S [@head] import A.B use export C meta m() type t = int val x : int scope N end end exception E end"
  let file = parse_mlw_file_entry(source)
  guard file is Modules([{ declarations, .. }]) else {
    fail("expected one module")
  }
  guard declarations
    is [
      Dscope(scope_span, true, scope_name, scope_declarations),
      Dexn(_, PTtuple([]), MaskVisible),
    ] else {
    fail("expected outer scope and exception")
  }
  assert_eq(scope_name.name, b"S")
  assert_true(scope_name.attributes is [Text(name)] && name == b"head")
  assert_eq(scope_span.start.byte_offset, 9)
  assert_eq(scope_span.end.byte_offset, 31)
  assert_true(
    scope_declarations
    is [
      Dimport(_),
      Duseexport(_),
      Dmeta(_, []),
      Dtype([_]),
      Dlet(_, false, RKnone, _),
      Dscope(_, false, { name: b"N", .. }, []),
    ],
  )
}

///|
test "a valueless return stops before the following let declaration" {
  let file = parse_mlw_file_entry(
    b"module M\nlet f () = return\nlet g () = ()\nend",
  )
  guard file
    is Modules(
      [
        {
          declarations: [
            Dlet({ name: b"f", .. }, false, RKnone, _),
            Dlet({ name: b"g", .. }, false, RKnone, _),
          ],
          ..,
        },
      ]
    ) else {
    fail("expected two independent let declarations")
  }
}

///|
test "a leading declaration selects top-level Decls mode" {
  let file = parse_mlw_file_entry(
    b"import A.B scope S use import C as D end meta m() let value = 1",
  )
  guard file
    is Decls(
      [
        Dimport(path),
        Dscope(_, false, _, [Duseimport(_, true, [_])]),
        Dmeta(_, []),
        Dlet(_, false, RKnone, _),
      ]
    ) else {
    fail("expected top-level declaration file")
  }
  assert_eq(path.last_ident().name, b"B")
  assert_true(mlw_file_parse_error(b"import A.value").kind is UnexpectedToken)
}

///|
test "file mode switches and direct module nesting report NestedModule" {
  let after_module = mlw_file_parse_error(b"module M end type t = int")
  assert_true(after_module.kind is NestedModule)
  assert_eq(after_module.span.start.byte_offset, 13)
  assert_eq(after_module.span.end.byte_offset, 25)
  let scope_after_module = mlw_file_parse_error(b"module M end scope S end")
  assert_true(scope_after_module.kind is NestedModule)
  assert_eq(scope_after_module.span.start.byte_offset, 13)
  assert_eq(scope_after_module.span.end.byte_offset, 18)
  let after_declaration = mlw_file_parse_error(b"type t module M end")
  assert_true(after_declaration.kind is NestedModule)
  assert_eq(after_declaration.span.start.byte_offset, 7)
  assert_eq(after_declaration.span.end.byte_offset, 13)
  let direct = mlw_file_parse_error(b"module A theory B end end")
  assert_true(direct.kind is NestedModule)
  assert_eq(direct.span.start.byte_offset, 9)
  assert_eq(direct.span.end.byte_offset, 15)
}

///|
test "modules inside scopes stay ordinary syntax errors and missing end is EOF" {
  let scoped = mlw_file_parse_error(b"scope S theory T end end")
  assert_true(scoped.kind is UnexpectedToken)
  assert_eq(scoped.span.start.byte_offset, 8)
  assert_eq(scoped.span.end.byte_offset, 14)
  let missing = mlw_file_parse_error(b"module M type t = int")
  assert_true(missing.kind is UnexpectedEof)
  assert_true(missing.expected.contains("end"))
  assert_true(
    mlw_file_parse_error(b"theory T : Interface end").kind is UnexpectedToken,
  )
}

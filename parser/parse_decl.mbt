// Pure, program, meta, use, and clone declaration grammar productions.

///|
fn starts_pure_decl(parser : Parser) -> Bool {
  parser.at_keyword(Type) ||
  parser.at_keyword(Constant) ||
  parser.at_keyword(Function) ||
  parser.at_keyword(Predicate) ||
  parser.at_keyword(Inductive) ||
  parser.at_keyword(Coinductive) ||
  parser.at_keyword(Axiom) ||
  parser.at_keyword(Lemma) ||
  parser.at_keyword(Goal)
}

///|
fn starts_prog_decl(parser : Parser) -> Bool {
  parser.at_keyword(Val) ||
  parser.at_keyword(Let) ||
  parser.at_keyword(Exception)
}

///|
fn Parser::parse_type_variable(self : Parser) -> Ident raise {
  parse_attrs_ident(self, parser => parser.parse_quote_lident())
}

///|
fn Parser::parse_visibility_mutability(
  self : Parser,
) -> (Visibility, Bool) raise {
  let mut visibility = Visibility::Public
  let mut mutable = false
  if self.consume_keyword(Mutable) is Some(_) {
    mutable = true
    if self.consume_keyword(Private) is Some(_) {
      visibility = Private
    } else if self.consume_keyword(Abstract) is Some(_) {
      visibility = Abstract
    }
    return (visibility, mutable)
  }
  if self.consume_keyword(Private) is Some(_) {
    visibility = Private
    mutable = self.consume_keyword(Mutable) is Some(_)
  } else if self.consume_keyword(Abstract) is Some(_) {
    visibility = Abstract
    mutable = self.consume_keyword(Mutable) is Some(_)
  }
  (visibility, mutable)
}

///|
fn Parser::parse_signed_bigint(self : Parser) -> BigInt raise {
  let negative = self.consume_symbol(Minus) is Some(_)
  let token = self.peek()
  guard token.kind is Integer(constant) else {
    self.fail_syntax("integer literal")
  }
  ignore(self.advance())
  if negative {
    -constant.value
  } else {
    constant.value
  }
}

///|
fn Parser::parse_type_field_modifiers(self : Parser) -> (Bool, Bool) raise {
  let mut mutable = false
  let mut ghost = false
  if self.consume_keyword(Ghost) is Some(_) {
    ghost = true
    mutable = self.consume_keyword(Mutable) is Some(_)
  } else if self.consume_keyword(Mutable) is Some(_) {
    mutable = true
    ghost = self.consume_keyword(Ghost) is Some(_)
  }
  (mutable, ghost)
}

///|
fn Parser::parse_type_field_name(self : Parser) -> (Bool, Ident) raise {
  if self.consume_keyword(Ref) is Some(_) {
    if self.consume_symbol(Amp) is Some(_) {
      let ident = parse_attrs_ident(self, parser => {
        parser.parse_lident(true, false)
      })
      return fail_binder_semantic(DoubleReference, ident.span)
    }
    let ident = parse_attrs_ident(self, parser => {
      parser.parse_lident(true, false)
    })
    return (true, set_reference(ident))
  }
  if self.consume_symbol(Amp) is Some(_) {
    let ident = parse_attrs_ident(self, parser => {
      parser.parse_lident(true, false)
    })
    return (false, set_reference(ident))
  }
  (false, parse_attrs_ident(self, parser => parser.parse_lident(true, false)))
}

///|
fn Parser::parse_type_field(self : Parser) -> Field raise {
  let mark = self.mark()
  // `field_modifiers` is inlined in the upstream grammar. Its empty branch
  // inherits the end position of the preceding `{` or `;`.
  let inherited_start = if !self.at_keyword(Ghost) && !self.at_keyword(Mutable) {
    Some(self.empty_span_at_cursor())
  } else {
    None
  }
  let (mutable, ghost) = self.parse_type_field_modifiers()
  let (wrap_reference, ident) = self.parse_type_field_name()
  let field_type = self.parse_cast()
  let span = self.span_from(mark)
  {
    span: if inherited_start is Some(start) {
      start.join(span)
    } else {
      span
    },
    ident,
    field_type: if wrap_reference {
      PTref([field_type])
    } else {
      field_type
    },
    mutable,
    ghost,
  }
}

///|
fn starts_type_field(parser : Parser) -> Bool {
  parser.at_keyword(Mutable) ||
  parser.at_keyword(Ghost) ||
  parser.at_keyword(Ref) ||
  parser.at_symbol(Amp) ||
  starts_plain_lident_kind(parser.peek_kind_n(0), false)
}

///|
fn Parser::parse_record_type_definition(self : Parser) -> TypeDef raise {
  ignore(self.expect_symbol(LeftBrc))
  if self.consume_symbol(RightBrc) is Some(_) {
    return TDrecord([])
  }
  let fields = parse_semicolon_list1(
    self,
    parser => starts_type_field(parser),
    parser => parser.parse_type_field(),
    expected="record type field",
  )
  ignore(self.expect_symbol(RightBrc))
  TDrecord(fields)
}

///|
fn Parser::parse_algebraic_case(self : Parser) -> AlgebraicCase raise {
  let mark = self.mark()
  let ident = parse_attrs_ident(self, parser => parser.parse_uident(true))
  let params = self.parse_params(false)
  { span: self.span_from(mark), ident, params }
}

///|
fn Parser::parse_algebraic_type_definition(self : Parser) -> TypeDef raise {
  TDalgebraic(
    parse_bar_list1(
      self,
      parser => starts_uident_kind(parser.peek_kind_n(0)),
      parser => parser.parse_algebraic_case(),
      expected="algebraic type case",
    ),
  )
}

///|
fn Parser::parse_type_definition(
  self : Parser,
) -> ((Visibility, Bool), TypeDef) raise {
  guard self.consume_symbol(Equal) is Some(_) else {
    return ((Abstract, false), TDrecord([]))
  }
  if self.consume_symbol(Lt) is Some(_) {
    if self.consume_keyword(Range) is Some(_) {
      let lower = self.parse_signed_bigint()
      let upper = self.parse_signed_bigint()
      ignore(self.expect_symbol(Gt))
      return ((Public, false), TDrange(lower, upper))
    }
    ignore(self.expect_keyword(Float))
    let significand_token = self.peek()
    guard significand_token.kind is Integer(significand) else {
      self.fail_syntax("integer literal")
    }
    ignore(self.advance())
    let exponent_token = self.peek()
    guard exponent_token.kind is Integer(exponent) else {
      self.fail_syntax("integer literal")
    }
    ignore(self.advance())
    ignore(self.expect_symbol(Gt))
    return (
      (Public, false),
      TDfloat(
        checked_ocaml_int(significand.value, significand_token.span),
        checked_ocaml_int(exponent.value, exponent_token.span),
      ),
    )
  }
  let modifiers = self.parse_visibility_mutability()
  if self.at_symbol(Bar) ||
    (
      starts_uident_kind(self.peek_kind_n(0)) &&
      !(self.peek_kind_n(1) is Some(Symbol(Dot)))
    ) {
    return (modifiers, self.parse_algebraic_type_definition())
  }
  if self.at_symbol(LeftBrc) {
    let definition = parse_alternative(
      self,
      parser => parser.parse_record_type_definition(),
      parser => TDalias(parser.parse_ty()),
    )
    return (modifiers, definition)
  }
  (modifiers, TDalias(self.parse_ty()))
}

///|
fn Parser::parse_type_decl(self : Parser) -> TypeDecl raise {
  let mark = self.mark()
  let ident = parse_attrs_ident(self, parser => parser.parse_lident(true, false))
  let params : Array[Ident] = []
  while self.peek_kind_n(0) is Some(QuoteLident(_)) {
    params.push(self.parse_type_variable())
  }
  let ((visibility, mutable), definition) = self.parse_type_definition()
  let invariants : Array[Term] = []
  while self.at_keyword(Invariant) {
    invariants.push(self.parse_type_invariant())
  }
  let witness = if self.consume_keyword(By) is Some(_) {
    Some(self.parse_expr())
  } else {
    None
  }
  {
    span: self.span_from(mark),
    ident,
    params,
    visibility,
    mutable,
    invariant: { terms: invariants },
    witness,
    definition,
  }
}

///|
fn Parser::parse_type_declaration(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Type))
  let declarations : Array[TypeDecl] = [self.parse_type_decl()]
  while self.consume_keyword(With) is Some(_) {
    declarations.push(self.parse_type_decl())
  }
  Dtype(declarations)
}

///|
fn Parser::parse_optional_term_definition(self : Parser) -> Term? raise {
  if self.consume_symbol(Equal) is Some(_) {
    Some(self.parse_term())
  } else {
    None
  }
}

///|
fn Parser::parse_logic_decl(
  self : Parser,
  allow_params : Bool,
  return_required : Bool,
  allow_return : Bool,
) -> LogicDecl raise {
  let mark = self.mark()
  let ident = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let params = if allow_params { self.parse_params(false) } else { [] }
  if !allow_return && self.at_symbol(Colon) {
    self.fail_syntax("predicate definition")
  }
  let return_type = if self.at_symbol(Colon) {
    Some(self.parse_cast())
  } else {
    None
  }
  if return_required && return_type is None {
    self.fail_syntax("return type")
  }
  let definition = self.parse_optional_term_definition()
  { span: self.span_from(mark), ident, params, return_type, definition }
}

///|
fn Parser::parse_logic_declaration(
  self : Parser,
  keyword : Keyword,
) -> Decl raise {
  ignore(self.expect_keyword(keyword))
  let return_required = keyword is (Constant | Function)
  let allow_return = !(keyword is Predicate)
  let declarations : Array[LogicDecl] = [
    self.parse_logic_decl(!(keyword is Constant), return_required, allow_return),
  ]
  if keyword is (Function | Predicate) {
    while self.at_keyword(With) {
      let with_mark = self.mark()
      ignore(self.advance())
      let declaration = self.parse_logic_decl(true, false, true)
      declarations.push({ ..declaration, span: self.span_from(with_mark) })
    }
  }
  Dlogic(declarations)
}

///|
fn Parser::parse_inductive_case(self : Parser) -> InductiveCase raise {
  let mark = self.mark()
  let ident = parse_attrs_ident(self, parser => parser.parse_ident_nq())
  ignore(self.expect_symbol(Colon))
  let body = self.parse_term()
  { span: self.span_from(mark), ident, body }
}

///|
fn Parser::parse_inductive_decl(self : Parser) -> InductiveDecl raise {
  let mark = self.mark()
  let ident = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let params = self.parse_params(false)
  let cases = if self.consume_symbol(Equal) is Some(_) {
    parse_bar_list1(
      self,
      parser => starts_ident(parser),
      parser => parser.parse_inductive_case(),
      expected="inductive case",
    )
  } else {
    []
  }
  { span: self.span_from(mark), ident, params, cases }
}

///|
fn Parser::parse_inductive_declaration(
  self : Parser,
  sign : InductiveSign,
) -> Decl raise {
  ignore(self.advance())
  let declarations = parse_with_list1(
    self,
    parser => {
      parser.at_symbol(LeftPar) ||
      starts_plain_lident_kind(parser.peek_kind_n(0), false)
    },
    parser => parser.parse_inductive_decl(),
    expected="lowercase identifier",
  )
  Dind(sign, declarations)
}

///|
fn Parser::parse_proposition_declaration(
  self : Parser,
  kind : PropositionKind,
) -> Decl raise {
  ignore(self.advance())
  let ident = parse_attrs_ident(self, parser => parser.parse_ident_nq())
  let ident = if kind is Paxiom {
    { ..ident, attributes: [Text(user_axiom_attribute)] + ident.attributes }
  } else {
    ident
  }
  ignore(self.expect_symbol(Colon))
  Dprop(kind, ident, self.parse_term())
}

///|
fn Parser::parse_pure_decl(self : Parser) -> Decl raise {
  if self.at_keyword(Type) {
    return self.parse_type_declaration()
  }
  if self.at_keyword(Constant) {
    return self.parse_logic_declaration(Constant)
  }
  if self.at_keyword(Function) {
    return self.parse_logic_declaration(Function)
  }
  if self.at_keyword(Predicate) {
    return self.parse_logic_declaration(Predicate)
  }
  if self.at_keyword(Inductive) {
    return self.parse_inductive_declaration(Ind)
  }
  if self.at_keyword(Coinductive) {
    return self.parse_inductive_declaration(Coind)
  }
  if self.at_keyword(Axiom) {
    return self.parse_proposition_declaration(Paxiom)
  }
  if self.at_keyword(Lemma) {
    return self.parse_proposition_declaration(Plemma)
  }
  if self.at_keyword(Goal) {
    return self.parse_proposition_declaration(Pgoal)
  }
  self.fail_syntax("pure declaration")
}

///|
fn Parser::parse_prog_val_decl(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Val))
  let partiality = self.parse_partiality()
  if self.consume_keyword(Ref) is Some(reference_token) {
    let name = self.parse_ref_binder()
    let value = self.parse_constant_declaration()
    let reference = make_expr(Eref, reference_token.span)
    let allocated = { ..value, desc: Eapply(reference, value) }
    return Dlet(
      name,
      partiality.is_ghost(),
      RKnone,
      apply_partial_expr(partiality, allocated),
    )
  }
  let kind = self.parse_routine_kind()
  if self.at_symbol(Amp) {
    let name = self.parse_sym_binder()
    let declaration = self.parse_constant_declaration()
    return Dlet(
      name,
      partiality.is_ghost(),
      kind,
      apply_partial_expr(partiality, declaration),
    )
  }
  let name = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let declaration = if starts_binder_or_param(self) && !self.at_symbol(Colon) {
    self.parse_function_declaration()
  } else {
    self.parse_constant_declaration()
  }
  Dlet(
    name,
    partiality.is_ghost(),
    kind,
    apply_partial_expr(partiality, declaration),
  )
}

///|
fn Parser::parse_prog_let_decl(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Let))
  if self.consume_keyword(Rec) is Some(_) {
    let definitions : Array[FunctionDef] = [self.parse_rec_definition()]
    while self.consume_keyword(With) is Some(_) {
      definitions.push(self.parse_rec_definition())
    }
    return Drec(definitions)
  }
  let partiality = self.parse_partiality()
  if self.consume_keyword(Ref) is Some(reference_token) {
    let name = self.parse_ref_binder()
    let value = self.parse_constant_definition()
    let reference = make_expr(Eref, reference_token.span)
    let allocated = { ..value, desc: Eapply(reference, value) }
    return Dlet(
      name,
      partiality.is_ghost(),
      RKnone,
      apply_partial_expr(partiality, allocated),
    )
  }
  let kind = self.parse_routine_kind()
  if self.at_symbol(Amp) {
    let name = self.parse_sym_binder()
    let value = self.parse_constant_definition()
    return Dlet(
      name,
      partiality.is_ghost(),
      kind,
      apply_partial_expr(partiality, value),
    )
  }
  let name = parse_attrs_ident(self, parser => parser.parse_lident_rich())
  let value = if starts_binder_or_param(self) {
    self.parse_function_definition()
  } else {
    self.parse_constant_definition()
  }
  Dlet(name, partiality.is_ghost(), kind, apply_partial_expr(partiality, value))
}

///|
fn Parser::parse_prog_exception_decl(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Exception))
  let name = parse_attrs_ident(self, parser => parser.parse_uident(true))
  if !starts_ty_arg(self) && !self.at_keyword(Ghost) {
    return Dexn(name, PTtuple([]), MaskVisible)
  }
  let info = self.parse_generic_return()
  Dexn(name, info.return_type, info.mask)
}

///|
fn Parser::parse_prog_decl(self : Parser) -> Decl raise {
  if self.at_keyword(Val) {
    return self.parse_prog_val_decl()
  }
  if self.at_keyword(Let) {
    return self.parse_prog_let_decl()
  }
  if self.at_keyword(Exception) {
    return self.parse_prog_exception_decl()
  }
  self.fail_syntax("program declaration")
}

///|
fn Parser::parse_meta_arg(self : Parser) -> MetaArg raise {
  if self.consume_keyword(Type) is Some(_) {
    return Mty(self.parse_ty())
  }
  if self.consume_keyword(Constant) is Some(_) ||
    self.consume_keyword(Function) is Some(_) {
    return Mfs(self.parse_qualid())
  }
  if self.consume_keyword(Predicate) is Some(_) {
    return Mps(self.parse_qualid())
  }
  if self.consume_keyword(Axiom) is Some(_) {
    return Max(self.parse_qualid())
  }
  if self.consume_keyword(Lemma) is Some(_) {
    return Mlm(self.parse_qualid())
  }
  if self.consume_keyword(Goal) is Some(_) {
    return Mgl(self.parse_qualid())
  }
  if self.consume_keyword(Val) is Some(_) {
    return Mval(self.parse_qualid())
  }
  let token = self.peek()
  match token.kind {
    StringToken(bytes) => {
      ignore(self.advance())
      Mstr(bytes)
    }
    Integer(constant) => {
      ignore(self.advance())
      Mint(checked_ocaml_int(constant.value, token.span))
    }
    _ => self.fail_syntax("meta argument")
  }
}

///|
fn starts_meta_arg(parser : Parser) -> Bool {
  parser.at_keyword(Type) ||
  parser.at_keyword(Constant) ||
  parser.at_keyword(Function) ||
  parser.at_keyword(Predicate) ||
  parser.at_keyword(Axiom) ||
  parser.at_keyword(Lemma) ||
  parser.at_keyword(Goal) ||
  parser.at_keyword(Val) ||
  parser.peek_kind_n(0) is Some(StringToken(_) | Integer(_))
}

///|
fn Parser::parse_meta_decl(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Meta))
  let (name, _) = self.parse_sident()
  if self.consume_symbol(LeftPar) is Some(_) {
    ignore(self.expect_symbol(RightPar))
    return Dmeta(name, [])
  }
  let arguments = parse_comma_list1(
    self,
    parser => starts_meta_arg(parser),
    parser => parser.parse_meta_arg(),
    expected="meta argument",
  )
  Dmeta(name, arguments)
}

///|
fn Parser::parse_clone_type_substitution(
  self : Parser,
) -> CloneSubstitution raise {
  let source = self.parse_qualid()
  let variables : Array[Ident] = []
  while self.peek_kind_n(0) is Some(QuoteLident(_)) {
    variables.push(self.parse_type_variable())
  }
  if self.consume_symbol(Equal) is Some(_) {
    CStsym(source, variables, self.parse_ty())
  } else {
    if !variables.is_empty() {
      self.fail_syntax("`=` after clone type parameters")
    }
    CStsym(source, [], PTtyapp(source, []))
  }
}

///|
fn Parser::parse_clone_symbol_substitution(
  self : Parser,
  keyword : Keyword,
) -> CloneSubstitution raise {
  ignore(self.expect_keyword(keyword))
  let source = self.parse_qualid()
  let target = if self.consume_symbol(Equal) is Some(_) {
    self.parse_qualid()
  } else {
    source
  }
  match keyword {
    Constant | Function => CSfsym(source, target)
    Predicate => CSpsym(source, target)
    Val => CSvsym(source, target)
    Exception => CSxsym(source, target)
    _ => abort("unexpected clone symbol substitution keyword")
  }
}

///|
fn Parser::parse_clone_proposition_substitution(
  self : Parser,
  keyword : Keyword,
) -> CloneSubstitution raise {
  ignore(self.expect_keyword(keyword))
  let kind = match keyword {
    Axiom => Paxiom
    Lemma => Plemma
    Goal => Pgoal
    _ => abort("unexpected clone proposition keyword")
  }
  if self.consume_symbol(Dot) is Some(_) {
    return CSprop(kind)
  }
  let source = self.parse_qualid()
  match kind {
    Paxiom => CSaxiom(source)
    Plemma => CSlemma(source)
    Pgoal => CSgoal(source)
  }
}

///|
fn starts_clone_substitution(parser : Parser) -> Bool {
  parser.at_keyword(Type) ||
  parser.at_keyword(Constant) ||
  parser.at_keyword(Function) ||
  parser.at_keyword(Predicate) ||
  parser.at_keyword(Val) ||
  parser.at_keyword(Exception) ||
  parser.at_keyword(Axiom) ||
  parser.at_keyword(Lemma) ||
  parser.at_keyword(Goal)
}

///|
fn Parser::parse_single_clone_substitution(
  self : Parser,
) -> CloneSubstitution raise {
  if self.consume_keyword(Type) is Some(_) {
    return self.parse_clone_type_substitution()
  }
  let token = self.peek()
  match token.kind {
    Keyword(keyword) if keyword
      is (Constant | Function | Predicate | Val | Exception) =>
      self.parse_clone_symbol_substitution(keyword)
    Keyword(keyword) if keyword is (Axiom | Lemma | Goal) =>
      self.parse_clone_proposition_substitution(keyword)
    _ => self.fail_syntax("clone substitution")
  }
}

///|
fn Parser::parse_clone_substitutions(
  self : Parser,
) -> Array[CloneSubstitution] raise {
  guard self.consume_keyword(With) is Some(_) else { return [] }
  parse_comma_list1(
    self,
    parser => starts_clone_substitution(parser),
    parser => parser.parse_single_clone_substitution(),
    expected="clone substitution",
  )
}

///|
fn Parser::parse_use_as(self : Parser) -> (QualId, Ident?) raise {
  let path = self.parse_tqualid()
  let renaming = if self.consume_keyword(As) is Some(_) {
    Some(self.parse_uident(false))
  } else {
    None
  }
  (path, renaming)
}

///|
fn Parser::parse_use_clone_decl(self : Parser) -> Decl raise {
  let mark = self.mark()
  if self.consume_keyword(Use) is Some(_) {
    if self.consume_keyword(Export) is Some(_) {
      return Duseexport(self.parse_tqualid())
    }
    let is_import = self.consume_keyword(Import) is Some(_)
    let modules = parse_comma_list1(
      self,
      parser => {
        starts_ident(parser) || parser.peek_kind_n(0) is Some(StringToken(_))
      },
      parser => parser.parse_use_as(),
      expected="module use",
    )
    return Duseimport(self.span_from(mark), is_import, modules)
  }
  ignore(self.expect_keyword(Clone))
  if self.consume_keyword(Export) is Some(_) {
    let path = self.parse_tqualid()
    let substitutions = self.parse_clone_substitutions()
    return Dcloneexport(self.span_from(mark), path, substitutions)
  }
  let is_import = self.consume_keyword(Import) is Some(_)
  let path = self.parse_tqualid()
  let renaming = if self.consume_keyword(As) is Some(_) {
    Some(self.parse_uident(false))
  } else {
    None
  }
  let substitutions = self.parse_clone_substitutions()
  Dcloneimport(self.span_from(mark), is_import, path, renaming, substitutions)
}

///|
fn Parser::parse_decl(self : Parser) -> Decl raise {
  if starts_pure_decl(self) {
    self.parse_pure_decl()
  } else if starts_prog_decl(self) {
    self.parse_prog_decl()
  } else {
    self.fail_syntax("declaration")
  }
}

///|
fn parse_decl_entry(
  input : BytesView,
  filename? : BytesView = b"<decl-test>",
) -> Decl raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_decl())
}

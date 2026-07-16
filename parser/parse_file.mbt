// Module, scope, and file-level grammar productions.

///|
fn starts_module_declaration(parser : Parser) -> Bool {
  parser.at_keyword(Scope) ||
  parser.at_keyword(Import) ||
  parser.at_keyword(Use) ||
  parser.at_keyword(Clone) ||
  parser.at_keyword(Meta) ||
  starts_pure_decl(parser) ||
  starts_prog_decl(parser)
}

///|
fn Parser::parse_scope_declaration(self : Parser) -> Decl raise {
  let head_mark = self.mark()
  let opening = self.expect_keyword(Scope)
  self.enter_nesting(opening.span)
  let result = try {
    let is_import = self.consume_keyword(Import) is Some(_)
    let name = parse_attrs_ident(self, parser => parser.parse_uident(true))
    let head_span = self.span_from(head_mark)
    let declarations : Array[Decl] = []
    while !self.at_keyword(End) {
      if self.peek_kind_n(0) is Some(Eof) {
        ignore(self.expect_keyword(End))
      }
      // Unlike a direct module body, a scope has no dedicated nested-module
      // production in Why3's grammar.
      guard starts_module_declaration(self) else {
        self.fail_syntax("scope declaration or `end`")
      }
      declarations.push(self.parse_module_declaration())
      self.record_list_push()
    }
    ignore(self.expect_keyword(End))
    self.record_list_finalize()
    Dscope(head_span, is_import, name, declarations)
  } catch {
    error => {
      self.leave_nesting()
      raise error
    }
  }
  self.leave_nesting()
  result
}

///|
fn Parser::parse_import_declaration(self : Parser) -> Decl raise {
  ignore(self.expect_keyword(Import))
  Dimport(self.parse_uqualid())
}

///|
fn Parser::parse_module_declaration(self : Parser) -> Decl raise {
  if self.at_keyword(Scope) {
    return self.parse_scope_declaration()
  }
  if self.at_keyword(Import) {
    return self.parse_import_declaration()
  }
  if self.at_keyword(Use) || self.at_keyword(Clone) {
    return self.parse_use_clone_decl()
  }
  if self.at_keyword(Meta) {
    return self.parse_meta_decl()
  }
  if starts_pure_decl(self) {
    return self.parse_pure_decl()
  }
  if starts_prog_decl(self) {
    return self.parse_prog_decl()
  }
  self.fail_syntax("module declaration")
}

///|
fn[A] fail_nested_module(span : Span) -> A raise {
  fail_with_diagnostic(make_parse_diagnostic(NestedModule, span))
}

///|
fn Parser::fail_direct_nested_module(self : Parser) -> Unit raise {
  let token = self.peek()
  guard token.kind is Keyword(Theory | Module) else {
    self.fail_syntax("theory or module")
  }
  ignore(self.advance())
  fail_nested_module(token.span)
}

///|
fn Parser::parse_mlw_module(self : Parser) -> MlwModule raise {
  let module_mark = self.mark()
  let kind = if self.consume_keyword(Theory) is Some(_) {
    ModuleKind::Theory
  } else {
    ignore(self.expect_keyword(Module))
    Module
  }
  let name = parse_attrs_ident(self, parser => parser.parse_uident(true))
  let interface = if kind is Module && self.consume_symbol(Colon) is Some(_) {
    Some(self.parse_tqualid())
  } else {
    None
  }
  let declarations : Array[Decl] = []
  while !self.at_keyword(End) {
    if self.at_keyword(Theory) || self.at_keyword(Module) {
      self.fail_direct_nested_module()
    }
    if self.peek_kind_n(0) is Some(Eof) {
      ignore(self.expect_keyword(End))
    }
    guard starts_module_declaration(self) else {
      self.fail_syntax("module declaration or `end`")
    }
    declarations.push(self.parse_module_declaration())
    self.record_list_push()
  }
  ignore(self.expect_keyword(End))
  self.record_list_finalize()
  { kind, name, interface, declarations, span: self.span_from(module_mark) }
}

///|
fn Parser::fail_declaration_after_module(self : Parser) -> Unit raise {
  let mark = self.mark()
  if self.at_keyword(Scope) ||
    self.at_keyword(Import) ||
    self.at_keyword(Use) ||
    self.at_keyword(Clone) {
    ignore(self.advance())
  } else if self.at_keyword(Meta) {
    ignore(self.parse_meta_decl())
  } else if starts_pure_decl(self) {
    ignore(self.parse_pure_decl())
  } else if starts_prog_decl(self) {
    ignore(self.parse_prog_decl())
  } else {
    self.fail_syntax("theory or module")
  }
  fail_nested_module(self.span_from(mark))
}

///|
fn Parser::parse_modules_file(self : Parser) -> MlwFile raise {
  let modules : Array[MlwModule] = [self.parse_mlw_module()]
  self.record_list_push()
  while !(self.peek_kind_n(0) is Some(Eof)) {
    if self.at_keyword(Theory) || self.at_keyword(Module) {
      modules.push(self.parse_mlw_module())
      self.record_list_push()
    } else {
      self.fail_declaration_after_module()
    }
  }
  self.record_list_finalize()
  Modules(modules)
}

///|
fn Parser::parse_declarations_file(self : Parser) -> MlwFile raise {
  let declarations : Array[Decl] = [self.parse_module_declaration()]
  self.record_list_push()
  while !(self.peek_kind_n(0) is Some(Eof)) {
    if self.at_keyword(Theory) || self.at_keyword(Module) {
      self.fail_direct_nested_module()
    }
    guard starts_module_declaration(self) else {
      self.fail_syntax("top-level declaration")
    }
    declarations.push(self.parse_module_declaration())
    self.record_list_push()
  }
  self.record_list_finalize()
  Decls(declarations)
}

///|
fn Parser::parse_mlw_file(self : Parser) -> MlwFile raise {
  if self.peek_kind_n(0) is Some(Eof) {
    return MlwFile::empty()
  }
  if self.at_keyword(Theory) || self.at_keyword(Module) {
    return self.parse_modules_file()
  }
  if starts_module_declaration(self) {
    return self.parse_declarations_file()
  }
  self.fail_syntax("WhyML module or declaration")
}

///|
fn parse_mlw_file_entry(
  input : BytesView,
  filename? : BytesView = b"<file-test>",
) -> MlwFile raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_mlw_file())
}

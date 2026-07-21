// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn require_same_context(
  anchor : @identity.SemanticId,
  id : @identity.SemanticId,
) -> Unit raise PrinterError {
  if !anchor.same_context(id) {
    fail_printer(
      ContextMismatch,
      "SMT query combines different compilation contexts",
    )
  }
}

///|
fn scan_type(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  ty : @logic.Ty,
) -> Unit raise PrinterError {
  require_same_context(anchor, ty.context_anchor())
  match ty.view() {
    TyVar(_) =>
      fail_printer(
        ResidualTypeVariable,
        "SMT printer received a residual type variable",
      )
    TyApp(symbol, arguments) => {
      match symbol.view().definition {
        Range(_, _) | Float(_, _) =>
          fail_printer(
            UnsupportedType,
            "range and float types are outside the SMT MVP printer",
          )
        NoDef | Alias(_) => ()
      }
      if symbol.builtin_kind() is Some(_) &&
        syntax.type_template(symbol) is None {
        fail_printer(
          MissingBuiltinSyntax,
          "builtin type has no bound driver syntax",
        )
      }
      for argument in arguments {
        scan_type(anchor, syntax, argument)
      }
    }
  }
}

///|
fn scan_logic_symbol(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  symbol : @logic.LSymbol,
) -> Unit raise PrinterError {
  let view = symbol.view()
  require_same_context(anchor, view.id)
  // Why3 deliberately keeps syntax-mapped builtins such as polymorphic
  // equality in the prepared Task. Their declarations and type parameters
  // are consumed entirely by the driver template and never reach SMT.
  if syntax.logic_template(symbol) is Some(_) {
    return
  }
  if !view.type_parameters.is_empty() {
    fail_printer(
      ResidualTypeVariable,
      "SMT printer received a polymorphic logic symbol",
    )
  }
  for ty in view.argument_types {
    scan_type(anchor, syntax, ty)
  }
  if view.result_type is Some(ty) {
    scan_type(anchor, syntax, ty)
  }
  if view.origin.attributes().any(attribute => attribute == b"builtin") &&
    view.role is Ordinary &&
    syntax.logic_template(symbol) is None {
    fail_printer(
      MissingBuiltinSyntax,
      "builtin logic symbol has no bound driver syntax",
    )
  }
}

///|
fn scan_term(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  term : @logic.Term,
) -> Unit raise PrinterError {
  if term.ty() is Some(ty) {
    scan_type(anchor, syntax, ty)
  }
  match term.view() {
    Tvar(variable) => {
      require_same_context(anchor, variable.semantic_id())
      scan_type(anchor, syntax, variable.ty())
    }
    Tconst(_) | Ttrue | Tfalse => ()
    Tapp(symbol, instantiation, arguments) => {
      scan_logic_symbol(anchor, syntax, symbol)
      if syntax.logic_template(symbol) is None && !instantiation.is_empty() {
        fail_printer(
          ResidualTypeVariable,
          "SMT printer received a residual type instantiation",
        )
      }
      for argument in arguments {
        scan_term(anchor, syntax, argument)
      }
    }
    Tif(condition, then_branch, else_branch) => {
      scan_term(anchor, syntax, condition)
      scan_term(anchor, syntax, then_branch)
      scan_term(anchor, syntax, else_branch)
    }
    Tlet(variable, value, body) => {
      require_same_context(anchor, variable.semantic_id())
      scan_type(anchor, syntax, variable.ty())
      scan_term(anchor, syntax, value)
      scan_term(anchor, syntax, body)
    }
    Tcase(_, _) =>
      fail_printer(
        UnsupportedTerm,
        "pattern matching must be eliminated before SMT printing",
      )
    Teps(_, _) =>
      fail_printer(
        UnsupportedTerm,
        "epsilon must be eliminated before SMT printing",
      )
    Tquant(_, binders, triggers, body) => {
      for binder in binders {
        require_same_context(anchor, binder.semantic_id())
        scan_type(anchor, syntax, binder.ty())
      }
      for group in triggers {
        for trigger in group {
          scan_term(anchor, syntax, trigger)
        }
      }
      scan_term(anchor, syntax, body)
    }
    Tbinop(_, left, right) => {
      scan_term(anchor, syntax, left)
      scan_term(anchor, syntax, right)
    }
    Tnot(inner) => scan_term(anchor, syntax, inner)
  }
}

///|
fn snapshot_key_matches(
  origin : @identity.Origin,
  theory_key : BytesView,
  item : UInt,
  inner : UInt,
  digest : BytesView,
) -> Bool {
  guard origin.view() is SnapshotOrigin(_, key, _) else { return false }
  let view = key.view()
  view.theory_key[:] == theory_key &&
  view.theory_item_ordinal == item &&
  view.declaration_inner_ordinal == inner &&
  view.symbol_digest[:] == digest
}

///|
fn trusted_tuple0_error(declaration : @logic.DataDeclaration) -> String? {
  let view = declaration.view()
  let type_view = view.type_symbol.view()
  if type_view.name != b"tuple0" {
    return Some("datatype is not the pinned tuple0 type")
  }
  if !type_view.parameters.is_empty() || !(type_view.definition is NoDef) {
    return Some("Tuple0 type shape does not match the manifest")
  }
  if view.constructors.length() != 1 {
    return Some("Tuple0 must have exactly one constructor")
  }
  if !snapshot_key_matches(
      type_view.origin,
      b"why3.Tuple0.Tuple0",
      0U,
      0U,
      b"\xb4\x3a\xdf\x23\x68\x0d\xdf\xd4\x46\xb2\xf6\x34\x60\xf5\x77\x00\x99\xf1\x92\x0b\x97\x75\x72\x1b\xec\xf4\x00\xc4\x58\x55\x74\x23",
    ) {
    return Some("Tuple0 type snapshot key does not match the manifest")
  }
  let data_constructor = view.constructors[0].view()
  let symbol = data_constructor.symbol.view()
  if symbol.name != b"Tuple0" ||
    !symbol.argument_types.is_empty() ||
    !(symbol.result_type is Some(_)) ||
    symbol.role != Constructor(1) ||
    !data_constructor.projections.is_empty() {
    return Some("Tuple0 constructor shape does not match the manifest")
  }
  if !snapshot_key_matches(
      symbol.origin,
      b"why3.Tuple0.Tuple0",
      0U,
      1U,
      b"\xe9\xd3\x05\x33\xff\xf3\xec\x08\xc2\x86\xcb\x56\x4e\xa5\xad\xbf\x83\xd3\x02\x64\xa4\x40\x3a\xfa\x8f\x2d\x12\x31\x61\xfe\x96\x19",
    ) {
    return Some("Tuple0 constructor snapshot key does not match the manifest")
  }
  None
}

///|
fn scan_declaration(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  declaration : @logic.Decl,
) -> Unit raise PrinterError {
  match declaration.view() {
    Dtype(symbols) =>
      for symbol in symbols {
        let view = symbol.view()
        require_same_context(anchor, view.id)
        // The upstream SMT printer omits type declarations handled by a
        // driver syntax template (for example the polymorphic function-arrow
        // type used by the higher-order encoding). The template consumes the
        // declaration and its parameters before SMT-LIB emission.
        if syntax.type_template(symbol) is Some(_) {
          continue
        }
        if !view.parameters.is_empty() {
          fail_printer(
            ResidualTypeVariable,
            "SMT printer received a parameterized type declaration",
          )
        }
        match view.definition {
          Range(_, _) | Float(_, _) =>
            fail_printer(
              UnsupportedType,
              "range and float declarations are outside the SMT MVP printer",
            )
          Alias(ty) => scan_type(anchor, syntax, ty)
          NoDef => ()
        }
      }
    Ddata(data) =>
      for entry in data {
        let symbol = entry.view().type_symbol
        if syntax.type_template(symbol) is Some(_) {
          if symbol.builtin_kind() != Some(BuiltinBoolean) {
            fail_printer(
              UnsupportedDatatype,
              "only driver-syntax Bool data may bypass datatype printing",
            )
          }
        } else if trusted_tuple0_error(entry) is Some(message) {
          fail_printer(UnsupportedDatatype, message)
        }
      }
    Dparam(symbol) => scan_logic_symbol(anchor, syntax, symbol)
    Dlogic(definitions) => {
      let printable = definitions.filter(definition => {
        syntax.logic_template(definition.view().symbol) is None
      })
      if printable.length() > 1 {
        fail_printer(
          UnsupportedDeclaration,
          "recursive logic groups are outside the SMT MVP printer",
        )
      }
      for definition in definitions {
        let view = definition.view()
        scan_logic_symbol(anchor, syntax, view.symbol)
        if syntax.logic_template(view.symbol) is Some(_) {
          continue
        }
        if view.body.contains_logic_symbol(view.symbol) {
          fail_printer(
            UnsupportedDeclaration,
            "recursive logic definitions are outside the SMT MVP printer",
          )
        }
        for parameter in view.parameters {
          require_same_context(anchor, parameter.semantic_id())
          scan_type(anchor, syntax, parameter.ty())
        }
        scan_term(anchor, syntax, view.body)
      }
    }
    Dind(_) =>
      fail_printer(
        UnsupportedDeclaration,
        "inductive declarations must be eliminated before SMT printing",
      )
    Dprop(kind, proposition, formula) => {
      require_same_context(anchor, proposition.semantic_id())
      if kind is Plemma {
        fail_printer(
          UnsupportedDeclaration,
          "lemma declarations cannot occur in a prepared SMT task",
        )
      }
      scan_term(anchor, syntax, formula)
    }
  }
}

///|
fn scan_prepared_task(
  query : SmtV26Query,
  syntax : SyntaxMaps,
  task : @theory.Task,
) -> Unit raise PrinterError {
  if !query.anchor.same_context(task.context_anchor()) {
    fail_printer(
      ContextMismatch,
      "printer query and task belong to different compilation contexts",
    )
  }
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      scan_declaration(query.anchor, syntax, declaration)
    }
  }
}

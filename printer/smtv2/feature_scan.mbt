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
  let attributes = view.origin.attributes()
  if attributes.any(attribute => attribute == b"builtin") &&
    !attributes.any(attribute => attribute == b"is_field_id") &&
    view.role is Ordinary &&
    view.origin.kind().view() is UserKind &&
    syntax.logic_template(symbol) is None {
    fail_printer(
      MissingBuiltinSyntax,
      "builtin logic symbol " +
      view.name.to_string() +
      " has no bound driver syntax",
    )
  }
}

///|
fn scan_pattern(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  pattern : @logic.Pattern,
) -> Unit raise PrinterError {
  scan_type(anchor, syntax, pattern.ty())
  match pattern.view() {
    Pwild(_) => ()
    Pvar(variable) => {
      require_same_context(anchor, variable.semantic_id())
      scan_type(anchor, syntax, variable.ty())
    }
    Papp(symbol, arguments, _) => {
      require_same_context(anchor, symbol.semantic_id())
      for argument in arguments {
        scan_pattern(anchor, syntax, argument)
      }
    }
    Por(_, _, _) | Pas(_, _, _) =>
      fail_printer(
        UnsupportedTerm,
        "nested pattern matching must be compiled before SMT printing",
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
      let view = symbol.view()
      if syntax.logic_template(symbol) is None &&
        (view.role is Constructor(_) || view.role is Projection) {
        require_same_context(anchor, view.id)
        for entry in instantiation {
          require_same_context(anchor, entry.0.semantic_id())
          scan_type(anchor, syntax, entry.1)
        }
      } else {
        scan_logic_symbol(anchor, syntax, symbol)
        if syntax.logic_template(symbol) is None && !instantiation.is_empty() {
          fail_printer(
            ResidualTypeVariable,
            "SMT printer received a residual type instantiation",
          )
        }
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
    Tcase(scrutinee, branches) => {
      scan_term(anchor, syntax, scrutinee)
      for branch in branches {
        let view = branch.view()
        scan_pattern(anchor, syntax, view.pattern)
        scan_term(anchor, syntax, view.body)
      }
    }
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
fn scan_data_type(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  allowed : Map[@logic.TyVarSymbol, Unit],
  ty : @logic.Ty,
) -> Unit raise PrinterError {
  require_same_context(anchor, ty.context_anchor())
  match ty.view() {
    TyVar(variable) =>
      if !allowed.contains(variable) {
        fail_printer(
          ResidualTypeVariable,
          "datatype refers to an undeclared type variable",
        )
      }
    TyApp(symbol, arguments) => {
      if symbol.builtin_kind() is Some(_) &&
        syntax.type_template(symbol) is None {
        fail_printer(
          MissingBuiltinSyntax,
          "builtin datatype field has no bound driver syntax",
        )
      }
      for argument in arguments {
        scan_data_type(anchor, syntax, allowed, argument)
      }
    }
  }
}

///|
fn scan_data_declaration(
  anchor : @identity.SemanticId,
  syntax : SyntaxMaps,
  declaration : @logic.DataDeclaration,
) -> Unit raise PrinterError {
  let view = declaration.view()
  let type_view = view.type_symbol.view()
  require_same_context(anchor, type_view.id)
  let allowed : Map[@logic.TyVarSymbol, Unit] = Map([])
  for parameter in type_view.parameters {
    require_same_context(anchor, parameter.semantic_id())
    allowed[parameter] = ()
  }
  let is_record = view.constructors.length() == 1
  for data_constructor in view.constructors {
    let constructor_view = data_constructor.view()
    let symbol_view = constructor_view.symbol.view()
    require_same_context(anchor, symbol_view.id)
    if !(symbol_view.role is Constructor(_)) {
      fail_printer(
        UnsupportedDatatype,
        "datatype declaration contains a non-constructor symbol",
      )
    }
    for argument in symbol_view.argument_types {
      scan_data_type(anchor, syntax, allowed, argument)
    }
    if symbol_view.result_type is Some(result_type) {
      scan_data_type(anchor, syntax, allowed, result_type)
    }
    for projection in constructor_view.projections {
      if projection is Some(projection) {
        require_same_context(anchor, projection.semantic_id())
        if !is_record {
          fail_printer(
            UnsupportedDatatype,
            "sum types cannot declare projections in SMT-LIB 2.6",
          )
        }
      }
    }
  }
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
        for parameter in view.parameters {
          require_same_context(anchor, parameter.semantic_id())
        }
        match view.definition {
          Range(_, _) | Float(_, _) =>
            fail_printer(
              UnsupportedType,
              "range and float declarations are outside the SMT MVP printer",
            )
          Alias(_) => ()
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
        } else {
          scan_data_declaration(anchor, syntax, entry)
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
    Dind(_, _) =>
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

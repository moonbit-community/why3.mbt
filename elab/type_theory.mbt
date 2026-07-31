// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct PendingLogic {
  declaration : @parser.LogicDecl
  symbol : @logic.LSymbol
  parameter_bindings : Array[(Bytes, DLocal)]
  semantic_parameters : Array[@logic.VSymbol]
  semantic_values : Array[(Int, @logic.VSymbol)]
  result_type : Dty?
}

///|
fn parser_proposition_kind(
  kind : @parser.PropositionKind,
) -> @logic.PropositionKind {
  match kind {
    Plemma => Plemma
    Paxiom => Paxiom
    Pgoal => Pgoal
  }
}

///|
fn PureTyping::type_parameters(
  self : PureTyping,
  parameters : ArrayView[@parser.Ident],
) -> Array[@logic.TyVarSymbol] raise {
  let result : Array[@logic.TyVarSymbol] = []
  for parameter in parameters {
    let span = source_span(parameter.span)
    result.push(
      self.environment.intern_type_variable(
        self.semantic_context,
        parameter.name,
        user_origin(parameter),
        Some(span),
      ),
    )
  }
  result
}

///|
fn PureTyping::make_pure_data_declaration(
  self : PureTyping,
  typing_space : @theory.Namespace,
  declaration : @parser.TypeDecl,
  symbol : @logic.TypeSymbol,
  parameters : ArrayView[@logic.TyVarSymbol],
  allow_program_fields? : Bool = false,
) -> @logic.DataDeclaration raise {
  let span = Some(source_span(declaration.span))
  let result_type = @logic.Ty::app(
    symbol,
    parameters.map(@logic.Ty::variable),
    span,
  )
  match declaration.definition {
    TDalgebraic(cases) => {
      if cases.is_empty() {
        @logic.fail_type(
          EmptyDeclaration,
          span,
          "algebraic datatype has no constructors",
        )
      }
      let projections : Map[Bytes, @logic.LSymbol] = Map([])
      let constructors : Array[@logic.DataConstructor] = []
      for case_ in cases {
        let argument_types : Array[@logic.Ty] = []
        let constructor_projections : Array[@logic.LSymbol?] = []
        for parameter in case_.params {
          if parameter.ghost && !allow_program_fields {
            fail_invalid_input(
              InvalidDeclaration,
              PureTyping,
              Some(source_span(parameter.span)),
              "ghost datatype fields are only allowed in programs",
            )
          }
          let argument_type = self.ty_of_pty(
            typing_space,
            parameter.param_type,
            Some(source_span(parameter.span)),
          )
          argument_types.push(argument_type)
          match parameter.ident {
            None => constructor_projections.push(None)
            Some(field) => {
              let projection = match projections.get(field.name) {
                Some(projection) => {
                  if projection.view().result_type != Some(argument_type) {
                    @logic.fail_type(
                      InvalidDeclaration,
                      Some(source_span(field.span)),
                      "datatype field has conflicting types",
                    )
                  }
                  projection
                }
                None => {
                  let projection = @logic.LSymbol::new_projection(
                    self.semantic_context,
                    field.name,
                    user_origin_with_attributes(field, [
                      b"is_field_id", b"builtin",
                    ]),
                    result_type,
                    argument_type,
                    Some(source_span(field.span)),
                  )
                  projections[field.name] = projection
                  projection
                }
              }
              constructor_projections.push(Some(projection))
            }
          }
        }
        let constructor_symbol = @logic.LSymbol::new_constructor(
          self.semantic_context,
          case_.ident.name,
          user_origin(case_.ident),
          argument_types,
          result_type,
          cases.length(),
          Some(source_span(case_.span)),
        )
        constructors.push(
          @logic.DataConstructor::new(
            constructor_symbol,
            constructor_projections,
            Some(source_span(case_.span)),
          ),
        )
      }
      @logic.DataDeclaration::new(symbol, constructors, span)
    }
    TDrecord(fields) => {
      if fields.is_empty() {
        @logic.fail_type(
          EmptyRecord,
          span,
          "empty records are represented by abstract types",
        )
      }
      let argument_types : Array[@logic.Ty] = []
      let projections : Array[@logic.LSymbol?] = []
      for field in fields {
        if (field.mutable || field.ghost) && !allow_program_fields {
          fail_invalid_input(
            InvalidTypeDeclaration,
            PureTyping,
            Some(source_span(field.span)),
            "mutable or ghost record fields are only allowed in programs",
          )
        }
        let field_type = self.ty_of_pty(
          typing_space,
          field.field_type,
          Some(source_span(field.span)),
        )
        argument_types.push(field_type)
        projections.push(
          Some(
            @logic.LSymbol::new_projection(
              self.semantic_context,
              field.ident.name,
              user_origin_with_attributes(field.ident, [
                b"is_field_id", b"builtin",
              ]),
              result_type,
              field_type,
              Some(source_span(field.span)),
            ),
          ),
        )
      }
      let constructor_name = declaration.ident.name + b"'mk"
      let constructor_origin = @identity.Origin::user(
        constructor_name,
        Some(source_span(declaration.ident.span)),
        [b"builtin"],
      )
      let constructor_symbol = @logic.LSymbol::new_constructor(
        self.semantic_context,
        constructor_name,
        constructor_origin,
        argument_types,
        result_type,
        1,
        span,
      )
      @logic.DataDeclaration::new(
        symbol,
        [@logic.DataConstructor::new(constructor_symbol, projections, span)],
        span,
      )
    }
    _ =>
      @logic.fail_type(
        InvalidDeclaration,
        span,
        "a semantic data declaration requires an algebraic or record source",
      )
  }
}

///|
fn PureTyping::add_program_data_type_declaration(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declaration : @parser.TypeDecl,
) -> Unit raise {
  let span = Some(source_span(declaration.span))
  if declaration.visibility != Public {
    @logic.fail_type(
      InvalidDeclaration,
      span,
      "program data helper requires a public type",
    )
  }
  let parameters = self.type_parameters(declaration.params)
  let origin = user_origin(declaration.ident)
  let symbol = @logic.TypeSymbol::new_abstract(
    self.semantic_context,
    declaration.ident.name,
    origin,
    parameters,
    span,
  )
  let typing_space = builder
    .current_namespace()
    .overlay(
      @theory.Namespace::empty().add_type(declaration.ident.name, symbol, span),
    )
  let data = self.make_pure_data_declaration(
    typing_space,
    declaration,
    symbol,
    parameters,
    allow_program_fields=true,
  )
  builder.add_decl(
    @logic.Decl::data(self.semantic_context, origin, [data], span),
    span,
  )
}

///|
fn pure_recursive_data_group(
  declarations : ArrayView[@parser.TypeDecl],
) -> Bool {
  if declarations.length() <= 1 {
    return false
  }
  for declaration in declarations {
    if declaration.visibility != Public ||
      declaration.mutable ||
      !declaration.invariant.terms.is_empty() ||
      declaration.witness is Some(_) {
      return false
    }
    match declaration.definition {
      TDalgebraic(_) => ()
      TDrecord(fields) => if fields.is_empty() { return false }
      _ => return false
    }
  }
  true
}

///|
fn pty_mentions_pending_type(
  source : @parser.Pty,
  names : ArrayView[Bytes],
) -> Bool {
  match source {
    PTtyvar(_) => false
    PTtyapp(path, arguments) => {
      let segments = qualid_segments(path)
      (segments.length() == 1 && names.any(name => name[:] == segments[0][:])) ||
      arguments.any(argument => pty_mentions_pending_type(argument, names))
    }
    PTtuple(arguments) | PTref(arguments) =>
      arguments.any(argument => pty_mentions_pending_type(argument, names))
    PTarrow(parameter, result) =>
      pty_mentions_pending_type(parameter, names) ||
      pty_mentions_pending_type(result, names)
    PTscope(_, nested) | PTparen(nested) | PTpure(nested) =>
      pty_mentions_pending_type(nested, names)
  }
}

///|
fn PureTyping::add_recursive_data_group(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declarations : ArrayView[@parser.TypeDecl],
  allow_program_fields? : Bool = false,
) -> Unit raise {
  let symbols : Array[@logic.TypeSymbol?] = [ for _ in declarations => None ]
  let parameters : Array[Array[@logic.TyVarSymbol]] = []
  let mut typing_space = builder.current_namespace()
  for index, declaration in declarations {
    let declaration_parameters = self.type_parameters(declaration.params)
    parameters.push(declaration_parameters)
    if declaration.definition is TDalias(_) {
      continue
    }
    let span = Some(source_span(declaration.span))
    let symbol = @logic.TypeSymbol::new_abstract(
      self.semantic_context,
      declaration.ident.name,
      user_origin(declaration.ident),
      declaration_parameters,
      span,
    )
    typing_space = typing_space.overlay(
      @theory.Namespace::empty().add_type(declaration.ident.name, symbol, span),
    )
    symbols[index] = Some(symbol)
  }

  // Aliases may refer forward to any concrete member of the group. Resolve
  // alias-to-alias dependencies in topological order; applications expand
  // aliases immediately, so the emitted declarations only depend on the
  // already declared concrete data symbols.
  let mut unresolved : Array[Int] = []
  for index, declaration in declarations {
    if declaration.definition is TDalias(_) {
      unresolved.push(index)
    }
  }
  let alias_order : Array[Int] = []
  while !unresolved.is_empty() {
    let pending_names = unresolved.map(index => declarations[index].ident.name)
    let next : Array[Int] = []
    let mut progress = false
    for index in unresolved {
      let declaration = declarations[index]
      guard declaration.definition is TDalias(target) else {
        abort("non-alias remained in recursive alias resolution")
      }
      if pty_mentions_pending_type(target, pending_names) {
        next.push(index)
        continue
      }
      let span = Some(source_span(declaration.span))
      let symbol = @logic.TypeSymbol::new_alias(
        self.semantic_context,
        declaration.ident.name,
        user_origin(declaration.ident),
        parameters[index],
        self.ty_of_pty(typing_space, target, span),
        span,
      )
      symbols[index] = Some(symbol)
      typing_space = typing_space.overlay(
        @theory.Namespace::empty().add_type(
          declaration.ident.name,
          symbol,
          span,
        ),
      )
      alias_order.push(index)
      progress = true
    }
    if !progress {
      @logic.fail_type(
        InvalidDeclaration,
        Some(source_span(declarations[unresolved[0]].span)),
        "recursive type aliases do not reach a concrete data constructor",
      )
    }
    unresolved = next
  }

  let data_declarations : Array[@logic.DataDeclaration] = []
  for index, declaration in declarations {
    if declaration.definition is TDalias(_) {
      continue
    }
    guard symbols[index] is Some(symbol) else {
      abort("recursive data symbol was not initialized")
    }
    data_declarations.push(
      self.make_pure_data_declaration(
        typing_space,
        declaration,
        symbol,
        parameters[index],
        allow_program_fields~,
      ),
    )
  }
  if data_declarations.is_empty() {
    @logic.fail_type(
      InvalidDeclaration,
      Some(source_span(declarations[0].span)),
      "recursive type group has no concrete data constructor",
    )
  }
  let mut first_data = 0
  while declarations[first_data].definition is TDalias(_) {
    first_data = first_data + 1
  }
  let first = declarations[first_data]
  let span = Some(source_span(first.span))
  builder.add_decl(
    @logic.Decl::data(
      self.semantic_context,
      user_origin(first.ident),
      data_declarations,
      span,
    ),
    span,
  )
  if !allow_program_fields {
    let record_projections : Array[@logic.LSymbol] = []
    for index, declaration in declarations {
      guard declaration.definition is TDrecord(_) &&
        symbols[index] is Some(symbol) else {
        continue
      }
      for data in data_declarations {
        if data.view().type_symbol == symbol {
          for data_constructor in data.view().constructors {
            for projection in data_constructor.view().projections {
              if projection is Some(projection) &&
                !record_projections.contains(projection) {
                record_projections.push(projection)
              }
            }
          }
        }
      }
    }
    for projection in record_projections.rev() {
      builder.add_meta(
        @theory.Meta::new(b"model_record", [MetaLogicSymbol(projection)]),
        span,
      )
    }
  }
  for index in alias_order {
    let declaration = declarations[index]
    guard symbols[index] is Some(symbol) else {
      abort("recursive alias symbol was not initialized")
    }
    let alias_span = Some(source_span(declaration.span))
    builder.add_decl(
      @logic.Decl::type_declaration(
        self.semantic_context,
        user_origin(declaration.ident),
        [symbol],
        alias_span,
      ),
      alias_span,
    )
  }
}

///|
fn PureTyping::add_type_declaration(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declaration : @parser.TypeDecl,
) -> Unit raise {
  let span = Some(source_span(declaration.span))
  if declaration.mutable ||
    !declaration.invariant.terms.is_empty() ||
    declaration.witness is Some(_) {
    fail_invalid_input(
      InvalidTypeDeclaration,
      DeclarationElaboration,
      span,
      "mutable types, invariants, and witnesses are outside the MVP",
    )
  }
  let parameters = self.type_parameters(declaration.params)
  let origin = user_origin(declaration.ident)
  match (declaration.visibility, declaration.definition) {
    (Abstract, TDrecord([])) =>
      builder.add_decl(
        @logic.Decl::type_declaration(
          self.semantic_context,
          origin,
          [
            @logic.TypeSymbol::new_abstract(
              self.semantic_context,
              declaration.ident.name,
              origin,
              parameters,
              span,
            ),
          ],
          span,
        ),
        span,
      )
    (Public, TDalias(target)) => {
      let target = self.ty_of_pty(builder.current_namespace(), target, span)
      let symbol = @logic.TypeSymbol::new_alias(
        self.semantic_context,
        declaration.ident.name,
        origin,
        parameters,
        target,
        span,
      )
      builder.add_decl(
        @logic.Decl::type_declaration(
          self.semantic_context,
          origin,
          [symbol],
          span,
        ),
        span,
      )
    }
    (Public, TDrange(lower, upper)) => {
      if !parameters.is_empty() {
        @logic.fail_type(
          InvalidRange,
          span,
          "Range types cannot have type parameters",
        )
      }
      let symbol = @logic.TypeSymbol::new_range(
        self.semantic_context,
        declaration.ident.name,
        origin,
        lower,
        upper,
        span,
      )
      builder.add_decl(
        @logic.Decl::type_declaration(
          self.semantic_context,
          origin,
          [symbol],
          span,
        ),
        span,
      )
      let projection_name = declaration.ident.name + b"'int"
      let projection_origin = @identity.Origin::user(projection_name, span, [
        b"builtin",
      ])
      let projection = @logic.LSymbol::new_function(
        self.semantic_context,
        projection_name,
        projection_origin,
        [@logic.Ty::app(symbol, [], span)],
        @logic.Ty::app(
          builder.current_namespace().find_type([b"int"], span),
          [],
          span,
        ),
        span,
      )
      builder.add_decl(
        @logic.Decl::parameter(
          self.semantic_context,
          projection_origin,
          projection,
          span,
        ),
        span,
      )
      let integer_type = @logic.Ty::app(
        builder.current_namespace().find_type([b"int"], span),
        [],
        span,
      )
      for
        entry in [
          (declaration.ident.name + b"'maxInt", upper),
          (declaration.ident.name + b"'minInt", lower),
        ] {
        let (name, value) = entry
        let origin = @identity.Origin::user(name, span, [b"builtin"])
        let bound = @logic.LSymbol::new_function(
          self.semantic_context,
          name,
          origin,
          [],
          integer_type,
          span,
        )
        builder.add_decl(
          @logic.Decl::logic(
            self.semantic_context,
            origin,
            [
              @logic.LogicDefinition::new(
                self.semantic_context,
                bound,
                [],
                @logic.Term::constant(
                  @logic.Constant::integer(ILitDec, value),
                  integer_type,
                  span,
                ),
                span,
              ),
            ],
            span,
          ),
          span,
        )
      }
      builder.add_meta(
        @theory.Meta::new(b"range_type", [
          MetaTypeSymbol(symbol),
          MetaLogicSymbol(projection),
        ]),
        span,
      )
      builder.add_meta(
        @theory.Meta::new(b"model_projection", [MetaLogicSymbol(projection)]),
        span,
      )
    }
    (Public, TDfloat(exponent_digits, significand_digits)) => {
      if !parameters.is_empty() {
        @logic.fail_type(
          InvalidFloat,
          span,
          "Float types cannot have type parameters",
        )
      }
      let symbol = @logic.TypeSymbol::new_float(
        self.semantic_context,
        declaration.ident.name,
        origin,
        exponent_digits.to_int(),
        significand_digits.to_int(),
        span,
      )
      builder.add_decl(
        @logic.Decl::type_declaration(
          self.semantic_context,
          origin,
          [symbol],
          span,
        ),
        span,
      )
      let source_type = @logic.Ty::app(symbol, [], span)
      let real_name = declaration.ident.name + b"'real"
      let real_origin = @identity.Origin::user(real_name, span, [b"builtin"])
      let real_projection = @logic.LSymbol::new_function(
        self.semantic_context,
        real_name,
        real_origin,
        [source_type],
        @logic.Ty::app(
          builder.current_namespace().find_type([b"real"], span),
          [],
          span,
        ),
        span,
      )
      let finite_name = declaration.ident.name + b"'isFinite"
      let finite_origin = @identity.Origin::user(finite_name, span, [b"builtin"])
      let finite_projection = @logic.LSymbol::new_predicate(
        self.semantic_context,
        finite_name,
        finite_origin,
        [source_type],
        span,
      )
      builder.add_decl(
        @logic.Decl::parameter(
          self.semantic_context,
          real_origin,
          real_projection,
          span,
        ),
        span,
      )
      builder.add_decl(
        @logic.Decl::parameter(
          self.semantic_context,
          finite_origin,
          finite_projection,
          span,
        ),
        span,
      )
      let integer_type = @logic.Ty::app(
        builder.current_namespace().find_type([b"int"], span),
        [],
        span,
      )
      for
        entry in [
          (declaration.ident.name + b"'eb", BigInt::from_int64(exponent_digits)),
          (
            declaration.ident.name + b"'sb",
            BigInt::from_int64(significand_digits),
          ),
        ] {
        let (name, value) = entry
        let digit_origin = @identity.Origin::user(name, span, [b"builtin"])
        let digit = @logic.LSymbol::new_function(
          self.semantic_context,
          name,
          digit_origin,
          [],
          integer_type,
          span,
        )
        builder.add_decl(
          @logic.Decl::logic(
            self.semantic_context,
            digit_origin,
            [
              @logic.LogicDefinition::new(
                self.semantic_context,
                digit,
                [],
                @logic.Term::constant(
                  @logic.Constant::integer(ILitDec, value),
                  integer_type,
                  span,
                ),
                span,
              ),
            ],
            span,
          ),
          span,
        )
      }
      builder.add_meta(
        @theory.Meta::new(b"float_type", [
          MetaTypeSymbol(symbol),
          MetaLogicSymbol(real_projection),
          MetaLogicSymbol(finite_projection),
        ]),
        span,
      )
      builder.add_meta(
        @theory.Meta::new(b"model_projection", [
          MetaLogicSymbol(real_projection),
        ]),
        span,
      )
    }
    (Public, TDalgebraic(_)) => {
      let symbol = @logic.TypeSymbol::new_abstract(
        self.semantic_context,
        declaration.ident.name,
        origin,
        parameters,
        span,
      )
      let typing_space = builder
        .current_namespace()
        .overlay(
          @theory.Namespace::empty().add_type(
            declaration.ident.name,
            symbol,
            span,
          ),
        )
      let data = self.make_pure_data_declaration(
        typing_space, declaration, symbol, parameters,
      )
      builder.add_decl(
        @logic.Decl::data(self.semantic_context, origin, [data], span),
        span,
      )
      let projections : Array[@logic.LSymbol] = []
      for data_constructor in data.view().constructors {
        for projection in data_constructor.view().projections {
          if projection is Some(projection) && !projections.contains(projection) {
            projections.push(projection)
          }
        }
      }
      for projection in projections.rev() {
        builder.add_meta(
          @theory.Meta::new(b"model_record", [MetaLogicSymbol(projection)]),
          span,
        )
      }
    }
    (Public, TDrecord(fields)) => {
      let symbol = @logic.TypeSymbol::new_abstract(
        self.semantic_context,
        declaration.ident.name,
        origin,
        parameters,
        span,
      )
      if fields.is_empty() {
        return builder.add_decl(
          @logic.Decl::type_declaration(
            self.semantic_context,
            origin,
            [symbol],
            span,
          ),
          span,
        )
      }
      let typing_space = builder
        .current_namespace()
        .overlay(
          @theory.Namespace::empty().add_type(
            declaration.ident.name,
            symbol,
            span,
          ),
        )
      let data = self.make_pure_data_declaration(
        typing_space, declaration, symbol, parameters,
      )
      builder.add_decl(
        @logic.Decl::data(self.semantic_context, origin, [data], span),
        span,
      )
    }
    (Private, _) =>
      fail_invalid_input(
        InvalidTypeDeclaration,
        DeclarationElaboration,
        span,
        "private user types are outside the MVP",
      )
    (Abstract, _) =>
      fail_invalid_input(
        InvalidTypeDeclaration,
        DeclarationElaboration,
        span,
        "unsupported abstract type definition",
      )
  }
}

///|
fn PureTyping::prepare_logic(
  self : PureTyping,
  space : @theory.Namespace,
  declaration : @parser.LogicDecl,
) -> PendingLogic raise {
  let span = Some(source_span(declaration.span))
  let argument_types : Array[@logic.Ty] = []
  let parameter_bindings : Array[(Bytes, DLocal)] = []
  let semantic_parameters : Array[@logic.VSymbol] = []
  let semantic_values : Array[(Int, @logic.VSymbol)] = []
  for parameter in declaration.params {
    if parameter.ghost {
      fail_invalid_input(
        InvalidBinder,
        PureTyping,
        Some(source_span(parameter.span)),
        "ghost logic parameters are outside the MVP",
      )
    }
    let parameter_type = self.ty_of_pty(
      space,
      parameter.param_type,
      Some(source_span(parameter.span)),
    )
    argument_types.push(parameter_type)
    let delayed = self.delayed.known(
      parameter_type,
      Some(source_span(parameter.span)),
    )
    let binding = self.make_local(parameter.ident, parameter.span, delayed)
    if parameter.ident is Some(ident) {
      if parameter_bindings.any(entry => entry.0[:] == ident.name[:]) {
        @logic.fail_type(
          DuplicateBinder,
          Some(source_span(ident.span)),
          "logic declaration repeats a parameter name",
        )
      }
      parameter_bindings.push((ident.name, binding))
    }
    let variable = self.semantic_local(
      space,
      binding,
      Some(source_span(parameter.span)),
    )
    semantic_parameters.push(variable)
    semantic_values.push((binding.id, variable))
  }
  let (result_type, semantic_result) = match declaration.return_type {
    None => (None, None)
    Some(pty) => {
      let semantic = self.ty_of_pty(space, pty, span)
      (Some(self.delayed.known(semantic, span)), Some(semantic))
    }
  }
  let origin = user_origin(declaration.ident)
  let symbol = match semantic_result {
    None =>
      @logic.LSymbol::new_predicate(
        self.semantic_context,
        declaration.ident.name,
        origin,
        argument_types,
        span,
      )
    Some(result) =>
      @logic.LSymbol::new_function(
        self.semantic_context,
        declaration.ident.name,
        origin,
        argument_types,
        result,
        span,
      )
  }
  {
    declaration,
    symbol,
    parameter_bindings,
    semantic_parameters,
    semantic_values,
    result_type,
  }
}

///|
fn PureTyping::add_logic_declarations(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declarations : ArrayView[@parser.LogicDecl],
) -> Unit raise {
  if declarations.is_empty() {
    @logic.fail_type(EmptyDeclaration, None, "logic declaration is empty")
  }
  let initial_space = builder.current_namespace()
  let pending : Array[PendingLogic] = []
  let mut typing_space = initial_space
  for declaration in declarations {
    let prepared = self.prepare_logic(initial_space, declaration)
    typing_space = typing_space.overlay(
      @theory.Namespace::empty().add_logic(
        declaration.ident.name,
        prepared.symbol,
        Some(source_span(declaration.ident.span)),
      ),
    )
    pending.push(prepared)
  }
  let definitions : Array[@logic.LogicDefinition] = []
  let definition_origins : Array[@identity.Origin] = []
  let definition_spans : Array[@identity.SourceSpan] = []
  for prepared in pending {
    match prepared.declaration.definition {
      None =>
        builder.add_decl(
          @logic.Decl::parameter(
            self.semantic_context,
            prepared.symbol.view().origin,
            prepared.symbol,
            Some(source_span(prepared.declaration.span)),
          ),
          Some(source_span(prepared.declaration.span)),
        )
      Some(body) => {
        let semantic_body = match prepared.result_type {
          None =>
            self.formula(
              typing_space,
              prepared.parameter_bindings,
              prepared.semantic_values,
              body,
            )
          Some(result) =>
            self.value(
              typing_space,
              prepared.parameter_bindings,
              prepared.semantic_values,
              body,
              result,
            )
        }
        let definition = @logic.LogicDefinition::new(
          self.semantic_context,
          prepared.symbol,
          prepared.semantic_parameters,
          semantic_body,
          Some(source_span(prepared.declaration.span)),
        )
        definitions.push(definition)
        definition_origins.push(prepared.symbol.view().origin)
        definition_spans.push(source_span(prepared.declaration.span))
      }
    }
  }
  if !definitions.is_empty() {
    let origin = definition_origins[0]
    let span = Some(definition_spans[0])
    builder.add_decl(
      @logic.Decl::logic(self.semantic_context, origin, definitions, span),
      span,
    )
  }
}

///|
fn PureTyping::add_inductive_declarations(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  sign : @parser.InductiveSign,
  declarations : ArrayView[@parser.InductiveDecl],
) -> Unit raise {
  if declarations.is_empty() {
    @logic.fail_type(
      EmptyDeclaration,
      None,
      "inductive declaration group is empty",
    )
  }
  let predicates : Array[@logic.LSymbol] = []
  let mut typing_space = builder.current_namespace()
  for declaration in declarations {
    let span = Some(source_span(declaration.span))
    let argument_types : Array[@logic.Ty] = []
    for parameter in declaration.params {
      if parameter.ghost {
        fail_invalid_input(
          InvalidBinder,
          PureTyping,
          Some(source_span(parameter.span)),
          "ghost parameters are not allowed in pure inductive declarations",
        )
      }
      argument_types.push(
        self.ty_of_pty(
          builder.current_namespace(),
          parameter.param_type,
          Some(source_span(parameter.span)),
        ),
      )
    }
    let predicate = @logic.LSymbol::new_predicate(
      self.semantic_context,
      declaration.ident.name,
      user_origin(declaration.ident),
      argument_types,
      span,
    )
    typing_space = typing_space.overlay(
      @theory.Namespace::empty().add_logic(
        declaration.ident.name,
        predicate,
        span,
      ),
    )
    predicates.push(predicate)
  }
  let semantic_declarations : Array[@logic.InductiveDeclaration] = []
  for index, declaration in declarations {
    let cases : Array[@logic.InductiveCase] = []
    for case_ in declaration.cases {
      let span = Some(source_span(case_.span))
      let proposition = @logic.PrSymbol::new(
        self.semantic_context,
        case_.ident.name,
        user_origin(case_.ident),
      )
      cases.push(
        @logic.InductiveCase::new(
          self.semantic_context,
          proposition,
          self.formula(typing_space, [], [], case_.body),
          span,
        ),
      )
    }
    semantic_declarations.push(
      @logic.InductiveDeclaration::new(
        predicates[index],
        cases,
        Some(source_span(declaration.span)),
      ),
    )
  }
  let first = declarations[0]
  let span = Some(source_span(first.span))
  builder.add_decl(
    @logic.Decl::inductive(
      self.semantic_context,
      user_origin(first.ident),
      match sign {
        Ind => Ind
        Coind => Coind
      },
      semantic_declarations,
      span,
    ),
    span,
  )
}

///|
fn PureTyping::proposition_declaration(
  self : PureTyping,
  pure_space : @theory.Namespace,
  kind : @parser.PropositionKind,
  ident : @parser.Ident,
  body : @parser.Term,
) -> @logic.Decl raise {
  let span = Some(source_span(ident.span))
  let origin = user_origin(ident)
  let symbol = @logic.PrSymbol::new(self.semantic_context, ident.name, origin)
  let formula = self.formula(pure_space, [], [], body)
  @logic.Decl::proposition(
    self.semantic_context,
    origin,
    parser_proposition_kind(kind),
    symbol,
    formula,
    span,
  )
}

///|
fn PureTyping::add_proposition(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  kind : @parser.PropositionKind,
  ident : @parser.Ident,
  body : @parser.Term,
) -> Unit raise {
  let span = Some(source_span(ident.span))
  builder.add_decl(
    self.proposition_declaration(builder.current_namespace(), kind, ident, body),
    span,
  )
}

///|
fn require_meta_logic_kind(
  symbol : @logic.LSymbol,
  function_expected : Bool,
  span : @identity.SourceSpan?,
) -> @logic.LSymbol raise @logic.TypeError {
  let function_actual = symbol.view().result_type is Some(_)
  if function_actual != function_expected {
    @logic.fail_type(
      if function_expected {
        ValueExpected
      } else {
        PredicateExpected
      },
      span,
      if function_expected {
        "meta argument requires a function or constant"
      } else {
        "meta argument requires a predicate"
      },
    )
  }
  symbol
}

///|
fn require_meta_proposition_kind(
  known : @logic.KnownMap,
  symbol : @logic.PrSymbol,
  expected : @logic.PropositionKind,
  span : @identity.SourceSpan?,
) -> @logic.PrSymbol raise @logic.TypeError {
  let (actual, _) = known.find_proposition(symbol, span)
  if actual != expected {
    @logic.fail_type(
      InvalidDeclaration,
      span,
      "meta proposition argument has the wrong declaration kind",
    )
  }
  symbol
}

///|
fn PureTyping::user_meta(
  self : PureTyping,
  space : @theory.Namespace,
  known : @logic.KnownMap,
  ident : @parser.Ident,
  arguments : ArrayView[@parser.MetaArg],
  program_space? : @mlw.ProgramNamespace? = None,
) -> @theory.Meta raise {
  let span = Some(source_span(ident.span))
  let semantic_arguments : Array[@theory.MetaArgument] = []
  for argument in arguments {
    semantic_arguments.push(
      match argument {
        Mty(PTtyapp(qualid, [])) =>
          MetaTypeSymbol(
            space.find_type(qualid_segments(qualid), Some(qualid_span(qualid))),
          )
        Mty(pty) => MetaType(self.ty_of_pty(space, pty, span))
        Mfs(qualid) =>
          MetaLogicSymbol(
            require_meta_logic_kind(
              space.find_logic(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              ),
              true,
              Some(qualid_span(qualid)),
            ),
          )
        Mps(qualid) =>
          MetaLogicSymbol(
            require_meta_logic_kind(
              space.find_logic(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              ),
              false,
              Some(qualid_span(qualid)),
            ),
          )
        Max(qualid) =>
          MetaPropositionSymbol(
            require_meta_proposition_kind(
              known,
              space.find_proposition(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              ),
              Paxiom,
              Some(qualid_span(qualid)),
            ),
          )
        Mlm(qualid) =>
          MetaPropositionSymbol(
            require_meta_proposition_kind(
              known,
              space.find_proposition(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              ),
              Plemma,
              Some(qualid_span(qualid)),
            ),
          )
        Mgl(qualid) =>
          MetaPropositionSymbol(
            require_meta_proposition_kind(
              known,
              space.find_proposition(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              ),
              Pgoal,
              Some(qualid_span(qualid)),
            ),
          )
        Mval(qualid) =>
          match program_space {
            Some(program_space) => {
              let routine = program_space.find_routine(
                qualid_segments(qualid),
                Some(qualid_span(qualid)),
              )
              let view = routine.view()
              MetaIdentifier(
                @theory.SemanticName::new(
                  view.name,
                  view.origin.attributes(),
                  view.origin.source_span(),
                ),
              )
            }
            None =>
              fail_invalid_input(
                InvalidDeclaration,
                DeclarationElaboration,
                span,
                "program-value meta arguments require module elaboration",
              )
          }
        Mstr(value) => MetaString(value)
        Mint(value) => MetaInteger(value)
      },
    )
  }
  @theory.Meta::new(ident.name, semantic_arguments)
}

///|
fn PureTyping::add_user_meta(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  ident : @parser.Ident,
  arguments : ArrayView[@parser.MetaArg],
) -> Unit raise {
  let span = Some(source_span(ident.span))
  builder.add_meta(
    self.user_meta(
      builder.current_namespace(),
      builder.current_known(),
      ident,
      arguments,
    ),
    span,
  )
}

///|
fn PureTyping::clone_instantiation(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  source : @theory.Theory,
  substitutions : ArrayView[@parser.CloneSubstitution],
  span : @identity.SourceSpan?,
  allow_program_symbols? : Bool = false,
) -> @theory.TheoryInstantiation raise {
  let source_space = source.export_namespace()
  let target_space = builder.current_namespace()
  let type_instances : Array[(@logic.TypeSymbol, @logic.Ty)] = []
  let type_symbol_instances : Array[(@logic.TypeSymbol, @logic.TypeSymbol)] = []
  let logic_instances : Array[(@logic.LSymbol, @logic.LSymbol)] = []
  let proposition_instances : Array[(@logic.PrSymbol, @logic.PropositionKind)] = []
  let mut default_kind = @logic.Plemma
  for substitution in substitutions {
    match substitution {
      CStsym(source_name, variables, target) => {
        let source_symbol = source_space.find_type(
          qualid_segments(source_name),
          Some(qualid_span(source_name)),
        )
        match target {
          PTtyapp(target_name, []) if variables.is_empty() => {
            let target_symbol = target_space.find_type(
              qualid_segments(target_name),
              Some(qualid_span(target_name)),
            )
            type_symbol_instances.push((source_symbol, target_symbol))
          }
          _ => {
            if variables.length() != source_symbol.arity() {
              @logic.fail_type(
                ArityMismatch,
                Some(qualid_span(source_name)),
                "clone type substitution has the wrong parameter arity",
              )
            }
            type_instances.push(
              (source_symbol, self.ty_of_pty(target_space, target, span)),
            )
          }
        }
      }
      CSfsym(source_name, target_name) | CSpsym(source_name, target_name) => {
        let source_symbol = source_space.find_logic(
          qualid_segments(source_name),
          Some(qualid_span(source_name)),
        )
        let target_symbol = target_space.find_logic(
          qualid_segments(target_name),
          Some(qualid_span(target_name)),
        )
        logic_instances.push((source_symbol, target_symbol))
      }
      CSvsym(source_name, _) | CSxsym(source_name, _) =>
        if !allow_program_symbols {
          fail_invalid_input(
            InvalidDeclaration,
            DeclarationElaboration,
            Some(qualid_span(source_name)),
            "program clone substitutions require module elaboration",
          )
        }
      CSprop(kind) => default_kind = parser_proposition_kind(kind)
      CSaxiom(source_name) =>
        proposition_instances.push(
          (
            source_space.find_proposition(
              qualid_segments(source_name),
              Some(qualid_span(source_name)),
            ),
            Paxiom,
          ),
        )
      CSlemma(source_name) =>
        proposition_instances.push(
          (
            source_space.find_proposition(
              qualid_segments(source_name),
              Some(qualid_span(source_name)),
            ),
            Plemma,
          ),
        )
      CSgoal(source_name) =>
        proposition_instances.push(
          (
            source_space.find_proposition(
              qualid_segments(source_name),
              Some(qualid_span(source_name)),
            ),
            Pgoal,
          ),
        )
    }
  }
  @theory.TheoryInstantiation::new(
    type_instances, type_symbol_instances, logic_instances, proposition_instances,
    default_kind, span,
  )
}

///|
fn PureTyping::add_clone(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  source_name : @parser.QualId,
  substitutions : ArrayView[@parser.CloneSubstitution],
  span : @identity.SourceSpan?,
) -> Unit raise {
  let source = resolve_used_theory(
    self.environment,
    self.library_path,
    self.file_theories,
    source_name,
  )
  ignore(
    builder.add_clone(
      source,
      self.clone_instantiation(builder, source, substitutions, span),
      span,
    ),
  )
}

///|
fn resolve_used_theory(
  environment : @environment.Environment,
  current_library_path : ArrayView[Bytes],
  file_theories : ArrayView[(Bytes, @theory.Theory)],
  qualid : @parser.QualId,
) -> @theory.Theory raise {
  let span = Some(qualid_span(qualid))
  let key = theory_key_of_qualid(qualid)
  let key_view = key.view()
  if key_view.path.is_empty() {
    for entry in file_theories {
      if entry.0 == key_view.name {
        return entry.1
      }
    }
  }
  match registered_theory(environment, key, span) {
    Some(theory) => theory
    None => {
      let view = key_view
      if view.path.is_empty() && !current_library_path.is_empty() {
        let current_key = @theory.TheoryKey::new(
          current_library_path,
          view.name,
        )
        match registered_theory(environment, current_key, span) {
          Some(theory) => return theory
          None => ()
        }
      }
      let library_path = @env.LibraryPath::new(view.path)
      environment.read_theory(library_path, view.name, load_mlw_library, span)
    }
  }
}

///|
fn registered_theory(
  environment : @environment.Environment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @theory.Theory? raise {
  Some(environment.resolve_theory(key, span)) catch {
    @environment.EnvironmentError(diagnostic) =>
      if diagnostic.kind == ResolveError {
        None
      } else {
        raise @environment.EnvironmentError(diagnostic)
      }
  }
}

///|
fn pattern_binds_name(pattern : @parser.Pattern, name : BytesView) -> Bool {
  match pattern.desc {
    Pvar(ident) => ident.name[:] == name
    Papp(_, arguments) | Ptuple(arguments) =>
      arguments.any(argument => pattern_binds_name(argument, name))
    Prec(fields) => fields.any(field => pattern_binds_name(field.1, name))
    Pas(inner, ident, _ghost) =>
      ident.name[:] == name || pattern_binds_name(inner, name)
    Por(left, right) =>
      pattern_binds_name(left, name) || pattern_binds_name(right, name)
    Pcast(inner, _) | Pscope(_, inner) | Pparen(inner) | Pghost(inner) =>
      pattern_binds_name(inner, name)
    Pwild => false
  }
}

///|
fn term_application_head_name(term : @parser.Term) -> Bytes? {
  match term.desc {
    Tapply(function_, _) => term_application_head_name(function_)
    Tident(Qident(ident)) => Some(ident.name)
    _ => None
  }
}

///|
fn term_applies_name(term : @parser.Term, name : BytesView) -> Bool {
  let recurse = fn(child : @parser.Term) -> Bool {
    term_applies_name(child, name)
  }
  match term.desc {
    Tapply(function_, argument) =>
      (term_application_head_name(term) is Some(head) && head[:] == name) ||
      recurse(function_) ||
      recurse(argument)
    Tidapp(_, arguments) | Ttuple(arguments) => arguments.any(recurse)
    Tinfix(left, _, right)
    | Tinnfix(left, _, right)
    | Tbinop(left, _, right)
    | Tbinnop(left, _, right) => recurse(left) || recurse(right)
    Tnot(inner)
    | Tattr(_, inner)
    | Tscope(_, inner)
    | Tat(inner, _)
    | Tcast(inner, _) => recurse(inner)
    Tif(condition, consequent, alternative) =>
      recurse(condition) || recurse(consequent) || recurse(alternative)
    Tquant(_, binders, triggers, body) => {
      let shadowed = binders.any(binder => {
        binder.ident is Some(ident) && ident.name[:] == name
      })
      !shadowed && (triggers.any(group => group.any(recurse)) || recurse(body))
    }
    Teps(ident, _, body) => ident.name[:] != name && recurse(body)
    Tlet(ident, value, body) =>
      recurse(value) || (ident.name[:] != name && recurse(body))
    Tcase(scrutinee, branches) =>
      recurse(scrutinee) ||
      branches.any(branch => {
        !pattern_binds_name(branch.0, name) && recurse(branch.1)
      })
    Trecord(fields) => fields.any(field => recurse(field.1))
    Tupdate(source, fields) =>
      recurse(source) || fields.any(field => recurse(field.1))
    Ttrue | Tfalse | Tconst(_) | Tident(_) | Tasref(_) => false
  }
}

///|
fn PureTyping::parameter_has_function_type(
  self : PureTyping,
  space : @theory.Namespace,
  parameter : @parser.Param,
  function_type : @logic.TypeSymbol,
  coercions : @theory.CoercionMap,
) -> Bool raise {
  let semantic_type = self.ty_of_pty(
    space,
    parameter.param_type,
    Some(source_span(parameter.span)),
  )
  guard semantic_type.view() is TyApp(symbol, _) else { return false }
  symbol == function_type ||
  coercions.find_by_symbols(symbol, function_type) is Some(_)
}

///|
fn PureTyping::declaration_applies_function_typed_parameter(
  self : PureTyping,
  space : @theory.Namespace,
  declaration : @parser.Decl,
  function_type : @logic.TypeSymbol,
  coercions : @theory.CoercionMap,
) -> Bool raise {
  match declaration {
    Dlogic(declarations) =>
      declarations.any(declaration => {
        guard declaration.definition is Some(definition) else { return false }
        declaration.params.any(parameter => {
          parameter.ident is Some(ident) &&
          term_applies_name(definition, ident.name) &&
          self.parameter_has_function_type(
            space, parameter, function_type, coercions,
          )
        })
      })
    Dind(_, declarations) =>
      declarations.any(declaration => {
        declaration.params.any(parameter => {
          parameter.ident is Some(ident) &&
          declaration.cases.any(case_ => {
            term_applies_name(case_.body, ident.name)
          }) &&
          self.parameter_has_function_type(
            space, parameter, function_type, coercions,
          )
        })
      })
    _ => false
  }
}

///|
fn PureTyping::add_declaration(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declaration : @parser.Decl,
) -> Unit raise {
  for arity in tuple_declaration_dependencies(declaration) {
    if arity > 0 {
      let name = tuple_type_name(arity)
      let available = try {
        ignore(builder.current_namespace().find_type([name], None))
        true
      } catch {
        _ => false
      }
      if !available {
        builder.add_use(
          self.environment.tuple_module(arity).pure_theory(),
          true,
          None,
        )
      }
    }
  }
  if reference_declaration_dependency(declaration) {
    let available = try {
      ignore(builder.current_namespace().find_type([b"ref"], None))
      true
    } catch {
      _ => false
    }
    if !available {
      builder.add_use(
        self.environment.reference_module().pure_theory(),
        true,
        None,
      )
    }
  }
  let high_order = self.environment.high_order_module().pure_theory()
  let function_type = high_order
    .export_namespace()
    .find_type([b"infix ->"], None)
  let requires_high_order = high_order_declaration_dependency(declaration) ||
    self.declaration_applies_function_typed_parameter(
      builder.current_namespace(),
      declaration,
      function_type,
      builder.current_coercions(),
    )
  if requires_high_order {
    let available = try {
      ignore(builder.current_namespace().find_type([b"infix ->"], None))
      true
    } catch {
      _ => false
    }
    if !available {
      builder.add_hidden_use(high_order, None)
    }
  }
  self.sync_known(builder.current_known())
  self.sync_coercions(builder.current_coercions())
  match declaration {
    Dtype(declarations) =>
      if pure_recursive_data_group(declarations) {
        self.add_recursive_data_group(builder, declarations)
      } else {
        for declaration in declarations {
          self.add_type_declaration(builder, declaration)
        }
      }
    Dlogic(declarations) => self.add_logic_declarations(builder, declarations)
    Dprop(kind, ident, body) => self.add_proposition(builder, kind, ident, body)
    Duseexport(qualid) =>
      builder.add_use(
        resolve_used_theory(
          self.environment,
          self.library_path,
          self.file_theories,
          qualid,
        ),
        true,
        Some(qualid_span(qualid)),
      )
    Duseimport(span, import_, uses) =>
      for use_ in uses {
        let (qualid, alias_name) = use_
        let scope_ident = match alias_name {
          Some(alias_name) => alias_name
          None => qualid_last(qualid)
        }
        builder.open_scope(scope_ident.name, Some(source_span(span)))
        builder.add_use(
          resolve_used_theory(
            self.environment,
            self.library_path,
            self.file_theories,
            qualid,
          ),
          true,
          Some(qualid_span(qualid)),
        )
        builder.close_scope(
          import_ || alias_name is None,
          Some(source_span(span)),
        )
      }
    Dimport(qualid) =>
      builder.import_scope(qualid_segments(qualid), Some(qualid_span(qualid)))
    Dscope(span, import_, ident, declarations) => {
      builder.open_scope(ident.name, Some(source_span(span)))
      for declaration in declarations {
        self.add_declaration(builder, declaration)
      }
      builder.close_scope(import_, Some(source_span(span)))
    }
    Dind(sign, declarations) =>
      self.add_inductive_declarations(builder, sign, declarations)
    Dmeta(ident, arguments) => self.add_user_meta(builder, ident, arguments)
    Dcloneexport(source_span_, source, substitutions) =>
      self.add_clone(
        builder,
        source,
        substitutions,
        Some(source_span(source_span_)),
      )
    Dcloneimport(source_span_, import_, source, alias_name, substitutions) => {
      let scope_ident = match alias_name {
        Some(alias_name) => alias_name
        None => qualid_last(source)
      }
      let span = Some(source_span(source_span_))
      builder.open_scope(scope_ident.name, span)
      self.add_clone(builder, source, substitutions, span)
      builder.close_scope(import_ || alias_name is None, span)
    }
    Dlet(ident, _, _, _) =>
      fail_invalid_input(
        InvalidDeclaration,
        DeclarationElaboration,
        Some(source_span(ident.span)),
        "program declarations are handled by program elaboration",
      )
    Drec(_) =>
      fail_invalid_input(
        InvalidDeclaration,
        DeclarationElaboration,
        None,
        "recursive program declarations are outside the MVP",
      )
    Dexn(ident, _, _) =>
      fail_invalid_input(
        InvalidDeclaration,
        DeclarationElaboration,
        Some(source_span(ident.span)),
        "exceptions are outside the MVP",
      )
  }
}

///|
fn add_implicit_prelude(
  environment : @environment.Environment,
  builder : @theory.TheoryBuilder,
) -> Unit raise {
  for name in [b"BuiltIn", b"Bool", b"Unit"] {
    let key = @theory.TheoryKey::new([], name)
    builder.add_use(environment.resolve_theory(key, None), true, None)
  }
}

///|
fn elaborate_theory_unit(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @theory.Theory raise {
  elaborate_theory_unit_at_path(context, environment, unit, [], [])
}

///|
fn elaborate_theory_unit_at_path(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
  path : ArrayView[Bytes],
  file_theories : ArrayView[(Bytes, @theory.Theory)],
) -> @theory.Theory raise {
  if unit.kind != Theory {
    fail_invalid_input(
      InvalidUnit,
      DeclarationElaboration,
      Some(source_span(unit.span)),
      "program modules require the program elaborator",
    )
  }
  if unit.interface is Some(_) {
    fail_invalid_input(
      InvalidUnit,
      DeclarationElaboration,
      Some(source_span(unit.span)),
      "module interfaces are outside the MVP",
    )
  }
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new(path, unit.name.name),
    semantic_name(unit.name),
  )
  add_implicit_prelude(environment, builder)
  let typing = PureTyping::new(
    context,
    environment,
    library_path=path,
    file_theories~,
  )
  for declaration in unit.declarations {
    typing.add_declaration(builder, declaration)
  }
  builder.close()
}

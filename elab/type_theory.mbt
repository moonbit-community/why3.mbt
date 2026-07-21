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
fn first_lambda_in_terms(
  terms : ArrayView[@parser.Term],
) -> @identity.SourceSpan? {
  for term in terms {
    match first_lambda_span(term) {
      Some(span) => return Some(span)
      None => ()
    }
  }
  None
}

///|
fn first_lambda_span(term : @parser.Term) -> @identity.SourceSpan? {
  match term.desc {
    Tquant(DTlambda, _, _, _) => Some(source_span(term.span))
    Tidapp(_, arguments) | Ttuple(arguments) => first_lambda_in_terms(arguments)
    Tapply(function_, argument)
    | Tinfix(function_, _, argument)
    | Tinnfix(function_, _, argument)
    | Tbinop(function_, _, argument)
    | Tbinnop(function_, _, argument) =>
      match first_lambda_span(function_) {
        Some(span) => Some(span)
        None => first_lambda_span(argument)
      }
    Tnot(inner)
    | Tattr(_, inner)
    | Tcast(inner, _)
    | Tscope(_, inner)
    | Tat(inner, _) => first_lambda_span(inner)
    Tif(condition, then_branch, else_branch) =>
      match first_lambda_span(condition) {
        Some(span) => Some(span)
        None =>
          match first_lambda_span(then_branch) {
            Some(span) => Some(span)
            None => first_lambda_span(else_branch)
          }
      }
    Tquant(_, _, triggers, body) => {
      for trigger in triggers {
        match first_lambda_in_terms(trigger) {
          Some(span) => return Some(span)
          None => ()
        }
      }
      first_lambda_span(body)
    }
    Teps(_, _, body) => first_lambda_span(body)
    Tlet(_, value, body) =>
      match first_lambda_span(value) {
        Some(span) => Some(span)
        None => first_lambda_span(body)
      }
    Tcase(scrutinee, branches) => {
      match first_lambda_span(scrutinee) {
        Some(span) => return Some(span)
        None => ()
      }
      for branch in branches {
        match first_lambda_span(branch.1) {
          Some(span) => return Some(span)
          None => ()
        }
      }
      None
    }
    Trecord(fields) => {
      for field in fields {
        match first_lambda_span(field.1) {
          Some(span) => return Some(span)
          None => ()
        }
      }
      None
    }
    Tupdate(base, fields) => {
      match first_lambda_span(base) {
        Some(span) => return Some(span)
        None => ()
      }
      for field in fields {
        match first_lambda_span(field.1) {
          Some(span) => return Some(span)
          None => ()
        }
      }
      None
    }
    Ttrue | Tfalse | Tconst(_) | Tident(_) | Tasref(_) => None
  }
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
fn PureTyping::add_type_declaration(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declaration : @parser.TypeDecl,
) -> Unit raise {
  let span = Some(source_span(declaration.span))
  if declaration.mutable ||
    !declaration.invariant.terms.is_empty() ||
    declaration.witness is Some(_) {
    fail_unsupported(
      RecordOrInvariant,
      FeatureClassification,
      span,
      "mutable types, invariants, and witnesses are outside the MVP",
    )
  }
  let parameters = self.type_parameters(declaration.params)
  let origin = user_origin(declaration.ident)
  let symbol = match (declaration.visibility, declaration.definition) {
    (Abstract, TDrecord([])) =>
      @logic.TypeSymbol::new_abstract(
        self.semantic_context,
        declaration.ident.name,
        origin,
        parameters,
        span,
      )
    (Public, TDalias(target)) => {
      let target = self.ty_of_pty(builder.current_namespace(), target, span)
      @logic.TypeSymbol::new_alias(
        self.semantic_context,
        declaration.ident.name,
        origin,
        parameters,
        target,
        span,
      )
    }
    (Private, _) =>
      fail_unsupported(
        PrivateType,
        FeatureClassification,
        span,
        "private user types are outside the MVP",
      )
    (_, TDalgebraic(_)) =>
      fail_unsupported(
        TypeDeclarationShape,
        FeatureClassification,
        span,
        "user algebraic datatypes are outside the MVP",
      )
    (_, TDrecord(_)) =>
      fail_unsupported(
        TypeDeclarationShape,
        FeatureClassification,
        span,
        "user record types are outside the MVP",
      )
    (_, TDrange(_, _) | TDfloat(_, _)) =>
      fail_unsupported(
        DriverOnlyType,
        FeatureClassification,
        span,
        "Range and Float are restricted to the frozen snapshot",
      )
    (_, TDalias(_)) =>
      fail_unsupported(
        TypeVisibilityShape,
        FeatureClassification,
        span,
        "unsupported visibility for a type alias",
      )
  }
  builder.add_decl(
    @logic.Decl::type_declaration(self.semantic_context, origin, [symbol], span),
    span,
  )
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
      fail_unsupported(
        Ghost,
        FeatureClassification,
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
    match declaration.definition {
      Some(body) =>
        match first_lambda_span(body) {
          Some(span) =>
            fail_unsupported(
              Lambda,
              FeatureClassification,
              Some(span),
              "lambda terms are outside the MVP",
            )
          None => ()
        }
      None => ()
    }
    let prepared = self.prepare_logic(initial_space, declaration)
    typing_space = typing_space.add_logic(
      declaration.ident.name,
      prepared.symbol,
      Some(source_span(declaration.ident.span)),
    )
    pending.push(prepared)
  }
  let definitions : Array[@logic.LogicDefinition] = []
  let definition_origins : Array[@identity.Origin] = []
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
        ) catch {
          TypeError(diagnostic) =>
            if diagnostic.kind == CyclicDefinition {
              fail_unsupported(
                RecursiveOrHigherOrderLogic,
                FeatureClassification,
                diagnostic.span,
                "recursive logic definitions are outside the MVP",
              )
            } else {
              @logic.fail_type(
                diagnostic.kind,
                diagnostic.span,
                diagnostic.message,
              )
            }
        }
        definitions.push(definition)
        definition_origins.push(prepared.symbol.view().origin)
      }
    }
  }
  if !definitions.is_empty() {
    let origin = definition_origins[0]
    builder.add_decl(
      @logic.Decl::logic(
        self.semantic_context,
        origin,
        definitions,
        origin.source_span(),
      ),
      origin.source_span(),
    )
  }
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
  let origin = user_origin(ident)
  let symbol = @logic.PrSymbol::new(self.semantic_context, ident.name, origin)
  let formula = self.formula(builder.current_namespace(), [], [], body)
  builder.add_decl(
    @logic.Decl::proposition(
      self.semantic_context,
      origin,
      parser_proposition_kind(kind),
      symbol,
      formula,
      span,
    ),
    span,
  )
}

///|
fn is_reference_theory_key(key : @theory.TheoryKey) -> Bool {
  let view = key.view()
  view.path.length() == 1 && view.path[0] == b"ref" && view.name == b"Ref"
}

///|
fn resolve_used_theory(
  environment : @environment.Environment,
  qualid : @parser.QualId,
) -> @theory.Theory raise {
  let span = Some(qualid_span(qualid))
  let key = theory_key_of_qualid(qualid)
  if is_reference_theory_key(key) {
    fail_unsupported(
      Reference,
      FeatureClassification,
      span,
      "mutable reference theory cannot be imported by user code",
    )
  }
  if environment.is_driver_only_theory(key) {
    fail_unsupported(
      ExternalOrDriverOnlyImport,
      FeatureClassification,
      span,
      "driver-only theory cannot be imported by user code",
    )
  }
  environment.resolve_theory(key, span)
}

///|
fn PureTyping::add_declaration(
  self : PureTyping,
  builder : @theory.TheoryBuilder,
  declaration : @parser.Decl,
) -> Unit raise {
  match declaration {
    Dtype(declarations) =>
      for declaration in declarations {
        self.add_type_declaration(builder, declaration)
      }
    Dlogic(declarations) => self.add_logic_declarations(builder, declarations)
    Dprop(kind, ident, body) => self.add_proposition(builder, kind, ident, body)
    Duseexport(qualid) =>
      builder.add_use(
        resolve_used_theory(self.environment, qualid),
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
          resolve_used_theory(self.environment, qualid),
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
    Dind(_, _) =>
      fail_unsupported(
        Inductive,
        FeatureClassification,
        None,
        "inductive declarations are outside the MVP",
      )
    Dmeta(ident, _) =>
      fail_unsupported(
        UserMeta,
        FeatureClassification,
        Some(source_span(ident.span)),
        "user meta declarations are outside the MVP",
      )
    Dcloneexport(span, _, _) | Dcloneimport(span, _, _, _, _) =>
      fail_unsupported(
        Clone,
        FeatureClassification,
        Some(source_span(span)),
        "user clone declarations are outside the MVP",
      )
    Dlet(ident, _, _, _) =>
      fail_unsupported(
        ProgramExpression,
        FeatureClassification,
        Some(source_span(ident.span)),
        "program declarations are handled by program elaboration",
      )
    Drec(_) =>
      fail_unsupported(
        Recursion,
        FeatureClassification,
        None,
        "recursive program declarations are outside the MVP",
      )
    Dexn(ident, _, _) =>
      fail_unsupported(
        Exception,
        FeatureClassification,
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
  if unit.kind != Theory {
    fail_unsupported(
      ProgramRoutineShape,
      FeatureClassification,
      Some(source_span(unit.span)),
      "program modules require the program elaborator",
    )
  }
  if unit.interface is Some(_) {
    fail_unsupported(
      AbstractRoutineShape,
      FeatureClassification,
      Some(source_span(unit.span)),
      "module interfaces are outside the MVP",
    )
  }
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], unit.name.name),
    semantic_name(unit.name),
  )
  add_implicit_prelude(environment, builder)
  let typing = PureTyping::new(context, environment)
  for declaration in unit.declarations {
    typing.add_declaration(builder, declaration)
  }
  builder.close()
}

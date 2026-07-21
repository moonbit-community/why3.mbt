// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct ProgramLocal {
  variable : @mlw.PVariable
  delayed : DLocal
}

///|
priv struct ProgramParameterSource {
  span : @parser.Span
  ident : @parser.Ident?
  ghost : Bool
  ty : @parser.Pty
}

///|
/// A routine contract is deliberately retained after parameter typing.  The
/// pre-state scope is sufficient for requires; each ensures branch extends a
/// fresh copy with its result symbol only after the result type is known.
priv struct PendingSpec {
  source : @parser.Spec
  arguments : Array[@mlw.PVariable]
  parameter_scope : Array[(Bytes, ProgramLocal)]
}

///|
priv struct ProgramDecoration {
  location : @identity.SourceSpan
  attributes : Array[Bytes]
}

///|
priv struct ProgramTyping {
  context : @identity.CompilationContext
  environment : @environment.Environment
  pure : PureTyping
}

///|
fn ProgramTyping::new(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
) -> ProgramTyping {
  { context, environment, pure: PureTyping::new(context, environment) }
}

///|
fn program_origin(decoration : ProgramDecoration) -> @identity.Origin {
  @identity.Origin::user(b"", Some(decoration.location), [])
}

///|
fn default_program_decoration(expression : @parser.Expr) -> ProgramDecoration {
  { location: source_span(expression.span), attributes: [] }
}

///|
fn find_program_local(
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
) -> ProgramLocal? {
  for index = locals.length() - 1; index >= 0; index = index - 1 {
    if locals[index].0[:] == name {
      return Some(locals[index].1)
    }
  }
  None
}

///|
fn program_logic_scope(
  locals : ArrayView[(Bytes, ProgramLocal)],
) -> (Array[(Bytes, DLocal)], Array[(Int, @logic.VSymbol)]) {
  let bindings : Array[(Bytes, DLocal)] = []
  let values : Array[(Int, @logic.VSymbol)] = []
  for entry in locals {
    bindings.push((entry.0, entry.1.delayed))
    values.push((entry.1.delayed.id, entry.1.variable.view().pure_symbol))
  }
  (bindings, values)
}

///|
fn program_formula_reads(
  locals : ArrayView[(Bytes, ProgramLocal)],
  formula : @logic.Term,
) -> Array[@mlw.PVariable] {
  let free = formula.free_variables()
  [
    for entry in locals if free.any(variable => {
      variable == entry.1.variable.view().pure_symbol
    }) => entry.1.variable
  ]
}

///|
fn pty_contains_purification(ty : @parser.Pty) -> Bool {
  match ty {
    PTpure(_) => true
    PTtyapp(_, arguments) | PTtuple(arguments) | PTref(arguments) =>
      arguments.any(pty_contains_purification)
    PTarrow(parameter, result) =>
      pty_contains_purification(parameter) || pty_contains_purification(result)
    PTscope(_, nested) | PTparen(nested) => pty_contains_purification(nested)
    PTtyvar(_) => false
  }
}

///|
fn reject_program_purification(ty : @parser.Pty) -> Unit raise ElabError {
  if pty_contains_purification(ty) {
    fail_unsupported(
      TypePurification,
      FeatureClassification,
      None,
      "type purification is outside the program MVP",
    )
  }
}

///|
fn ProgramTyping::program_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  source : @parser.Pty,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  match source {
    PTtuple([]) => {
      let unit_symbol = pure_space.find_type([b"unit"], span)
      return @mlw.Ity::from_ty(
        program_space,
        @logic.Ty::app(unit_symbol, [], span),
        span,
      )
    }
    PTtuple(_) =>
      return fail_unsupported(
        TupleType,
        FeatureClassification,
        span,
        "non-unit tuple program types are outside the MVP",
      )
    _ => ()
  }
  let delayed = self.pure.dty_of_pty(pure_space, source)
  let ty = self.pure.delayed.finalize_strict(delayed, span)
  @mlw.Ity::from_ty(program_space, ty, span)
}

///|
fn anonymous_semantic_name(
  name : BytesView,
  span : @parser.Span,
  attributes : ArrayView[Bytes],
) -> @theory.SemanticName {
  @theory.SemanticName::new(name, attributes, Some(source_span(span)))
}

///|
fn ProgramTyping::make_program_local(
  self : ProgramTyping,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  ity : @mlw.Ity,
  ghost : Bool,
) -> ProgramLocal raise {
  let name = match ident {
    Some(ident) => semantic_name(ident)
    None => anonymous_semantic_name(b"_", fallback_span, [])
  }
  let variable = @mlw.PVariable::trusted_new(
    self.context,
    name,
    ity,
    ghost,
    Some(source_span(fallback_span)),
  )
  let delayed = self.pure.make_local(
    ident,
    fallback_span,
    self.pure.delayed.known(ity.to_ty(Some(source_span(fallback_span))), None),
  )
  { variable, delayed }
}

///|
fn ProgramTyping::prepare_spec(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  parameters : ArrayView[ProgramParameterSource],
  spec : @parser.Spec,
) -> PendingSpec raise {
  let arguments : Array[@mlw.PVariable] = []
  let parameter_scope : Array[(Bytes, ProgramLocal)] = []
  for parameter in parameters {
    reject_program_purification(parameter.ty)
    if parameter.ghost {
      fail_unsupported(
        Ghost,
        FeatureClassification,
        Some(source_span(parameter.span)),
        "ghost program parameters are outside the MVP",
      )
    }
    let span = Some(source_span(parameter.span))
    let ity = self.program_ity(pure_space, program_space, parameter.ty, span)
    let binding = self.make_program_local(
      parameter.ident,
      parameter.span,
      ity,
      false,
    )
    arguments.push(binding.variable)
    if parameter.ident is Some(ident) {
      if find_program_local(parameter_scope, ident.name) is Some(_) {
        @logic.fail_type(
          DuplicateBinder,
          Some(source_span(ident.span)),
          "program routine repeats a parameter name",
        )
      }
      parameter_scope.push((ident.name, binding))
    }
  }
  { source: spec, arguments, parameter_scope }
}

///|
fn validate_program_spec_shape(spec : @parser.Spec) -> Unit raise ElabError {
  if !spec.exceptional_postconditions.is_empty() {
    fail_unsupported(
      Exception,
      FeatureClassification,
      Some(source_span(spec.exceptional_postconditions[0].span)),
      "exceptional postconditions are outside the MVP",
    )
  }
  if !spec.variant.items.is_empty() {
    fail_unsupported(
      Loop,
      FeatureClassification,
      None,
      "variants are outside the nonrecursive program MVP",
    )
  }
  if !spec.reads.is_empty() ||
    !spec.writes.is_empty() ||
    !spec.aliases.is_empty() ||
    spec.check_reads_writes ||
    spec.diverges ||
    spec.partial {
    fail_unsupported(
      ProgramExpression,
      FeatureClassification,
      None,
      "effectful or partial routine contracts are outside the MVP",
    )
  }
}

///|
fn ProgramTyping::type_preconditions(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  pending : PendingSpec,
) -> Array[@logic.Term] raise {
  let (locals, values) = program_logic_scope(pending.parameter_scope)
  [
    for condition in pending.source.preconditions => {
      self.pure.formula(pure_space, locals, values, condition)
    }
  ]
}

///|
fn ProgramTyping::post_result_pattern(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pattern : @parser.Pattern,
  result : @mlw.Ity,
) -> (@parser.Ident?, @parser.Span) raise {
  match pattern.desc {
    Pvar(ident) => (Some(ident), pattern.span)
    Pwild => (None, pattern.span)
    Pparen(inner) | Pscope(_, inner) =>
      self.post_result_pattern(pure_space, program_space, inner, result)
    Pcast(inner, annotation) => {
      let annotated = self.program_ity(
        pure_space,
        program_space,
        annotation,
        Some(source_span(pattern.span)),
      )
      if annotated != result {
        @logic.fail_type(
          TypeMismatch,
          Some(source_span(pattern.span)),
          "postcondition result pattern has the wrong type",
        )
      }
      self.post_result_pattern(pure_space, program_space, inner, result)
    }
    Pghost(_) =>
      fail_unsupported(
        Ghost,
        FeatureClassification,
        Some(source_span(pattern.span)),
        "ghost result patterns are outside the MVP",
      )
    _ =>
      fail_unsupported(
        DestructuringPattern,
        FeatureClassification,
        Some(source_span(pattern.span)),
        "destructuring result patterns are outside the MVP",
      )
  }
}

///|
fn ProgramTyping::type_postconditions(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  result_ity : @mlw.Ity,
) -> Array[@mlw.Postcondition] raise {
  let (parameter_locals, parameter_values) = program_logic_scope(
    pending.parameter_scope,
  )
  let result_ty = result_ity.to_ty(None)
  let result : Array[@mlw.Postcondition] = []
  for postcondition in pending.source.postconditions {
    for branch in postcondition.branches {
      let (ident, fallback_span) = self.post_result_pattern(
        pure_space,
        program_space,
        branch.0,
        result_ity,
      )
      let delayed = self.pure.make_local(
        ident,
        fallback_span,
        self.pure.delayed.known(result_ty, Some(source_span(fallback_span))),
      )
      let result_symbol = @logic.VSymbol::new(
        self.context,
        delayed.name,
        delayed.origin,
        result_ty,
        Some(source_span(fallback_span)),
      )
      let locals = parameter_locals.copy()
      let values = parameter_values.copy()
      locals.push((delayed.name, delayed))
      values.push((delayed.id, result_symbol))
      let formula = self.pure.formula(pure_space, locals, values, branch.1)
      result.push(
        @mlw.Postcondition::trusted_new(
          result_symbol,
          formula,
          Some(source_span(postcondition.span)),
        ),
      )
    }
  }
  result
}

///|
fn ProgramTyping::boolean_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  ignore(self)
  let symbol = pure_space.find_type([b"bool"], span)
  @mlw.Ity::from_ty(program_space, @logic.Ty::app(symbol, [], span), span)
}

///|
fn ProgramTyping::unit_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  ignore(self)
  let symbol = pure_space.find_type([b"unit"], span)
  @mlw.Ity::from_ty(program_space, @logic.Ty::app(symbol, [], span), span)
}

///|
fn ProgramTyping::constant_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  constant : @parser.Constant,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  ignore(self)
  let type_name = match constant {
    ConstInt(_) => b"int"
    ConstReal(_) => b"real"
    ConstStr(_) =>
      return fail_unsupported(
        StringLiteral,
        FeatureClassification,
        Some(decoration.location),
        "string program literals are outside the MVP",
      )
  }
  let symbol = pure_space.find_type([type_name], Some(decoration.location))
  let ity = @mlw.Ity::from_ty(
    program_space,
    @logic.Ty::app(symbol, [], Some(decoration.location)),
    Some(decoration.location),
  )
  @mlw.Expr::constant(
    @logic.Constant::from_parser(constant),
    ity,
    program_origin(decoration),
    decoration.attributes,
  )
}

///|
fn ProgramTyping::zero_argument_pure_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  name : BytesView,
  result : @mlw.Ity,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  ignore(self)
  ignore(program_space)
  let symbol = pure_space.find_logic(
    [name.to_owned()],
    Some(decoration.location),
  )
  let view = symbol.view()
  if !view.argument_types.is_empty() || view.result_type is None {
    @logic.fail_type(
      TypeMismatch,
      Some(decoration.location),
      "expected a zero-argument pure program value",
    )
  }
  @mlw.Expr::pure_application(
    symbol,
    [],
    result,
    program_origin(decoration),
    decoration.attributes,
    Some(decoration.location),
  )
}

///|
fn collect_program_application(
  expression : @parser.Expr,
  reversed : Array[@parser.Expr],
) -> @parser.Expr {
  match expression.desc {
    Eapply(function_, argument) => {
      reversed.push(argument)
      collect_program_application(function_, reversed)
    }
    _ => expression
  }
}

///|
fn ProgramTyping::proxy_argument(
  self : ProgramTyping,
  expression : @mlw.Expr,
  span : @identity.SourceSpan,
) -> (@mlw.PVariable, @mlw.Expr?) raise {
  match expression.view() {
    Evar(variable, _) => (variable, None)
    _ => {
      let proxy = @mlw.PVariable::trusted_new(
        self.context,
        @theory.SemanticName::new(b"o", [b"mlw:proxy_symbol"], Some(span)),
        expression.ity(),
        false,
        Some(span),
      )
      (proxy, Some(expression))
    }
  }
}

///|
fn ProgramTyping::wrap_argument_proxies(
  self : ProgramTyping,
  proxies : ArrayView[(@mlw.PVariable, @mlw.Expr?)],
  body : @mlw.Expr,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  ignore(self)
  let mut result = body
  for index = proxies.length() - 1; index >= 0; index = index - 1 {
    let (binder, value) = proxies[index]
    if value is Some(value) {
      result = @mlw.Expr::let_in(
        binder,
        value,
        result,
        program_origin(decoration),
        decoration.attributes,
        Some(decoration.location),
      )
    }
  }
  result
}

///|
fn ProgramTyping::routine_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let routine = program_space.find_routine(path, span)
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "routine expected \{cty.arguments.length()} arguments but received \{arguments.length()}",
    )
  }
  let typed : Array[@mlw.Expr] = []
  for argument in arguments {
    typed.push(
      self.type_program_expression(pure_space, program_space, locals, argument),
    )
  }
  let mut substitution = @logic.TySubstitution::new()
  for index, argument in typed {
    substitution = substitution.match_type(
      cty.arguments[index].view().ity.to_ty(span),
      argument.ity().to_ty(span),
      span,
    )
  }
  let result_ty = substitution.apply(cty.result.to_ty(span), span)
  if !result_ty.is_closed() {
    @logic.fail_type(
      PolymorphicProgramRoutine,
      span,
      "routine call leaves a residual program type variable",
    )
  }
  let result_ity = @mlw.Ity::from_ty(program_space, result_ty, span)
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  let variables : Array[@mlw.PVariable] = []
  for index, argument in typed {
    let proxy = self.proxy_argument(
      argument,
      source_span(arguments[index].span),
    )
    proxies.push(proxy)
    variables.push(proxy.0)
  }
  let call = @mlw.Expr::routine_call(
    routine,
    variables,
    result_ity,
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, call, decoration)
}

///|
fn ProgramTyping::pure_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let symbol = pure_space.find_logic(path, span)
  let symbol_view = symbol.view()
  if arguments.length() != symbol_view.argument_types.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "logic symbol expected \{symbol_view.argument_types.length()} arguments but received \{arguments.length()}",
    )
  }
  let typed : Array[@mlw.Expr] = []
  let mut substitution = @logic.TySubstitution::new()
  for index, argument in arguments {
    let typed_argument = self.type_program_expression(
      pure_space, program_space, locals, argument,
    )
    typed.push(typed_argument)
    substitution = substitution.match_type(
      symbol_view.argument_types[index],
      typed_argument.ity().to_ty(span),
      span,
    )
  }
  let result_ty = match symbol_view.result_type {
    Some(formal_result) => substitution.apply(formal_result, span)
    None => self.boolean_ity(pure_space, program_space, span).to_ty(span)
  }
  if !result_ty.is_closed() {
    @logic.fail_type(
      PolymorphicProgramRoutine,
      span,
      "pure application leaves a residual program type variable",
    )
  }
  let result_ity = @mlw.Ity::from_ty(program_space, result_ty, span)
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  let variables : Array[@mlw.PVariable] = []
  for index, argument in typed {
    let proxy = self.proxy_argument(
      argument,
      source_span(arguments[index].span),
    )
    proxies.push(proxy)
    variables.push(proxy.0)
  }
  let application = @mlw.Expr::pure_application(
    symbol,
    variables,
    result_ity,
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, application, decoration)
}

///|
fn ProgramTyping::resolved_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  match program_space.find_routine_option(path) {
    Some(_) =>
      self.routine_application(
        pure_space, program_space, locals, path, arguments, decoration,
      )
    None =>
      self.pure_application(
        pure_space, program_space, locals, path, arguments, decoration,
      )
  }
}

///|
fn ProgramTyping::negate_boolean_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  condition : @mlw.Expr,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let boolean = self.boolean_ity(
    pure_space,
    program_space,
    Some(decoration.location),
  )
  let false_value = self.zero_argument_pure_expression(
    pure_space, program_space, b"False", boolean, decoration,
  )
  let true_value = self.zero_argument_pure_expression(
    pure_space, program_space, b"True", boolean, decoration,
  )
  @mlw.Expr::if_then_else(
    condition,
    false_value,
    true_value,
    boolean,
    program_origin(decoration),
    decoration.attributes,
    Some(decoration.location),
  )
}

///|
fn ProgramTyping::type_program_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
) -> @mlw.Expr raise {
  self.type_decorated_program_expression(
    pure_space,
    program_space,
    locals,
    expression,
    default_program_decoration(expression),
  )
}

///|
fn ProgramTyping::type_decorated_program_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  match expression.desc {
    Etrue => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      self.zero_argument_pure_expression(
        pure_space, program_space, b"True", boolean, decoration,
      )
    }
    Efalse => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      self.zero_argument_pure_expression(
        pure_space, program_space, b"False", boolean, decoration,
      )
    }
    Econst(constant) =>
      self.constant_expression(pure_space, program_space, constant, decoration)
    Eident(Qident(ident)) =>
      match find_program_local(locals, ident.name) {
        Some(binding) =>
          @mlw.Expr::variable(
            binding.variable,
            program_origin(decoration),
            decoration.attributes,
          )
        None =>
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            [ident.name],
            [],
            decoration,
          )
      }
    Eident(qualid) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        qualid_segments(qualid),
        [],
        decoration,
      )
    Eidapp(qualid, arguments) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        qualid_segments(qualid),
        arguments,
        decoration,
      )
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let arguments = reversed.rev()
      match head.desc {
        Eident(qualid) =>
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            qualid_segments(qualid),
            arguments,
            decoration,
          )
        Eidapp(qualid, initial) => {
          let all = initial.copy()
          for argument in arguments {
            all.push(argument)
          }
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            qualid_segments(qualid),
            all,
            decoration,
          )
        }
        _ =>
          fail_unsupported(
            HigherOrderApplication,
            FeatureClassification,
            span,
            "higher-order program application is outside the MVP",
          )
      }
    }
    Einfix(left, operator, right) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        [operator.name],
        [left, right],
        decoration,
      )
    Einnfix(left, operator, right) => {
      let comparison = self.resolved_application(
        pure_space,
        program_space,
        locals,
        [operator.name],
        [left, right],
        decoration,
      )
      self.negate_boolean_expression(
        pure_space, program_space, comparison, decoration,
      )
    }
    Elet(ident, ghost, kind, value, body) => {
      if ghost {
        fail_unsupported(
          Ghost,
          FeatureClassification,
          Some(source_span(ident.span)),
          "ghost local bindings are outside the MVP",
        )
      }
      if kind != RKnone {
        fail_unsupported(
          LocalRoutine,
          FeatureClassification,
          Some(source_span(ident.span)),
          "local routines are outside the MVP",
        )
      }
      let value = self.type_program_expression(
        pure_space, program_space, locals, value,
      )
      let binding = self.make_program_local(
        Some(ident),
        ident.span,
        value.ity(),
        false,
      )
      let nested = locals.to_owned()
      nested.push((ident.name, binding))
      let body = self.type_program_expression(
        pure_space, program_space, nested, body,
      )
      @mlw.Expr::let_in(
        binding.variable,
        value,
        body,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Esequence(first, second) => {
      let first = self.type_program_expression(
        pure_space, program_space, locals, first,
      )
      let binder = self.make_program_local(
        None,
        expression.span,
        first.ity(),
        false,
      )
      let second = self.type_program_expression(
        pure_space, program_space, locals, second,
      )
      @mlw.Expr::let_in(
        binder.variable,
        first,
        second,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eif(condition, consequent, alternative) => {
      let condition = self.type_program_expression(
        pure_space, program_space, locals, condition,
      )
      let consequent = self.type_program_expression(
        pure_space, program_space, locals, consequent,
      )
      let alternative = self.type_program_expression(
        pure_space, program_space, locals, alternative,
      )
      let boolean = self.boolean_ity(pure_space, program_space, span)
      if condition.ity() != boolean || consequent.ity() != alternative.ity() {
        @logic.fail_type(
          TypeMismatch,
          span,
          "program conditional has incompatible condition or branch types",
        )
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eand(left, right) => {
      let condition = self.type_program_expression(
        pure_space, program_space, locals, left,
      )
      let consequent = self.type_program_expression(
        pure_space, program_space, locals, right,
      )
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let alternative = self.zero_argument_pure_expression(
        pure_space, program_space, b"False", boolean, decoration,
      )
      if condition.ity() != boolean || consequent.ity() != boolean {
        @logic.fail_type(TypeMismatch, span, "boolean conjunction expected")
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eor(left, right) => {
      let condition = self.type_program_expression(
        pure_space, program_space, locals, left,
      )
      let alternative = self.type_program_expression(
        pure_space, program_space, locals, right,
      )
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let consequent = self.zero_argument_pure_expression(
        pure_space, program_space, b"True", boolean, decoration,
      )
      if condition.ity() != boolean || alternative.ity() != boolean {
        @logic.fail_type(TypeMismatch, span, "boolean disjunction expected")
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Enot(inner) => {
      let condition = self.type_program_expression(
        pure_space, program_space, locals, inner,
      )
      self.negate_boolean_expression(
        pure_space, program_space, condition, decoration,
      )
    }
    Eassert(kind, formula) => {
      if kind is Check {
        fail_unsupported(
          CheckAssertion,
          FeatureClassification,
          span,
          "check assertions are outside the MVP",
        )
      }
      let (logic_locals, logic_values) = program_logic_scope(locals)
      let formula = self.pure.formula(
        pure_space, logic_locals, logic_values, formula,
      )
      let reads = program_formula_reads(locals, formula)
      let unit = self.unit_ity(pure_space, program_space, span)
      match kind {
        Assert =>
          @mlw.Expr::assert_formula(
            formula,
            reads,
            unit,
            program_origin(decoration),
            decoration.attributes,
            span,
          )
        Assume =>
          @mlw.Expr::assume_formula(
            formula,
            reads,
            unit,
            program_origin(decoration),
            decoration.attributes,
            span,
          )
        Check => abort("check assertion handled above")
      }
    }
    Escope(qualid, inner) => {
      let scope_span = Some(qualid_span(qualid))
      self.type_decorated_program_expression(
        pure_space.import_scope(qualid_segments(qualid), scope_span),
        program_space.import_scope(qualid_segments(qualid), scope_span),
        locals,
        inner,
        decoration,
      )
    }
    Ecast(inner, annotation) => {
      let inner = self.type_decorated_program_expression(
        pure_space, program_space, locals, inner, decoration,
      )
      let expected = self.program_ity(
        pure_space, program_space, annotation, span,
      )
      if inner.ity() != expected {
        @logic.fail_type(TypeMismatch, span, "program cast has the wrong type")
      }
      inner
    }
    Eattr(attribute, inner) => {
      let nested = match attribute {
        Text(text) => {
          let attributes = decoration.attributes.copy()
          attributes.push(checked_text_attribute(text, span))
          { ..decoration, attributes, }
        }
        Position(position) => { ..decoration, location: source_span(position) }
      }
      self.type_decorated_program_expression(
        pure_space, program_space, locals, inner, nested,
      )
    }
    Etuple([]) => {
      let unit = self.unit_ity(pure_space, program_space, span)
      self.zero_argument_pure_expression(
        pure_space, program_space, b"Tuple0", unit, decoration,
      )
    }
    Etuple(_) =>
      fail_unsupported(
        TupleExpression,
        FeatureClassification,
        span,
        "non-unit tuple expressions are outside the MVP",
      )
    Eoptexn(ident, MaskVisible, inner) if ident.name == b"'Return" =>
      self.type_decorated_program_expression(
        pure_space, program_space, locals, inner, decoration,
      )
    Ewhile(_, _, _, _) | Efor(_, _, _, _, _, _) =>
      fail_unsupported(
        Loop,
        FeatureClassification,
        span,
        "program loops are outside the MVP",
      )
    Erec(_, _) =>
      fail_unsupported(
        Recursion,
        FeatureClassification,
        span,
        "recursive local routines are outside the MVP",
      )
    Eraise(_, _) | Eexn(_, _, _, _) | Eoptexn(_, _, _) =>
      fail_unsupported(
        Exception,
        FeatureClassification,
        span,
        "program exceptions are outside the MVP",
      )
    Eghost(_) =>
      fail_unsupported(
        Ghost,
        FeatureClassification,
        span,
        "ghost program expressions are outside the MVP",
      )
    Eref | Easref(_) | Eassign(_) =>
      fail_unsupported(
        Reference,
        FeatureClassification,
        span,
        "mutable references are outside the MVP",
      )
    Efun(_, _, _, _, _, _) | Eany(_, _, _, _, _, _) =>
      fail_unsupported(
        ProgramExpression,
        FeatureClassification,
        span,
        "first-class program routines are outside the MVP",
      )
    Eidpur(qualid) =>
      self.pure_application(
        pure_space,
        program_space,
        locals,
        qualid_segments(qualid),
        [],
        decoration,
      )
    Epure(_) =>
      fail_unsupported(
        NestedUnsupportedExpression,
        FeatureClassification,
        span,
        "this pure-expression form is outside the typed program MVP",
      )
    Elabel(_, _) =>
      fail_unsupported(
        OldAt,
        FeatureClassification,
        span,
        "labels and old/at expressions are outside the MVP",
      )
    Ematch(_, _, _) | Eabsurd | Erecord(_) | Eupdate(_, _) =>
      fail_unsupported(
        ProgramExpression,
        FeatureClassification,
        span,
        "unsupported program expression shape",
      )
  }
}

///|
fn validate_program_mask(
  mask : @parser.Mask,
  span : @identity.SourceSpan?,
) -> Unit raise ElabError {
  match mask {
    MaskVisible => ()
    MaskGhost | MaskTuple(_) =>
      fail_unsupported(
        Ghost,
        FeatureClassification,
        span,
        "ghost or tuple result masks are outside the MVP",
      )
  }
}

///|
fn validate_routine_result_pattern(
  pattern : @parser.Pattern,
) -> Unit raise ElabError {
  match pattern.desc {
    Pwild | Pvar(_) => ()
    Pparen(inner) | Pscope(_, inner) => validate_routine_result_pattern(inner)
    Pcast(inner, _) => validate_routine_result_pattern(inner)
    Pghost(_) =>
      fail_unsupported(
        Ghost,
        FeatureClassification,
        Some(source_span(pattern.span)),
        "ghost routine results are outside the MVP",
      )
    _ =>
      fail_unsupported(
        DestructuringPattern,
        FeatureClassification,
        Some(source_span(pattern.span)),
        "destructuring routine results are outside the MVP",
      )
  }
}

///|
fn ProgramTyping::add_routine(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  ident : @parser.Ident,
  ghost : Bool,
  kind : @parser.RoutineKind,
  parameters : ArrayView[ProgramParameterSource],
  return_type : @parser.Pty?,
  return_pattern : @parser.Pattern,
  mask : @parser.Mask,
  spec : @parser.Spec,
  body : @parser.Expr?,
) -> Unit raise {
  for parameter in parameters {
    reject_program_purification(parameter.ty)
  }
  if return_type is Some(return_type) {
    reject_program_purification(return_type)
  }
  if ghost {
    fail_unsupported(
      Ghost,
      FeatureClassification,
      Some(source_span(ident.span)),
      "ghost routines are outside the MVP",
    )
  }
  if kind != RKnone {
    fail_unsupported(
      RoutineKind,
      FeatureClassification,
      Some(source_span(ident.span)),
      "only ordinary RLnone routines are supported",
    )
  }
  validate_program_mask(mask, Some(source_span(return_pattern.span)))
  validate_routine_result_pattern(return_pattern)
  validate_program_spec_shape(spec)
  guard return_type is Some(return_type) else {
    fail_unsupported(
      ProgramRoutineShape,
      FeatureClassification,
      Some(source_span(ident.span)),
      "program routine requires an explicit result type",
    )
  }
  let pure_space = builder.pure_namespace()
  let program_space = builder.program_namespace()
  let pending = self.prepare_spec(pure_space, program_space, parameters, spec)
  let result = self.program_ity(
    pure_space,
    program_space,
    return_type,
    Some(source_span(return_pattern.span)),
  )
  let preconditions = self.type_preconditions(pure_space, pending)
  let postconditions = self.type_postconditions(
    pure_space, program_space, pending, result,
  )
  let cty = @mlw.Cty::trusted_new(
    result.context_anchor(),
    pending.arguments,
    pending.arguments,
    preconditions,
    postconditions,
    @mlw.Effect::pure(false),
    result,
    Visible,
    Some(source_span(ident.span)),
  )
  let routine = @mlw.RoutineSymbol::new_user(
    self.context,
    ident.name,
    user_origin(ident),
    cty,
    Some(source_span(ident.span)),
  )
  let computation = match body {
    None => @mlw.ProgramComputation::Cany(cty)
    Some(body) => {
      let typed = self.type_program_expression(
        pure_space,
        program_space,
        pending.parameter_scope,
        body,
      )
      if typed.ity() != result {
        @logic.fail_type(
          TypeMismatch,
          Some(source_span(body.span)),
          "routine body and declared result have different types",
        )
      }
      Cfun(cty, Some(typed))
    }
  }
  builder.add_program_decl(
    routine,
    computation,
    [],
    Some(source_span(ident.span)),
  )
}

///|
fn ProgramTyping::add_top_level_routine(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  ident : @parser.Ident,
  ghost : Bool,
  kind : @parser.RoutineKind,
  expression : @parser.Expr,
) -> Unit raise {
  match expression.desc {
    Efun(binders, return_type, return_pattern, mask, spec, body) => {
      let parameters : Array[ProgramParameterSource] = []
      for binder in binders {
        guard binder.binder_type is Some(ty) else {
          return fail_unsupported(
            ProgramRoutineShape,
            FeatureClassification,
            Some(source_span(binder.span)),
            "program parameters require explicit types",
          )
        }
        parameters.push({
          span: binder.span,
          ident: binder.ident,
          ghost: binder.ghost,
          ty,
        })
      }
      self.add_routine(
        builder,
        ident,
        ghost,
        kind,
        parameters,
        return_type,
        return_pattern,
        mask,
        spec,
        Some(body),
      )
    }
    Eany(params, inner_kind, return_type, return_pattern, mask, spec) => {
      let parameters = [
        for parameter in params => {
          ProgramParameterSource::{
            span: parameter.span,
            ident: parameter.ident,
            ghost: parameter.ghost,
            ty: parameter.param_type,
          }
        }
      ]
      // For `val function`, Why3 keeps the declaration-level Dlet kind
      // ordinary and records the refined kind on Eany.  Pass that semantic
      // kind onward; add_routine intentionally checks type purification
      // before classifying the kind.
      let effective_kind = if inner_kind != RKnone { inner_kind } else { kind }
      self.add_routine(
        builder,
        ident,
        ghost,
        effective_kind,
        parameters,
        return_type,
        return_pattern,
        mask,
        spec,
        None,
      )
    }
    _ =>
      fail_unsupported(
        ProgramRoutineShape,
        FeatureClassification,
        Some(source_span(expression.span)),
        "top-level program declaration is not a let/val routine",
      )
  }
}

///|
fn resolve_used_module(
  environment : @environment.Environment,
  qualid : @parser.QualId,
) -> @mlw.Pmodule raise {
  let key = theory_key_of_qualid(qualid)
  let span = Some(qualid_span(qualid))
  if is_reference_theory_key(key) {
    fail_unsupported(
      Reference,
      FeatureClassification,
      span,
      "mutable reference module cannot be imported by user code",
    )
  }
  if environment.is_driver_only_theory(key) {
    fail_unsupported(
      DriverOnlyTheory,
      FeatureClassification,
      span,
      "driver-only module cannot be imported by user code",
    )
  }
  environment.resolve_module(key, span)
}

///|
/// Classifies syntax-level exclusions before name resolution.  In particular,
/// a loop must remain `UnsupportedFeature(Loop)` even when its body also uses
/// a module that is outside the frozen MVP root set.
fn classify_nested_program_expression(
  expression : @parser.Expr,
) -> Unit raise ElabError {
  let span = Some(source_span(expression.span))
  match expression.desc {
    Ewhile(condition, _, _, body) => {
      ignore(condition)
      ignore(body)
      fail_unsupported(Loop, FeatureClassification, span, "while loop")
    }
    Efor(_, _, _, _, _, _) =>
      fail_unsupported(Loop, FeatureClassification, span, "for loop")
    Erec(_, _) =>
      fail_unsupported(
        Recursion,
        FeatureClassification,
        span,
        "local recursion",
      )
    Eraise(_, _) | Eexn(_, _, _, _) =>
      fail_unsupported(
        Exception,
        FeatureClassification,
        span,
        "exception expression",
      )
    Eoptexn(ident, MaskVisible, inner) if ident.name == b"'Return" ||
      ident.name == b"'Break" ||
      ident.name == b"'Continue" => classify_nested_program_expression(inner)
    Eoptexn(_, _, _) =>
      fail_unsupported(
        Exception,
        FeatureClassification,
        span,
        "optional exception",
      )
    Eghost(_) =>
      fail_unsupported(Ghost, FeatureClassification, span, "ghost expression")
    Eref | Easref(_) | Eassign(_) =>
      fail_unsupported(
        Reference,
        FeatureClassification,
        span,
        "mutable expression",
      )
    Eassert(Check, _) =>
      fail_unsupported(
        CheckAssertion,
        FeatureClassification,
        span,
        "check assertion",
      )
    Elet(ident, ghost, kind, value, body) => {
      if ghost {
        fail_unsupported(
          Ghost,
          FeatureClassification,
          Some(source_span(ident.span)),
          "ghost local binding",
        )
      }
      if kind != RKnone {
        fail_unsupported(
          LocalRoutine,
          FeatureClassification,
          Some(source_span(ident.span)),
          "local routine binding",
        )
      }
      classify_nested_program_expression(value)
      classify_nested_program_expression(body)
    }
    Efun(_, _, _, _, _, _) | Eany(_, _, _, _, _, _) =>
      fail_unsupported(
        ProgramExpression,
        FeatureClassification,
        span,
        "nested routine expression",
      )
    Elabel(_, _) =>
      fail_unsupported(
        OldAt,
        FeatureClassification,
        span,
        "labels and old/at expressions are outside the MVP",
      )
    Ematch(_, _, _) | Eabsurd | Erecord(_) | Eupdate(_, _) =>
      fail_unsupported(
        ProgramExpression,
        FeatureClassification,
        span,
        "unsupported program expression",
      )
    Eapply(function_, argument)
    | Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Esequence(function_, argument)
    | Eand(function_, argument)
    | Eor(function_, argument) => {
      classify_nested_program_expression(function_)
      classify_nested_program_expression(argument)
    }
    Eidapp(_, arguments) | Etuple(arguments) =>
      for argument in arguments {
        classify_nested_program_expression(argument)
      }
    Eif(condition, consequent, alternative) => {
      classify_nested_program_expression(condition)
      classify_nested_program_expression(consequent)
      classify_nested_program_expression(alternative)
    }
    Enot(inner) | Escope(_, inner) | Ecast(inner, _) | Eattr(_, inner) =>
      classify_nested_program_expression(inner)
    Eassert(_, _)
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Epure(_)
    | Eidpur(_) => ()
  }
}

///|
fn classify_program_module_syntax(
  unit : @parser.MlwModule,
) -> Unit raise ElabError {
  for declaration in unit.declarations {
    match declaration {
      Drec(_) =>
        fail_unsupported(
          Recursion,
          FeatureClassification,
          None,
          "recursive program declaration",
        )
      Dexn(ident, _, _) =>
        fail_unsupported(
          Exception,
          FeatureClassification,
          Some(source_span(ident.span)),
          "program exception declaration",
        )
      Dlet(_, _, _, expression) =>
        match expression.desc {
          Efun(_, _, _, _, _, body) => classify_nested_program_expression(body)
          Eany(_, _, _, _, _, _) => ()
          _ => classify_nested_program_expression(expression)
        }
      _ => ()
    }
  }
}

///|
fn ProgramTyping::add_module_declaration(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.Decl,
) -> Unit raise {
  match declaration {
    Dlet(ident, ghost, kind, expression) =>
      self.add_top_level_routine(builder, ident, ghost, kind, expression)
    Duseexport(qualid) =>
      builder.add_use(
        resolve_used_module(self.environment, qualid),
        true,
        Some(qualid_span(qualid)),
      )
    Duseimport(span, import_, uses) =>
      for use_ in uses {
        let (qualid, renaming) = use_
        if renaming is Some(renaming) &&
          renaming.name != qualid_last(qualid).name {
          fail_unsupported(
            ExternalOrDriverOnlyImport,
            FeatureClassification,
            Some(source_span(renaming.span)),
            "renamed program imports are outside the MVP",
          )
        }
        let scope_name = match renaming {
          Some(renaming) => renaming.name
          None => qualid_last(qualid).name
        }
        builder.add_scoped_use(
          scope_name,
          resolve_used_module(self.environment, qualid),
          import_ || renaming is None,
          Some(source_span(span)),
        )
      }
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
        "program exceptions are outside the MVP",
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
        "program clones are outside the MVP",
      )
    Dind(_, _) =>
      fail_unsupported(
        Inductive,
        FeatureClassification,
        None,
        "program inductive declarations are outside the MVP",
      )
    Dtype(_) | Dlogic(_) | Dprop(_, _, _) =>
      fail_unsupported(
        TypeDeclarationShape,
        FeatureClassification,
        None,
        "user pure declarations inside modules are outside the MVP",
      )
    Dimport(qualid) =>
      fail_unsupported(
        ExternalOrDriverOnlyImport,
        FeatureClassification,
        Some(qualid_span(qualid)),
        "standalone program-scope imports are outside the MVP",
      )
    Dscope(span, _, _, _) =>
      fail_unsupported(
        ProgramRoutineShape,
        FeatureClassification,
        Some(source_span(span)),
        "nested program module scopes are outside the MVP",
      )
  }
}

///|
fn add_implicit_program_prelude(
  environment : @environment.Environment,
  builder : @mlw.PmoduleBuilder,
) -> Unit raise {
  for name in [b"BuiltIn", b"Bool", b"Unit"] {
    let key = @theory.TheoryKey::new([], name)
    builder.add_use(environment.resolve_module(key, None), true, None)
  }
}

///|
fn elaborate_program_unit_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @mlw.Pmodule raise {
  if unit.kind != Module {
    fail_unsupported(
      ProgramRoutineShape,
      FeatureClassification,
      Some(source_span(unit.span)),
      "theory unit was sent to the program elaborator",
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
  classify_program_module_syntax(unit)
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([], unit.name.name),
    semantic_name(unit.name),
  )
  add_implicit_program_prelude(environment, builder)
  let typing = ProgramTyping::new(context, environment)
  for declaration in unit.declarations {
    typing.add_module_declaration(builder, declaration)
  }
  builder.close()
}

///|
fn[A] normalize_program_elaboration_errors(
  action : () -> A raise,
) -> A raise ElabError {
  action() catch {
    @logic.TypeError(diagnostic) => {
      let normalized = type_failure_diagnostic(diagnostic)
      raise ElabError({ ..normalized, stage: ProgramTyping })
    }
    @theory.TheoryError(diagnostic) =>
      raise ElabError(theory_failure_diagnostic(diagnostic))
    @environment.EnvironmentError(diagnostic) =>
      raise ElabError(environment_failure_diagnostic(diagnostic, ProgramTyping))
    @mlw.MlwError(diagnostic) =>
      raise ElabError(program_failure_diagnostic(diagnostic))
    ElabError(diagnostic) => raise ElabError(diagnostic)
    _ => abort("unexpected program elaboration error escaped a typed boundary")
  }
}

///|
pub fn elaborate_program_unit(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @mlw.Pmodule raise ElabError {
  normalize_program_elaboration_errors(() => {
    elaborate_program_unit_raw(context, environment, unit)
  })
}

///|
pub(all) enum ElaboratedUnitView {
  ElaboratedTheory(@theory.Theory)
  ElaboratedModule(@mlw.Pmodule)
}

///|
struct ElaboratedFile {
  units : Array[ElaboratedUnitView]
}

///|
pub fn ElaboratedFile::units(
  self : ElaboratedFile,
) -> ArrayView[ElaboratedUnitView] {
  self.units[:]
}

///|
fn elaborate_file_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> ElaboratedFile raise {
  guard file is Modules(source_units) else {
    fail_unsupported(
      ProgramRoutineShape,
      FeatureClassification,
      None,
      "anonymous declaration files are outside the MVP",
    )
  }
  let units : Array[ElaboratedUnitView] = []
  for unit in source_units {
    match unit.kind {
      Theory => {
        let theory = elaborate_pure_unit(context, environment, unit)
        environment.register_theory(
          theory,
          true,
          Some(source_span(unit.name.span)),
        )
        units.push(ElaboratedTheory(theory))
      }
      Module => {
        let pmodule = elaborate_program_unit(context, environment, unit)
        environment.register_theory(
          pmodule.pure_theory(),
          true,
          Some(source_span(unit.name.span)),
        )
        environment.register_module(
          pmodule,
          true,
          Some(source_span(unit.name.span)),
        )
        units.push(ElaboratedModule(pmodule))
      }
    }
  }
  { units, }
}

///|
/// Elaborates pure theories and program modules in their original file order.
pub fn elaborate_file(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> ElaboratedFile raise ElabError {
  normalize_program_elaboration_errors(() => {
    elaborate_file_raw(context, environment, file)
  })
}

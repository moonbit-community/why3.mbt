// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv enum DTermNode {
  DLocalTerm(DLocal)
  DConstantTerm(@logic.Constant)
  DGlobalApplication(@logic.LSymbol, Array[DTerm])
  DFunctionApplication(DTerm, DTerm)
  DIfTerm(DTerm, DTerm, DTerm)
  DLetTerm(DLocal, DTerm, DTerm)
  DCaseTerm(DTerm, Array[(DPattern, DTerm)])
  DEpsilonTerm(DLocal, DTerm)
  DQuantifiedTerm(@parser.Quantifier, Array[DLocal], Array[Array[DTerm]], DTerm)
  DBinaryTerm(@parser.BinaryLogicOp, DTerm, DTerm)
  DNotTerm(DTerm)
  DAtTerm(DTerm, Bytes)
  DTrueTerm
  DFalseTerm
  DCastTerm(DTerm)
}

///|
priv enum DPatternNode {
  DWildPattern
  DVariablePattern(DLocal)
  DApplicationPattern(@logic.LSymbol, Array[DPattern])
  DOrPattern(DPattern, DPattern)
  DAsPattern(DPattern, DLocal)
  DCastPattern(DPattern)
}

///|
priv struct DPattern {
  node : DPatternNode
  ty : Dty
  bindings : Array[(Bytes, DLocal)]
  source_span : @identity.SourceSpan?
}

///|
priv struct DTerm {
  node : DTermNode
  result_type : Dty?
  source_span : @identity.SourceSpan?
  attributes : Array[Bytes]
  missing_arguments : Int
}

///|
priv struct DAtValue {
  local_id : Int
  label : Bytes
  value : @logic.VSymbol
}

///|
fn make_dterm(
  node : DTermNode,
  result_type : Dty?,
  span : @parser.Span,
) -> DTerm {
  {
    node,
    result_type,
    source_span: Some(source_span(span)),
    attributes: [],
    missing_arguments: 0,
  }
}

///|
fn PureTyping::named_type(
  self : PureTyping,
  space : @theory.Namespace,
  name : BytesView,
  span : @identity.SourceSpan?,
) -> (Dty, @logic.Ty) raise {
  let symbol = space.find_type([name.to_owned()], span)
  let semantic = @logic.Ty::app(symbol, [], span)
  (self.delayed.known(semantic, span), semantic)
}

///|
fn PureTyping::boolean_dty(
  self : PureTyping,
  space : @theory.Namespace,
  span : @identity.SourceSpan?,
) -> Dty raise {
  self.named_type(space, b"bool", span).0
}

///|
fn PureTyping::expect_value(
  self : PureTyping,
  space : @theory.Namespace,
  term : DTerm,
  expected : Dty,
) -> DTerm raise {
  match term.result_type {
    Some(_) => {
      let mut coerced = match (term.node, self.delayed.head_symbol(expected)) {
        (DConstantTerm(ConstInt(_)), Some(symbol)) if symbol.view().definition
          is Range(_, _) => { ..term, result_type: Some(expected) }
        (DConstantTerm(ConstReal(_)), Some(symbol)) if symbol.view().definition
          is Float(_, _) => { ..term, result_type: Some(expected) }
        _ => term
      }
      guard coerced.result_type is Some(actual) else {
        abort("value coercion lost its delayed result type")
      }
      match
        (self.delayed.head_symbol(actual), self.delayed.head_symbol(expected)) {
        (Some(source), Some(target)) if source != target =>
          match self.coercions.find_by_symbols(source, target) {
            Some(functions) =>
              for function_ in functions {
                let (parameters, result) = self.specialized_symbol_types(
                  function_,
                  coerced.source_span,
                )
                guard parameters is [parameter] &&
                  result is Some(result_type) &&
                  coerced.result_type is Some(actual_type) else {
                  @logic.fail_type(
                    InvalidDeclaration,
                    coerced.source_span,
                    "registered coercion is not a unary logic function",
                  )
                }
                self.delayed.unify_expected(
                  actual_type,
                  parameter,
                  coerced.source_span,
                )
                coerced = {
                  node: DGlobalApplication(function_, [coerced]),
                  result_type: Some(result_type),
                  source_span: coerced.source_span,
                  attributes: [b"coercion"],
                  missing_arguments: coerced.missing_arguments,
                }
              }
            None => ()
          }
        _ => ()
      }
      guard coerced.result_type is Some(actual) else {
        abort("value coercion lost its delayed result type")
      }
      self.delayed.unify_expected(actual, expected, coerced.source_span) catch {
        @logic.TypeError(diagnostic) =>
          if coerced.missing_arguments > 0 && diagnostic.kind == TypeMismatch {
            raise @logic.TypeError({ ..diagnostic, kind: ArityMismatch })
          } else {
            raise @logic.TypeError(diagnostic)
          }
      }
      coerced
    }
    None => {
      let boolean = self.boolean_dty(space, term.source_span)
      self.delayed.unify_expected(boolean, expected, term.source_span)
      term
    }
  }
}

///|
fn PureTyping::expect_formula(
  self : PureTyping,
  space : @theory.Namespace,
  term : DTerm,
) -> Unit raise {
  match term.result_type {
    None => ()
    Some(actual) => {
      let boolean = self.boolean_dty(space, term.source_span)
      self.delayed.unify_expected(actual, boolean, term.source_span)
    }
  }
}

///|
fn PureTyping::specialized_symbol_types(
  self : PureTyping,
  symbol : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> (Array[Dty], Dty?) raise @logic.TypeError {
  let variables : Map[@logic.TyVarSymbol, Dty] = Map([])
  let view = symbol.view()
  let arguments = [
    for argument in view.argument_types => {
      self.delayed.specialize(argument, variables, span)
    }
  ]
  let result = match view.result_type {
    None => None
    Some(result) => Some(self.delayed.specialize(result, variables, span))
  }
  (arguments, result)
}

///|
fn PureTyping::global_application(
  self : PureTyping,
  space : @theory.Namespace,
  symbol : @logic.LSymbol,
  arguments : Array[DTerm],
  span : @parser.Span,
) -> DTerm raise {
  let semantic_span = Some(source_span(span))
  let view = symbol.view()
  if arguments.length() != view.argument_types.length() {
    @logic.fail_type_with_types(
      ArityMismatch,
      semantic_span,
      application_actual_type(symbol, arguments.length()),
      application_expected_type(symbol),
      "logic symbol expected \{view.argument_types.length()} arguments but received \{arguments.length()}",
    )
  }
  if view.name == b"infix =" &&
    arguments.length() == 2 &&
    (arguments[0].result_type is None || arguments[1].result_type is None) {
    self.expect_formula(space, arguments[0])
    self.expect_formula(space, arguments[1])
    return make_dterm(DGlobalApplication(symbol, arguments), None, span)
  }
  let (formal_arguments, result) = self.specialized_symbol_types(
    symbol, semantic_span,
  )
  // Why3's equality constructor first selects a maximal operand type under
  // the coercion relation. Unrelated ground types retain the right-biased
  // diagnostic behavior.
  if view.name == b"infix =" &&
    arguments.length() == 2 &&
    arguments[0].result_type is Some(left) &&
    arguments[1].result_type is Some(right) {
    let preferred = match
      (self.delayed.head_symbol(left), self.delayed.head_symbol(right)) {
      (Some(left_symbol), Some(right_symbol)) =>
        if self.coercions.find_by_symbols(left_symbol, right_symbol) is Some(_) {
          right
        } else if self.coercions.find_by_symbols(right_symbol, left_symbol)
          is Some(_) {
          left
        } else {
          right
        }
      _ => right
    }
    self.delayed.unify_expected(
      preferred,
      formal_arguments[0],
      arguments[1].source_span,
    )
  }
  for index, argument in arguments {
    arguments[index] = self.expect_value(
      space,
      argument,
      formal_arguments[index],
    )
  }
  make_dterm(DGlobalApplication(symbol, arguments), result, span)
}

///|
fn PureTyping::function_application(
  self : PureTyping,
  space : @theory.Namespace,
  function_ : DTerm,
  argument : DTerm,
  span : @parser.Span,
) -> DTerm raise {
  guard function_.result_type is Some(function_type) else {
    @logic.fail_type(
      FunctionExpected,
      function_.source_span,
      "formula cannot be applied as a function",
    )
  }
  let parameter = self.delayed.fresh()
  let result = self.delayed.fresh()
  let function_symbol = Some(
    space.find_type([b"infix ->"], Some(source_span(span))),
  ) catch {
    _ => None
  }
  let function_ = match function_symbol {
    Some(function_symbol) => {
      let arrow = self.delayed.app(
        function_symbol,
        [parameter, result],
        Some(source_span(span)),
      )
      self.expect_value(space, function_, arrow)
    }
    None => {
      let arrow = self.delayed.arrow(parameter, result, Some(source_span(span)))
      self.delayed.unify_expected(function_type, arrow, function_.source_span)
      function_
    }
  }
  let argument = self.expect_value(space, argument, parameter)
  {
    ..make_dterm(DFunctionApplication(function_, argument), Some(result), span),
    missing_arguments: Int::max(function_.missing_arguments - 1, 0),
  }
}

///|
fn find_pattern_binding(
  bindings : ArrayView[(Bytes, DLocal)],
  name : BytesView,
) -> DLocal? {
  for entry in bindings {
    if entry.0[:] == name {
      return Some(entry.1)
    }
  }
  None
}

///|
fn merge_pattern_bindings(
  patterns : ArrayView[DPattern],
  span : @identity.SourceSpan?,
) -> Array[(Bytes, DLocal)] raise @logic.TypeError {
  let result : Array[(Bytes, DLocal)] = []
  for pattern in patterns {
    for entry in pattern.bindings {
      if find_pattern_binding(result, entry.0) is Some(_) {
        @logic.fail_type(
          DuplicateBinder,
          span,
          "pattern binds the same variable more than once",
        )
      }
      result.push(entry)
    }
  }
  result
}

///|
fn PureTyping::expect_pattern(
  self : PureTyping,
  pattern : DPattern,
  expected : Dty,
) -> Unit raise @logic.TypeError {
  self.delayed.unify_expected(pattern.ty, expected, pattern.source_span)
}

///|
fn PureTyping::constructor_pattern(
  self : PureTyping,
  symbol : @logic.LSymbol,
  arguments : Array[DPattern],
  span : @parser.Span,
) -> DPattern raise {
  let semantic_span = Some(source_span(span))
  guard symbol.view().role is Constructor(_) else {
    @logic.fail_type(
      InvalidDeclaration,
      semantic_span,
      "pattern application requires a constructor",
    )
  }
  let (formal_arguments, result) = self.specialized_symbol_types(
    symbol, semantic_span,
  )
  if arguments.length() != formal_arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      semantic_span,
      "constructor pattern has the wrong arity",
    )
  }
  for index, argument in arguments {
    self.expect_pattern(argument, formal_arguments[index])
  }
  guard result is Some(result) else {
    @logic.fail_type(
      FunctionExpected,
      semantic_span,
      "constructor pattern requires a value result",
    )
  }
  {
    node: DApplicationPattern(symbol, arguments),
    ty: result,
    bindings: merge_pattern_bindings(arguments, semantic_span),
    source_span: semantic_span,
  }
}

///|
fn tuple_constructor_name(arity : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"Tuple")
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn tuple_type_name(arity : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"tuple")
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn PureTyping::record_pattern(
  self : PureTyping,
  space : @theory.Namespace,
  fields : ArrayView[(@parser.QualId, @parser.Pattern)],
  span : @parser.Span,
) -> DPattern raise {
  let semantic_span = Some(source_span(span))
  let resolved : Array[(@logic.LSymbol, @parser.Pattern)] = []
  for field in fields {
    resolved.push(
      (
        space.find_logic(qualid_segments(field.0), Some(qualid_span(field.0))),
        field.1,
      ),
    )
  }
  let symbols = resolved.map(entry => entry.0)
  let (data_constructor, projections) = self.known.record_layout(
    symbols, semantic_span,
  )
  let values : Map[@logic.LSymbol, @parser.Pattern] = Map([])
  for entry in resolved {
    values[entry.0] = entry.1
  }
  let constructor_symbol = data_constructor.view().symbol
  let (formal_arguments, _) = self.specialized_symbol_types(
    constructor_symbol, semantic_span,
  )
  let arguments : Array[DPattern] = []
  for index, projection in projections {
    match values.get(projection) {
      Some(pattern) => arguments.push(self.type_pattern(space, pattern))
      None =>
        arguments.push({
          node: DWildPattern,
          ty: formal_arguments[index],
          bindings: [],
          source_span: semantic_span,
        })
    }
  }
  self.constructor_pattern(constructor_symbol, arguments, span)
}

///|
fn PureTyping::type_pattern(
  self : PureTyping,
  space : @theory.Namespace,
  pattern : @parser.Pattern,
) -> DPattern raise {
  let semantic_span = Some(source_span(pattern.span))
  match pattern.desc {
    Pwild =>
      {
        node: DWildPattern,
        ty: self.delayed.fresh(),
        bindings: [],
        source_span: semantic_span,
      }
    Pvar(ident) => {
      let binding = self.make_local(
        Some(ident),
        pattern.span,
        self.delayed.fresh(),
      )
      {
        node: DVariablePattern(binding),
        ty: binding.ty,
        bindings: [(ident.name, binding)],
        source_span: semantic_span,
      }
    }
    Papp(qualid, arguments) => {
      let typed = arguments.map(argument => self.type_pattern(space, argument))
      self.constructor_pattern(
        space.find_logic(qualid_segments(qualid), Some(qualid_span(qualid))),
        typed,
        pattern.span,
      )
    }
    Prec(fields) => self.record_pattern(space, fields, pattern.span)
    Ptuple(arguments) => {
      let typed = arguments.map(argument => self.type_pattern(space, argument))
      self.constructor_pattern(
        space.find_logic(
          [tuple_constructor_name(arguments.length())],
          semantic_span,
        ),
        typed,
        pattern.span,
      )
    }
    Pas(inner, ident, ghost) => {
      if ghost {
        fail_invalid_input(
          InvalidPattern,
          PureTyping,
          semantic_span,
          "ghost patterns are only allowed in programs",
        )
      }
      let inner = self.type_pattern(space, inner)
      if find_pattern_binding(inner.bindings, ident.name) is Some(_) {
        @logic.fail_type(
          DuplicateBinder,
          Some(source_span(ident.span)),
          "as-pattern repeats a bound variable",
        )
      }
      let binding = self.make_local(Some(ident), ident.span, inner.ty)
      let bindings = inner.bindings.copy()
      bindings.push((ident.name, binding))
      {
        node: DAsPattern(inner, binding),
        ty: inner.ty,
        bindings,
        source_span: semantic_span,
      }
    }
    Por(left, right) => {
      let left = self.type_pattern(space, left)
      let right = self.type_pattern(space, right)
      self.expect_pattern(right, left.ty)
      if left.bindings.length() != right.bindings.length() {
        @logic.fail_type(
          InvalidDeclaration,
          semantic_span,
          "or-pattern branches bind different variables",
        )
      }
      for left_binding in left.bindings {
        guard find_pattern_binding(right.bindings, left_binding.0)
          is Some(right_binding) else {
          @logic.fail_type(
            InvalidDeclaration,
            semantic_span,
            "or-pattern branches bind different variables",
          )
        }
        self.delayed.unify_expected(
          right_binding.ty,
          left_binding.1.ty,
          semantic_span,
        )
      }
      {
        node: DOrPattern(left, right),
        ty: left.ty,
        bindings: left.bindings.copy(),
        source_span: semantic_span,
      }
    }
    Pcast(inner, annotation) => {
      let inner = self.type_pattern(space, inner)
      let expected = self.dty_of_pty(space, annotation)
      self.expect_pattern(inner, expected)
      {
        node: DCastPattern(inner),
        ty: expected,
        bindings: inner.bindings.copy(),
        source_span: semantic_span,
      }
    }
    Pscope(qualid, inner) =>
      self.type_pattern(
        space.open_scope(qualid_segments(qualid), Some(qualid_span(qualid))),
        inner,
      )
    Pparen(inner) => self.type_pattern(space, inner)
    Pghost(_) =>
      fail_invalid_input(
        InvalidPattern,
        PureTyping,
        semantic_span,
        "ghost patterns are only allowed in programs",
      )
  }
}

///|
fn collect_application(
  term : @parser.Term,
  reversed_arguments : Array[(@parser.Term, @parser.Span)],
) -> @parser.Term {
  match term.desc {
    Tapply(function_, argument) => {
      // Why3 retains the location of every left-associated application
      // prefix.  In `f x y`, the direct `f x` node therefore ends before
      // `y`, even when `f` is first resolved as a logic symbol and `y` is
      // subsequently lowered through HighOrd application.
      reversed_arguments.push((argument, term.span))
      collect_application(function_, reversed_arguments)
    }
    _ => term
  }
}

///|
fn qualid_parser_span(qualid : @parser.QualId) -> @parser.Span {
  match qualid {
    Qident(ident) => ident.span
    Qdot(parent, ident) => qualid_parser_span(parent).join(ident.span)
  }
}

///|
fn PureTyping::logic_symbol_closure(
  self : PureTyping,
  space : @theory.Namespace,
  symbol : @logic.LSymbol,
  span : @parser.Span,
) -> DTerm raise {
  let semantic_span = Some(source_span(span))
  let (argument_types, result_type) = self.specialized_symbol_types(
    symbol, semantic_span,
  )
  let binders : Array[DLocal] = []
  let arguments : Array[DTerm] = []
  for argument_type in argument_types {
    let binder = self.make_local(None, span, argument_type)
    binders.push(binder)
    arguments.push(make_dterm(DLocalTerm(binder), Some(argument_type), span))
  }
  let body = make_dterm(
    DGlobalApplication(symbol, arguments),
    result_type,
    span,
  )
  let mut closure_type = match result_type {
    Some(result_type) => result_type
    None => self.boolean_dty(space, semantic_span)
  }
  for binder in binders.rev() {
    closure_type = self.delayed.arrow(binder.ty, closure_type, semantic_span)
  }
  {
    ..make_dterm(
      DQuantifiedTerm(DTlambda, binders, [], body),
      Some(closure_type),
      span,
    ),
    missing_arguments: binders.length(),
  }
}

///|
fn application_allows_local_head(
  qualid : @parser.QualId,
  arguments : ArrayView[@parser.Term],
) -> Bool {
  if arguments.is_empty() {
    return true
  }
  // The parser lowers `record.field` to `field record`, just like an ordinary
  // prefix application. Source order is the remaining distinction: a real
  // function head precedes its first argument, while a dot projection follows
  // its receiver. A same-named local must not capture the latter.
  qualid_span(qualid).view().end_byte <= arguments[0].span.start.byte_offset
}

///|
fn PureTyping::receiver_projection(
  self : PureTyping,
  receiver : DTerm,
  name : Bytes,
  span : @identity.SourceSpan?,
) -> @logic.LSymbol? raise @logic.TypeError {
  guard receiver.result_type is Some(delayed) &&
    self.delayed.head_symbol(delayed) is Some(type_symbol) else {
    return None
  }
  for data_constructor in self.known.find_constructors(type_symbol, span) {
    for projection in data_constructor.view().projections {
      if projection is Some(projection) && projection.view().name == name {
        return Some(projection)
      }
    }
  }
  None
}

///|
fn PureTyping::qualid_application(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  qualid : @parser.QualId,
  arguments : Array[@parser.Term],
  application_spans : ArrayView[@parser.Span],
  allow_local_head : Bool,
) -> DTerm raise {
  guard arguments.length() == application_spans.length() else {
    abort("application argument/span arity mismatch")
  }
  match (qualid, allow_local_head) {
    (Qident(ident), true) =>
      if find_local(locals, ident.name) is Some(binding) {
        let mut result = make_dterm(
          DLocalTerm(binding),
          Some(binding.ty),
          ident.span,
        )
        if binding.reference {
          result = self.global_application(
            space,
            space.find_logic([b"contents"], Some(source_span(ident.span))),
            [result],
            ident.span,
          )
        }
        for index, argument in arguments {
          result = self.function_application(
            space,
            result,
            self.type_term(space, locals, argument),
            application_spans[index],
          )
        }
        return result
      }
    _ => ()
  }
  let semantic_span = Some(qualid_span(qualid))
  let path = qualid_segments(qualid)
  let mut typed_receiver : DTerm? = None
  let symbol = if !allow_local_head &&
    path.length() == 1 &&
    !arguments.is_empty() {
    let ordinary_function : @logic.LSymbol? = try {
      let candidate = space.find_logic(path, semantic_span)
      let candidate_view = candidate.view()
      if candidate_view.role is Projection ||
        candidate_view.origin
        .attributes()
        .any(attribute => attribute == b"is_field_id") {
        None
      } else {
        Some(candidate)
      }
    } catch {
      _ => None
    }
    match ordinary_function {
      Some(function_) => function_
      None => {
        let receiver = self.type_term(space, locals, arguments[0])
        typed_receiver = Some(receiver)
        match self.receiver_projection(receiver, path[0], semantic_span) {
          Some(projection) => projection
          None => space.find_logic(path, semantic_span)
        }
      }
    }
  } else {
    space.find_logic(path, semantic_span)
  }
  let direct_arity = symbol.view().argument_types.length()
  if arguments.length() < direct_arity {
    let mut result = self.logic_symbol_closure(
      space,
      symbol,
      qualid_parser_span(qualid),
    )
    for index, argument in arguments {
      let argument = match (index, typed_receiver) {
        (0, Some(receiver)) => receiver
        _ => self.type_term(space, locals, argument)
      }
      result = self.function_application(
        space,
        result,
        argument,
        application_spans[index],
      )
    }
    return result
  }
  let direct_arguments : Array[DTerm] = []
  for index = 0; index < direct_arity; index = index + 1 {
    direct_arguments.push(
      match (index, typed_receiver) {
        (0, Some(receiver)) => receiver
        _ => self.type_term(space, locals, arguments[index])
      },
    )
  }
  let direct_span = if direct_arity == 0 {
    qualid_parser_span(qualid)
  } else {
    application_spans[direct_arity - 1]
  }
  let mut result = self.global_application(
    space,
    symbol,
    direct_arguments,
    direct_span,
  )
  for index = direct_arity; index < arguments.length(); index = index + 1 {
    let argument = match (index, typed_receiver) {
      (0, Some(receiver)) => receiver
      _ => self.type_term(space, locals, arguments[index])
    }
    result = self.function_application(
      space,
      result,
      argument,
      application_spans[index],
    )
  }
  result
}

///|
fn PureTyping::typed_relation_application(
  self : PureTyping,
  space : @theory.Namespace,
  left : DTerm,
  operator : @parser.Ident,
  right : DTerm,
  span : @parser.Span,
) -> DTerm raise {
  let name = if operator.name == b"infix <>" {
    b"infix ="
  } else {
    operator.name
  }
  let symbol = space.find_logic([name], Some(source_span(operator.span)))
  let application = self.global_application(space, symbol, [left, right], span)
  if operator.name == b"infix <>" {
    make_dterm(DNotTerm(application), None, span)
  } else {
    application
  }
}

///|
fn PureTyping::relation_chain(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  left : DTerm,
  operator : @parser.Ident,
  tail : @parser.Term,
  span : @parser.Span,
) -> DTerm raise {
  match tail.desc {
    Tinfix(middle, next_operator, rest) => {
      let typed_middle = self.type_term(space, locals, middle)
      let first_span = @parser.Span::{ start: span.start, end: middle.span.end }
      let first = self.typed_relation_application(
        space, left, operator, typed_middle, first_span,
      )
      let rest = self.relation_chain(
        space,
        locals,
        typed_middle,
        next_operator,
        rest,
        tail.span,
      )
      self.expect_formula(space, first)
      self.expect_formula(space, rest)
      make_dterm(DBinaryTerm(DTand, first, rest), None, span)
    }
    _ =>
      self.typed_relation_application(
        space,
        left,
        operator,
        self.type_term(space, locals, tail),
        span,
      )
  }
}

///|
fn PureTyping::type_binders(
  self : PureTyping,
  space : @theory.Namespace,
  outer : ArrayView[(Bytes, DLocal)],
  binders : ArrayView[@parser.Binder],
) -> (Array[DLocal], Array[(Bytes, DLocal)]) raise {
  let typed : Array[DLocal] = []
  let local_bindings = outer.to_owned()
  let names : Array[Bytes] = []
  for binder in binders {
    if binder.ghost {
      fail_invalid_input(
        InvalidBinder,
        PureTyping,
        Some(source_span(binder.span)),
        "ghost binders are outside pure logic",
      )
    }
    let delayed = match binder.binder_type {
      Some(pty) => self.dty_of_pty(space, pty)
      None => self.delayed.fresh()
    }
    let binding = self.make_local(binder.ident, binder.span, delayed)
    if binder.ident is Some(ident) {
      if names.any(name => name[:] == ident.name[:]) {
        @logic.fail_type(
          DuplicateBinder,
          Some(source_span(ident.span)),
          "quantifier repeats a binder name",
        )
      }
      names.push(ident.name)
      local_bindings.push((ident.name, binding))
    }
    typed.push(binding)
  }
  (typed, local_bindings)
}

///|
fn PureTyping::branch_head_symbol(
  self : PureTyping,
  space : @theory.Namespace,
  result_type : Dty?,
  span : @identity.SourceSpan?,
) -> @logic.TypeSymbol? raise {
  match result_type {
    Some(delayed) => self.delayed.head_symbol(delayed)
    None => Some(space.find_type([b"bool"], span))
  }
}

///|
fn PureTyping::max_branch_type(
  self : PureTyping,
  space : @theory.Namespace,
  branches : ArrayView[DTerm],
  span : @identity.SourceSpan?,
) -> Dty? raise {
  if branches.is_empty() {
    abort("branch type selection requires at least one branch")
  }
  let mut selected_index = -1
  for index = branches.length() - 1; index >= 0; index = index - 1 {
    match self.branch_head_symbol(space, branches[index].result_type, span) {
      None => ()
      Some(source) => {
        let mut coerces_to_earlier = false
        for earlier_index in 0..<index {
          match
            self.branch_head_symbol(
              space,
              branches[earlier_index].result_type,
              span,
            ) {
            Some(target) =>
              if source == target ||
                self.coercions.find_by_symbols(source, target) is Some(_) {
                coerces_to_earlier = true
                break
              }
            None => ()
          }
        }
        if !coerces_to_earlier {
          selected_index = index
          break
        }
      }
    }
  }
  if selected_index < 0 {
    return branches[0].result_type
  }
  let selected = branches[selected_index].result_type
  // `prop` and `bool` share a coercion head; Why3 favors `prop` whenever
  // both forms occur in the same branch family.
  if branches.any(branch => branch.result_type is None) &&
    selected is Some(delayed) &&
    self.delayed.head_symbol(delayed) is Some(selected_symbol) &&
    selected_symbol == space.find_type([b"bool"], span) {
    None
  } else {
    selected
  }
}

///|
fn PureTyping::expect_branch_type(
  self : PureTyping,
  space : @theory.Namespace,
  branch : DTerm,
  expected : Dty?,
) -> DTerm raise {
  match expected {
    Some(expected) => self.expect_value(space, branch, expected)
    None => {
      self.expect_formula(space, branch)
      branch
    }
  }
}

///|
fn is_reusable_dterm(term : DTerm) -> Bool {
  match term.node {
    DLocalTerm(_) | DConstantTerm(_) | DTrueTerm | DFalseTerm => true
    DGlobalApplication(_, arguments) => arguments.is_empty()
    DFunctionApplication(_, _)
    | DIfTerm(_, _, _)
    | DLetTerm(_, _, _)
    | DCaseTerm(_, _)
    | DEpsilonTerm(_, _)
    | DQuantifiedTerm(_, _, _, _)
    | DBinaryTerm(_, _, _)
    | DNotTerm(_)
    | DAtTerm(_, _)
    | DCastTerm(_) => false
  }
}

///|
fn PureTyping::record_term_in_scope(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  fields : ArrayView[(@parser.QualId, @parser.Term)],
  span : @parser.Span,
) -> DTerm raise {
  let semantic_span = Some(source_span(span))
  let resolved : Array[(@logic.LSymbol, @parser.Term)] = []
  for field in fields {
    resolved.push(
      (
        space.find_logic(qualid_segments(field.0), Some(qualid_span(field.0))),
        field.1,
      ),
    )
  }
  let symbols = resolved.map(entry => entry.0)
  let (data_constructor, projections) = self.known.record_layout(
    symbols, semantic_span,
  )
  let values : Map[@logic.LSymbol, @parser.Term] = Map([])
  for entry in resolved {
    values[entry.0] = entry.1
  }
  let arguments : Array[DTerm] = []
  for projection in projections {
    guard values.get(projection) is Some(value) else {
      @logic.fail_type(
        RecordFieldMissing,
        semantic_span,
        "record construction omits a field",
      )
    }
    arguments.push(self.type_term(space, locals, value))
  }
  self.global_application(
    space,
    data_constructor.view().symbol,
    arguments,
    span,
  )
}

///|
fn PureTyping::record_update(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  source : @parser.Term,
  fields : ArrayView[(@parser.QualId, @parser.Term)],
  span : @parser.Span,
) -> DTerm raise {
  let semantic_span = Some(source_span(span))
  let source_term = self.type_term(space, locals, source)
  let resolved : Array[(@logic.LSymbol, @parser.Term)] = []
  for field in fields {
    resolved.push(
      (
        space.find_logic(qualid_segments(field.0), Some(qualid_span(field.0))),
        field.1,
      ),
    )
  }
  let symbols = resolved.map(entry => entry.0)
  let (data_constructor, projections) = self.known.record_layout(
    symbols, semantic_span,
  )
  let values : Map[@logic.LSymbol, @parser.Term] = Map([])
  for entry in resolved {
    values[entry.0] = entry.1
  }
  let reusable = is_reusable_dterm(source_term)
  let source_type = match source_term.result_type {
    Some(ty) => ty
    None => self.boolean_dty(space, source_term.source_span)
  }
  let proxy = self.make_local(None, source.span, source_type)
  let source_reference = if reusable {
    source_term
  } else {
    make_dterm(DLocalTerm(proxy), Some(proxy.ty), source.span)
  }
  let mut used_source = false
  let arguments : Array[DTerm] = []
  for projection in projections {
    match values.get(projection) {
      Some(value) => arguments.push(self.type_term(space, locals, value))
      None => {
        used_source = true
        arguments.push(
          self.global_application(space, projection, [source_reference], span),
        )
      }
    }
  }
  let rebuilt = self.global_application(
    space,
    data_constructor.view().symbol,
    arguments,
    span,
  )
  if used_source && !reusable {
    make_dterm(DLetTerm(proxy, source_term, rebuilt), rebuilt.result_type, span)
  } else {
    rebuilt
  }
}

///|
fn PureTyping::type_term(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  term : @parser.Term,
) -> DTerm raise {
  match term.desc {
    Ttrue =>
      make_dterm(
        DTrueTerm,
        Some(self.boolean_dty(space, Some(source_span(term.span)))),
        term.span,
      )
    Tfalse =>
      make_dterm(
        DFalseTerm,
        Some(self.boolean_dty(space, Some(source_span(term.span)))),
        term.span,
      )
    Tconst(constant) => {
      let type_name = match constant {
        ConstInt(_) => b"int"
        ConstReal(_) => b"real"
        ConstStr(_) => b"string"
      }
      let (delayed, _) = self.named_type(
        space,
        type_name,
        Some(source_span(term.span)),
      )
      make_dterm(DConstantTerm(constant), Some(delayed), term.span)
    }
    Tident(qualid) =>
      self.qualid_application(space, locals, qualid, [], [], true)
    Tidapp(qualid, arguments) => {
      let application_spans = [for _ in arguments => term.span]
      self.qualid_application(
        space,
        locals,
        qualid,
        arguments,
        application_spans,
        application_allows_local_head(qualid, arguments),
      )
    }
    Tapply(_, _) => {
      let reversed : Array[(@parser.Term, @parser.Span)] = []
      let head = collect_application(term, reversed)
      let applications = reversed.rev()
      let arguments : Array[@parser.Term] = []
      let application_spans : Array[@parser.Span] = []
      for application in applications {
        arguments.push(application.0)
        application_spans.push(application.1)
      }
      match head.desc {
        Tident(qualid) =>
          self.qualid_application(
            space,
            locals,
            qualid,
            arguments,
            application_spans,
            application_allows_local_head(qualid, arguments),
          )
        _ => {
          let mut result = self.type_term(space, locals, head)
          for index, argument in arguments {
            result = self.function_application(
              space,
              result,
              self.type_term(space, locals, argument),
              application_spans[index],
            )
          }
          result
        }
      }
    }
    Tinfix(left, operator, right) | Tinnfix(left, operator, right) =>
      self.relation_chain(
        space,
        locals,
        self.type_term(space, locals, left),
        operator,
        right,
        term.span,
      )
    Tbinop(left, operator, right) | Tbinnop(left, operator, right) => {
      let left = self.type_term(space, locals, left)
      let right = self.type_term(space, locals, right)
      self.expect_formula(space, left)
      self.expect_formula(space, right)
      make_dterm(DBinaryTerm(operator, left, right), None, term.span)
    }
    Tnot(inner) => {
      let inner = self.type_term(space, locals, inner)
      self.expect_formula(space, inner)
      make_dterm(DNotTerm(inner), None, term.span)
    }
    Tif(condition, then_branch, else_branch) => {
      let condition = self.type_term(space, locals, condition)
      self.expect_formula(space, condition)
      let branches = [
        self.type_term(space, locals, then_branch),
        self.type_term(space, locals, else_branch),
      ]
      let result_type = self.max_branch_type(
        space,
        branches,
        Some(source_span(term.span)),
      )
      branches[0] = self.expect_branch_type(space, branches[0], result_type)
      branches[1] = self.expect_branch_type(space, branches[1], result_type)
      make_dterm(
        DIfTerm(condition, branches[0], branches[1]),
        result_type,
        term.span,
      )
    }
    Tlet(ident, value, body) => {
      let value = self.type_term(space, locals, value)
      let local_type = match value.result_type {
        Some(delayed) => delayed
        None => self.boolean_dty(space, value.source_span)
      }
      let binding = self.make_local(Some(ident), ident.span, local_type)
      let nested = locals.to_owned()
      nested.push((ident.name, binding))
      let body = self.type_term(space, nested, body)
      make_dterm(DLetTerm(binding, value, body), body.result_type, term.span)
    }
    Tquant(quantifier, binders, triggers, body) => {
      let (binders, nested) = self.type_binders(space, locals, binders)
      let typed_triggers = [
        for group in triggers => {
          [
            for trigger in group => self.type_term(space, nested, trigger)
          ]
        }
      ]
      let body = self.type_term(space, nested, body)
      match quantifier {
        DTforall | DTexists => {
          self.expect_formula(space, body)
          make_dterm(
            DQuantifiedTerm(quantifier, binders, typed_triggers, body),
            None,
            term.span,
          )
        }
        DTlambda => {
          let mut result = match body.result_type {
            Some(result) => result
            None => self.boolean_dty(space, body.source_span)
          }
          for binder in binders.rev() {
            result = self.delayed.arrow(binder.ty, result, body.source_span)
          }
          make_dterm(
            DQuantifiedTerm(quantifier, binders, typed_triggers, body),
            Some(result),
            term.span,
          )
        }
      }
    }
    Tcast(inner, pty) => {
      let expected = self.dty_of_pty(space, pty)
      if inner.desc is Tconst(constant) {
        return make_dterm(
          DCastTerm(
            make_dterm(DConstantTerm(constant), Some(expected), inner.span),
          ),
          Some(expected),
          term.span,
        )
      }
      let inner = self.type_term(space, locals, inner)
      let inner = self.expect_value(space, inner, expected)
      make_dterm(DCastTerm(inner), Some(expected), term.span)
    }
    Tattr(attribute, inner) => {
      let inner = self.type_term(space, locals, inner)
      match attribute {
        Text(text) => {
          let attributes = inner.attributes.copy()
          attributes.push(
            checked_text_attribute(text, Some(source_span(term.span))),
          )
          { ..inner, attributes, }
        }
        Position(position) =>
          { ..inner, source_span: Some(source_span(position)) }
      }
    }
    Tscope(qualid, inner) => {
      let span = qualid_span(qualid)
      let imported = space.open_scope(qualid_segments(qualid), Some(span))
      self.type_term(imported, locals, inner)
    }
    Ttuple(arguments) => {
      let symbol = space.find_logic(
        [tuple_constructor_name(arguments.length())],
        Some(source_span(term.span)),
      )
      self.global_application(
        space,
        symbol,
        arguments.map(argument => self.type_term(space, locals, argument)),
        term.span,
      )
    }
    Teps(ident, annotation, body) => {
      let delayed = self.dty_of_pty(space, annotation)
      let binding = self.make_local(Some(ident), ident.span, delayed)
      let nested = locals.to_owned()
      nested.push((ident.name, binding))
      let body = self.type_term(space, nested, body)
      self.expect_formula(space, body)
      make_dterm(DEpsilonTerm(binding, body), Some(delayed), term.span)
    }
    Tcase(scrutinee, branches) => {
      if branches.is_empty() {
        @logic.fail_type(
          EmptyDeclaration,
          Some(source_span(term.span)),
          "case expression has no branches",
        )
      }
      let scrutinee = self.type_term(space, locals, scrutinee)
      let scrutinee_type = match scrutinee.result_type {
        Some(ty) => ty
        None => self.boolean_dty(space, scrutinee.source_span)
      }
      let typed_branches : Array[(DPattern, DTerm)] = []
      for branch in branches {
        let pattern = self.type_pattern(space, branch.0)
        self.expect_pattern(pattern, scrutinee_type)
        let nested = locals.to_owned()
        for binding in pattern.bindings {
          nested.push(binding)
        }
        let body = self.type_term(space, nested, branch.1)
        typed_branches.push((pattern, body))
      }
      let branch_bodies = [ for branch in typed_branches => branch.1 ]
      let result_type = self.max_branch_type(
        space,
        branch_bodies,
        Some(source_span(term.span)),
      )
      for index, branch in typed_branches {
        typed_branches[index] = (
          branch.0,
          self.expect_branch_type(space, branch.1, result_type),
        )
      }
      make_dterm(DCaseTerm(scrutinee, typed_branches), result_type, term.span)
    }
    Trecord(fields) =>
      self.record_term_in_scope(space, locals, fields, term.span)
    Tupdate(source, fields) =>
      self.record_update(space, locals, source, fields, term.span)
    Tasref(Qident(ident)) =>
      match find_local(locals, ident.name) {
        Some(binding) if binding.reference =>
          make_dterm(DLocalTerm(binding), Some(binding.ty), term.span)
        _ =>
          @logic.fail_type(
            TypeMismatch,
            Some(source_span(term.span)),
            "reference escape expects a reference-marked local variable",
          )
      }
    Tasref(_) =>
      @logic.fail_type(
        TypeMismatch,
        Some(source_span(term.span)),
        "reference escape expects an unqualified local variable",
      )
    Tat(inner, label) => {
      let inner = self.type_term(space, locals, inner)
      make_dterm(DAtTerm(inner, label.name), inner.result_type, term.span)
    }
  }
}

///|
fn find_semantic_local(
  values : ArrayView[(Int, @logic.VSymbol)],
  id : Int,
  at_values : ArrayView[DAtValue],
  active_label : Bytes?,
  at_resolver : (DAtValue) -> @logic.VSymbol raise,
) -> @logic.VSymbol raise {
  if active_label is Some(label) {
    for index = at_values.length() - 1; index >= 0; index = index - 1 {
      if at_values[index].local_id == id && at_values[index].label == label {
        return at_resolver(at_values[index])
      }
    }
  }
  for index = values.length() - 1; index >= 0; index = index - 1 {
    if values[index].0 == id {
      return values[index].1
    }
  }
  @logic.fail_type(UnboundVariable, None, "delayed binding was not finalized")
}

///|
fn PureTyping::semantic_local(
  self : PureTyping,
  space : @theory.Namespace,
  binding : DLocal,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  @logic.VSymbol::new(
    self.semantic_context,
    binding.name,
    binding.origin,
    self.finalize_dty(space, binding.ty, span),
    span,
  )
}

///|
fn PureTyping::finalize_dty(
  self : PureTyping,
  space : @theory.Namespace,
  delayed : Dty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  if self.delayed.contains_arrow(delayed) {
    self.delayed.finalize_higher_order(
      delayed,
      space.find_type([b"infix ->"], span),
      span,
    )
  } else {
    self.delayed.finalize_pure(delayed, span)
  }
}

///|
fn boolean_value(
  space : @theory.Namespace,
  value : Bool,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let name = if value { b"True" } else { b"False" }
  let symbol = space.find_logic([name], span)
  let bool_symbol = space.find_type([b"bool"], span)
  let bool_type = @logic.Ty::app(bool_symbol, [], span)
  @logic.Term::elaborated_apply(symbol, [], Some(bool_type), span)
}

///|
fn decorate_finalized(term : DTerm, semantic : @logic.Term) -> @logic.Term {
  let attributes = semantic.attributes().to_owned()
  for attribute in term.attributes {
    attributes.push(attribute)
  }
  semantic.source_decorate(term.source_span, attributes)
}

///|
fn find_named_pattern_variable(
  values : ArrayView[(Bytes, @logic.VSymbol)],
  name : BytesView,
) -> @logic.VSymbol raise @logic.TypeError {
  for entry in values {
    if entry.0[:] == name {
      return entry.1
    }
  }
  @logic.fail_type(
    UnboundVariable,
    None,
    "delayed pattern binding was not finalized",
  )
}

///|
fn PureTyping::finalize_pattern_node(
  self : PureTyping,
  space : @theory.Namespace,
  pattern : DPattern,
  values : ArrayView[(Bytes, @logic.VSymbol)],
) -> @logic.Pattern raise {
  let result_type = self.finalize_dty(space, pattern.ty, pattern.source_span)
  match pattern.node {
    DWildPattern => @logic.Pattern::wild(result_type)
    DVariablePattern(binding) =>
      @logic.Pattern::variable(
        find_named_pattern_variable(values, binding.name),
      )
    DApplicationPattern(symbol, arguments) =>
      @logic.Pattern::app(
        symbol,
        arguments.map(argument => {
          self.finalize_pattern_node(space, argument, values)
        }),
        result_type,
        pattern.source_span,
      )
    DOrPattern(left, right) =>
      @logic.Pattern::or(
        self.finalize_pattern_node(space, left, values),
        self.finalize_pattern_node(space, right, values),
        pattern.source_span,
      )
    DAsPattern(inner, binding) =>
      @logic.Pattern::as_pattern(
        self.finalize_pattern_node(space, inner, values),
        find_named_pattern_variable(values, binding.name),
        pattern.source_span,
      )
    DCastPattern(inner) => self.finalize_pattern_node(space, inner, values)
  }
}

///|
fn PureTyping::finalize_pattern(
  self : PureTyping,
  space : @theory.Namespace,
  pattern : DPattern,
) -> (@logic.Pattern, Array[(Int, @logic.VSymbol)]) raise {
  let named : Array[(Bytes, @logic.VSymbol)] = []
  let semantic_values : Array[(Int, @logic.VSymbol)] = []
  for binding in pattern.bindings {
    let variable = self.semantic_local(space, binding.1, pattern.source_span)
    named.push((binding.0, variable))
    semantic_values.push((binding.1.id, variable))
  }
  (self.finalize_pattern_node(space, pattern, named), semantic_values)
}

///|
fn semantic_function_result(
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  match ty.view() {
    TyApp(symbol, arguments) if symbol.view().name == b"infix ->" &&
      arguments.length() == 2 => arguments[1]
    _ =>
      @logic.fail_type(
        FunctionExpected,
        span,
        "lambda application expected the builtin function type",
      )
  }
}

///|
fn PureTyping::finalize_term(
  self : PureTyping,
  space : @theory.Namespace,
  values : ArrayView[(Int, @logic.VSymbol)],
  term : DTerm,
  formula_expected : Bool,
  at_values : ArrayView[DAtValue],
  at_labels : ArrayView[Bytes],
  active_label : Bytes?,
  at_resolver : (DAtValue) -> @logic.VSymbol raise,
) -> @logic.Term raise {
  let recurse = fn(
    nested_values : ArrayView[(Int, @logic.VSymbol)],
    nested_term : DTerm,
    nested_formula : Bool,
  ) -> @logic.Term raise {
    self.finalize_term(
      space, nested_values, nested_term, nested_formula, at_values, at_labels, active_label,
      at_resolver,
    )
  }
  let node = match term.node {
    DLocalTerm(binding) => {
      let selected = find_semantic_local(
        values,
        binding.id,
        at_values,
        active_label,
        at_resolver,
      )
      let variable = @logic.Term::variable(selected)
      match active_label {
        Some(label) => {
          let current = find_semantic_local(
            values,
            binding.id,
            at_values,
            None,
            at_resolver,
          )
          if selected == current {
            variable
          } else {
            variable.add_attributes([b"at:" + label])
          }
        }
        None => variable
      }
    }
    DConstantTerm(constant) => {
      guard term.result_type is Some(delayed) else {
        abort("constant delayed type is missing")
      }
      @logic.Term::constant(
        constant,
        self.finalize_dty(space, delayed, term.source_span),
        term.source_span,
      )
    }
    DGlobalApplication(symbol, arguments) => {
      let view = symbol.view()
      if arguments.is_empty() && view.name == b"True" && formula_expected {
        @logic.Term::true_formula()
      } else if arguments.is_empty() &&
        view.name == b"False" &&
        formula_expected {
        @logic.Term::false_formula()
      } else if view.name == b"infix =" &&
        arguments.length() == 2 &&
        (arguments[0].result_type is None || arguments[1].result_type is None) {
        @logic.Term::binary(
          Iff,
          recurse(values, arguments[0], true),
          recurse(values, arguments[1], true),
          term.source_span,
        )
      } else {
        let finalized_arguments = [
          for argument in arguments => recurse(values, argument, false)
        ]
        let result = match term.result_type {
          None => None
          Some(delayed) =>
            Some(self.finalize_dty(space, delayed, term.source_span))
        }
        @logic.Term::elaborated_apply(
          symbol,
          finalized_arguments,
          result,
          term.source_span,
        )
      }
    }
    DFunctionApplication(function_, argument) => {
      let result = match term.result_type {
        None => None
        Some(delayed) =>
          Some(self.finalize_dty(space, delayed, term.source_span))
      }
      @logic.Term::elaborated_apply(
        space.find_logic([b"infix @"], term.source_span),
        [recurse(values, function_, false), recurse(values, argument, false)],
        result,
        term.source_span,
      )
    }
    DIfTerm(condition, then_branch, else_branch) => {
      let branch_formula = formula_expected || term.result_type is None
      @logic.Term::if_then_else(
        recurse(values, condition, true),
        recurse(values, then_branch, branch_formula),
        recurse(values, else_branch, branch_formula),
        term.source_span,
      )
    }
    DCaseTerm(scrutinee, branches) => {
      let branch_formula = formula_expected || term.result_type is None
      let finalized : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let (pattern, bound) = self.finalize_pattern(space, branch.0)
        let nested = values.to_owned()
        for entry in bound {
          nested.push(entry)
        }
        finalized.push((pattern, recurse(nested, branch.1, branch_formula)))
      }
      @logic.Term::case(
        recurse(values, scrutinee, false),
        finalized,
        term.source_span,
      )
    }
    DEpsilonTerm(binding, body) => {
      let variable = self.semantic_local(space, binding, term.source_span)
      let nested = values.to_owned()
      nested.push((binding.id, variable))
      @logic.Term::epsilon(
        variable,
        recurse(nested, body, true),
        term.source_span,
      )
    }
    DLetTerm(binding, value, body) => {
      let variable = self.semantic_local(space, binding, term.source_span)
      let nested = values.to_owned()
      nested.push((binding.id, variable))
      @logic.Term::let_in(
        variable,
        recurse(values, value, false),
        recurse(nested, body, formula_expected || term.result_type is None),
        term.source_span,
      )
    }
    DQuantifiedTerm(DTlambda, binders, triggers, body) => {
      guard term.result_type is Some(delayed_result) else {
        abort("lambda delayed result type is missing")
      }
      let function_type = self.finalize_dty(
        space,
        delayed_result,
        term.source_span,
      )
      let nested = values.to_owned()
      let semantic_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let variable = self.semantic_local(space, binder, term.source_span)
        nested.push((binder.id, variable))
        semantic_binders.push(variable)
      }
      let semantic_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              recurse(nested, trigger, trigger.result_type is None)
            }
          ]
        }
      ]
      let semantic_body = recurse(nested, body, body.result_type is None)
      let closure = @logic.VSymbol::new(
        self.semantic_context,
        b"fc",
        @identity.Origin::user(b"fc", None, []),
        function_type,
        None,
      )
      let application = space.find_logic([b"infix @"], term.source_span)
      let mut head = @logic.Term::variable(closure)
      let mut head_type = function_type
      let body_span = semantic_body.source_span()
      for binder in semantic_binders {
        let result_type = semantic_function_result(head_type, term.source_span)
        let argument = @logic.Term::variable(binder).source_decorate(
          binder.view().origin.identifier_source_span(),
          [],
        )
        head = @logic.Term::elaborated_apply(
          application,
          [head, argument],
          Some(result_type),
          None,
        ).source_decorate(body_span, [])
        head_type = result_type
      }
      let defining_formula = match semantic_body.ty() {
        Some(_) =>
          @logic.Term::elaborated_apply(
            space.find_logic([b"infix ="], term.source_span),
            [head, semantic_body],
            None,
            None,
          ).source_decorate(body_span, [])
        None => {
          let head_is_true = @logic.Term::elaborated_apply(
            space.find_logic([b"infix ="], term.source_span),
            [head, boolean_value(space, true, term.source_span)],
            None,
            None,
          ).source_decorate(body_span, [])
          @logic.Term::binary(Iff, head_is_true, semantic_body, None).source_decorate(
            body_span,
            [],
          )
        }
      }
      @logic.Term::epsilon(
        closure,
        @logic.Term::quantify(
          ForallQuantifier,
          semantic_binders,
          semantic_triggers,
          defining_formula,
          None,
        ).source_decorate(body_span, []),
        term.source_span,
      )
    }
    DQuantifiedTerm(quantifier, binders, triggers, body) => {
      let nested = values.to_owned()
      let semantic_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let variable = self.semantic_local(space, binder, term.source_span)
        nested.push((binder.id, variable))
        semantic_binders.push(variable)
      }
      let semantic_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              recurse(nested, trigger, trigger.result_type is None)
            }
          ]
        }
      ]
      @logic.Term::quantify(
        match quantifier {
          DTforall => ForallQuantifier
          DTexists => ExistsQuantifier
          DTlambda => abort("lambda handled above")
        },
        semantic_binders,
        semantic_triggers,
        recurse(nested, body, true),
        term.source_span,
      )
    }
    DBinaryTerm(operator, left, right) => {
      let left = recurse(values, left, true)
      let right = recurse(values, right, true)
      if operator is DTby || operator is DTso {
        let truth = @logic.Term::true_formula().source_decorate(
          right.source_span(),
          [],
        )
        let guarded = @logic.Term::binary(
          Or,
          right.add_attributes([b"asym_split"]),
          truth,
          right.source_span(),
        ).source_decorate(right.source_span(), [])
        @logic.Term::binary(
          if operator is DTby {
            Implies
          } else {
            And
          },
          if operator is DTby {
            guarded
          } else {
            left
          },
          if operator is DTby {
            left
          } else {
            guarded
          },
          term.source_span,
        )
      } else {
        let left = if operator is DTandAsym || operator is DTorAsym {
          left.add_attributes([b"asym_split"])
        } else {
          left
        }
        @logic.Term::binary(
          match operator {
            DTand | DTandAsym => And
            DTor | DTorAsym => Or
            DTimplies => Implies
            DTiff => Iff
            DTby | DTso => abort("proof-control connective handled above")
          },
          left,
          right,
          term.source_span,
        )
      }
    }
    DNotTerm(inner) =>
      @logic.Term::not(recurse(values, inner, true), term.source_span)
    DAtTerm(inner, label) => {
      if !at_labels.any(known => known == label) {
        let known_labels = at_labels.map(known => known.to_string()).join(", ")
        @logic.fail_type(
          UnboundVariable,
          term.source_span,
          "unknown program-state label \{label}; known labels: \{known_labels}",
        )
      }
      return self.finalize_term(
        space,
        values,
        inner,
        formula_expected,
        at_values,
        at_labels,
        Some(label),
        at_resolver,
      )
    }
    DTrueTerm =>
      if formula_expected {
        @logic.Term::true_formula()
      } else {
        boolean_value(space, true, term.source_span)
      }
    DFalseTerm =>
      if formula_expected {
        @logic.Term::false_formula()
      } else {
        boolean_value(space, false, term.source_span)
      }
    // A type ascription is erased before Why3 selects the semantic term
    // location (`Dterm.strip`).  Keep the inner term's source decoration
    // instead of widening it to the whole `(term : type)` syntax.
    DCastTerm(inner) => return recurse(values, inner, formula_expected)
  }
  let node = decorate_finalized(term, node)
  match (node.ty(), formula_expected) {
    (Some(_), true) => {
      let promoted = @logic.Term::elaborated_apply(
        space.find_logic([b"infix ="], term.source_span),
        [node, boolean_value(space, true, term.source_span)],
        None,
        term.source_span,
      )
      decorate_finalized(term, promoted)
    }
    (None, false) => {
      let lowered = @logic.Term::if_then_else(
        node,
        boolean_value(space, true, term.source_span),
        boolean_value(space, false, term.source_span),
        term.source_span,
      )
      decorate_finalized(term, lowered)
    }
    _ => node
  }
}

///|
fn PureTyping::formula(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  values : ArrayView[(Int, @logic.VSymbol)],
  term : @parser.Term,
  at_values? : ArrayView[DAtValue] = [],
  at_labels? : ArrayView[Bytes] = [],
  at_resolver? : (DAtValue) -> @logic.VSymbol raise = fn(entry) { entry.value },
) -> @logic.Term raise {
  let delayed = self.type_term(space, locals, term)
  self.expect_formula(space, delayed)
  self.finalize_term(
    space,
    values,
    delayed,
    true,
    at_values,
    at_labels,
    None,
    at_resolver,
  )
}

///|
/// Finalizes a source term in the same value-or-formula mode selected by
/// Why3's delayed term typer. Formulae become boolean-valued program terms;
/// value terms retain their inferred semantic type.
fn PureTyping::program_term(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  values : ArrayView[(Int, @logic.VSymbol)],
  term : @parser.Term,
  at_values? : ArrayView[DAtValue] = [],
  at_labels? : ArrayView[Bytes] = [],
  at_resolver? : (DAtValue) -> @logic.VSymbol raise = fn(entry) { entry.value },
) -> (@logic.Term, @logic.Ty) raise {
  let delayed = self.type_term(space, locals, term)
  match delayed.result_type {
    Some(result) => {
      let ty = self.finalize_dty(space, result, delayed.source_span)
      (
        self.finalize_term(
          space,
          values,
          delayed,
          false,
          at_values,
          at_labels,
          None,
          at_resolver,
        ),
        ty,
      )
    }
    None => {
      let (_, boolean) = self.named_type(space, b"bool", delayed.source_span)
      (
        self.finalize_term(
          space,
          values,
          delayed,
          true,
          at_values,
          at_labels,
          None,
          at_resolver,
        ),
        boolean,
      )
    }
  }
}

///|
fn PureTyping::value(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  values : ArrayView[(Int, @logic.VSymbol)],
  term : @parser.Term,
  expected : Dty,
  at_values? : ArrayView[DAtValue] = [],
  at_labels? : ArrayView[Bytes] = [],
  at_resolver? : (DAtValue) -> @logic.VSymbol raise = fn(entry) { entry.value },
) -> @logic.Term raise {
  let delayed = self.expect_value(
    space,
    self.type_term(space, locals, term),
    expected,
  )
  self.finalize_term(
    space,
    values,
    delayed,
    false,
    at_values,
    at_labels,
    None,
    at_resolver,
  )
}

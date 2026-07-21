// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv enum DTermNode {
  DLocalTerm(DLocal)
  DConstantTerm(@logic.Constant)
  DGlobalApplication(@logic.LSymbol, Array[DTerm])
  DFunctionApplication
  DIfTerm(DTerm, DTerm, DTerm)
  DLetTerm(DLocal, DTerm, DTerm)
  DQuantifiedTerm(@parser.Quantifier, Array[DLocal], Array[Array[DTerm]], DTerm)
  DBinaryTerm(@parser.BinaryLogicOp, DTerm, DTerm)
  DNotTerm(DTerm)
  DTrueTerm
  DFalseTerm
  DCastTerm(DTerm)
}

///|
priv struct DTerm {
  node : DTermNode
  result_type : Dty?
  source_span : @identity.SourceSpan?
  attributes : Array[Bytes]
}

///|
fn make_dterm(
  node : DTermNode,
  result_type : Dty?,
  span : @parser.Span,
) -> DTerm {
  { node, result_type, source_span: Some(source_span(span)), attributes: [] }
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
) -> Unit raise {
  match term.result_type {
    Some(actual) =>
      self.delayed.unify_expected(actual, expected, term.source_span)
    None => {
      let boolean = self.boolean_dty(space, term.source_span)
      self.delayed.unify_expected(boolean, expected, term.source_span)
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
  // Why3's equality constructor first selects a maximal operand type, then
  // checks arguments from left to right. With no coercion between two
  // supported ground types, the right operand is selected; this preserves
  // both the reported actual/expected types and the failing left span.
  if view.name == b"infix =" &&
    arguments.length() == 2 &&
    arguments[1].result_type is Some(preferred) {
    self.delayed.unify_expected(
      preferred,
      formal_arguments[0],
      arguments[1].source_span,
    )
  }
  for index, argument in arguments {
    self.expect_value(space, argument, formal_arguments[index])
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
  let arrow = self.delayed.arrow(parameter, result, Some(source_span(span)))
  self.delayed.unify_expected(function_type, arrow, function_.source_span)
  self.expect_value(space, argument, parameter)
  make_dterm(DFunctionApplication, Some(result), span)
}

///|
fn collect_application(
  term : @parser.Term,
  reversed_arguments : Array[@parser.Term],
) -> @parser.Term {
  match term.desc {
    Tapply(function_, argument) => {
      reversed_arguments.push(argument)
      collect_application(function_, reversed_arguments)
    }
    _ => term
  }
}

///|
fn PureTyping::qualid_application(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  qualid : @parser.QualId,
  arguments : Array[@parser.Term],
  span : @parser.Span,
) -> DTerm raise {
  match qualid {
    Qident(ident) =>
      if find_local(locals, ident.name) is Some(binding) {
        let mut result = make_dterm(
          DLocalTerm(binding),
          Some(binding.ty),
          ident.span,
        )
        for argument in arguments {
          result = self.function_application(
            space,
            result,
            self.type_term(space, locals, argument),
            span,
          )
        }
        return result
      }
    Qdot(_, _) => ()
  }
  let semantic_span = Some(qualid_span(qualid))
  let symbol = space.find_logic(qualid_segments(qualid), semantic_span)
  let typed_arguments = [
    for argument in arguments => self.type_term(space, locals, argument)
  ]
  self.global_application(space, symbol, typed_arguments, span)
}

///|
fn PureTyping::relation_application(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  left : @parser.Term,
  operator : @parser.Ident,
  right : @parser.Term,
  span : @parser.Span,
) -> DTerm raise {
  let left = self.type_term(space, locals, left)
  let right = self.type_term(space, locals, right)
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
      fail_unsupported(
        Ghost,
        FeatureClassification,
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
    Tconst(ConstStr(_)) =>
      fail_unsupported(
        StringLiteral,
        FeatureClassification,
        Some(source_span(term.span)),
        "string literals are outside the user-visible MVP",
      )
    Tconst(constant) => {
      let type_name = match constant {
        ConstInt(_) => b"int"
        ConstReal(_) => b"real"
        ConstStr(_) => abort("string literal handled above")
      }
      let (delayed, _) = self.named_type(
        space,
        type_name,
        Some(source_span(term.span)),
      )
      make_dterm(
        DConstantTerm(@logic.Constant::from_parser(constant)),
        Some(delayed),
        term.span,
      )
    }
    Tident(qualid) =>
      self.qualid_application(space, locals, qualid, [], term.span)
    Tidapp(qualid, arguments) =>
      self.qualid_application(space, locals, qualid, arguments, term.span)
    Tapply(_, _) => {
      let reversed : Array[@parser.Term] = []
      let head = collect_application(term, reversed)
      let arguments = reversed.rev()
      match head.desc {
        Tident(qualid) =>
          self.qualid_application(space, locals, qualid, arguments, term.span)
        _ => {
          let mut result = self.type_term(space, locals, head)
          for argument in arguments {
            result = self.function_application(
              space,
              result,
              self.type_term(space, locals, argument),
              term.span,
            )
          }
          result
        }
      }
    }
    Tinfix(left, operator, right) | Tinnfix(left, operator, right) =>
      self.relation_application(space, locals, left, operator, right, term.span)
    Tbinop(left, operator, right) | Tbinnop(left, operator, right) => {
      if operator is DTby || operator is DTso {
        fail_unsupported(
          ProofControlConnective,
          FeatureClassification,
          Some(source_span(term.span)),
          "proof-control connectives are outside the MVP",
        )
      }
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
      let then_branch = self.type_term(space, locals, then_branch)
      let else_branch = self.type_term(space, locals, else_branch)
      let result_type = match
        (then_branch.result_type, else_branch.result_type) {
        (None, None) => None
        (None, Some(other)) | (Some(other), None) => {
          self.delayed.unify_expected(
            other,
            self.boolean_dty(space, Some(source_span(term.span))),
            Some(source_span(term.span)),
          )
          None
        }
        (Some(left), Some(right)) => {
          self.delayed.unify_expected(left, right, Some(source_span(term.span)))
          Some(left)
        }
      }
      make_dterm(
        DIfTerm(condition, then_branch, else_branch),
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
      let inner = self.type_term(space, locals, inner)
      let expected = self.dty_of_pty(space, pty)
      self.expect_value(space, inner, expected)
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
      let imported = space.import_scope(qualid_segments(qualid), Some(span))
      self.type_term(imported, locals, inner)
    }
    Ttuple([]) => {
      let symbol = space.find_logic([b"Tuple0"], Some(source_span(term.span)))
      self.global_application(space, symbol, [], term.span)
    }
    Ttuple(_) =>
      fail_unsupported(
        TupleTerm,
        FeatureClassification,
        Some(source_span(term.span)),
        "non-unit tuple terms are outside the MVP",
      )
    Teps(_, _, _) =>
      fail_unsupported(
        Epsilon,
        FeatureClassification,
        Some(source_span(term.span)),
        "epsilon terms are outside the MVP",
      )
    Tcase(_, _) =>
      fail_unsupported(
        DestructuringPattern,
        FeatureClassification,
        Some(source_span(term.span)),
        "pattern matching is outside the MVP",
      )
    Trecord(_) | Tupdate(_, _) =>
      fail_unsupported(
        Datatype,
        FeatureClassification,
        Some(source_span(term.span)),
        "record terms are outside the MVP",
      )
    Tasref(_) =>
      fail_unsupported(
        Reference,
        FeatureClassification,
        Some(source_span(term.span)),
        "reference projection is outside the MVP",
      )
    Tat(_, _) =>
      fail_unsupported(
        OldAt,
        FeatureClassification,
        Some(source_span(term.span)),
        "old/at terms are outside the MVP",
      )
  }
}

///|
fn find_semantic_local(
  values : ArrayView[(Int, @logic.VSymbol)],
  id : Int,
) -> @logic.VSymbol raise @logic.TypeError {
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
  binding : DLocal,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise @logic.TypeError {
  @logic.VSymbol::new(
    self.semantic_context,
    binding.name,
    binding.origin,
    self.delayed.finalize_pure(binding.ty, span),
    span,
  )
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
  semantic.source_decorate(term.source_span, term.attributes)
}

///|
fn PureTyping::finalize_term(
  self : PureTyping,
  space : @theory.Namespace,
  values : ArrayView[(Int, @logic.VSymbol)],
  term : DTerm,
  formula_expected : Bool,
) -> @logic.Term raise {
  let node = match term.node {
    DLocalTerm(binding) =>
      @logic.Term::variable(find_semantic_local(values, binding.id))
    DConstantTerm(constant) => {
      guard term.result_type is Some(delayed) else {
        abort("constant delayed type is missing")
      }
      @logic.Term::constant(
        constant,
        self.delayed.finalize_pure(delayed, term.source_span),
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
          self.finalize_term(space, values, arguments[0], true),
          self.finalize_term(space, values, arguments[1], true),
          term.source_span,
        )
      } else {
        let finalized_arguments = [
          for argument in arguments => {
            self.finalize_term(space, values, argument, false)
          }
        ]
        let result = match term.result_type {
          None => None
          Some(delayed) =>
            Some(self.delayed.finalize_pure(delayed, term.source_span))
        }
        @logic.Term::elaborated_apply(
          symbol,
          finalized_arguments,
          result,
          term.source_span,
        )
      }
    }
    DFunctionApplication =>
      fail_unsupported(
        HigherOrderApplication,
        FeatureClassification,
        term.source_span,
        "higher-order application is outside the MVP",
      )
    DIfTerm(condition, then_branch, else_branch) => {
      let branch_formula = formula_expected || term.result_type is None
      @logic.Term::if_then_else(
        self.finalize_term(space, values, condition, true),
        self.finalize_term(space, values, then_branch, branch_formula),
        self.finalize_term(space, values, else_branch, branch_formula),
        term.source_span,
      )
    }
    DLetTerm(binding, value, body) => {
      let variable = self.semantic_local(binding, term.source_span)
      let nested = values.to_owned()
      nested.push((binding.id, variable))
      @logic.Term::let_in(
        variable,
        self.finalize_term(space, values, value, false),
        self.finalize_term(
          space,
          nested,
          body,
          formula_expected || term.result_type is None,
        ),
        term.source_span,
      )
    }
    DQuantifiedTerm(DTlambda, _, _, _) =>
      fail_unsupported(
        Lambda,
        FeatureClassification,
        term.source_span,
        "lambda terms are outside the MVP",
      )
    DQuantifiedTerm(quantifier, binders, triggers, body) => {
      let nested = values.to_owned()
      let semantic_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let variable = self.semantic_local(binder, term.source_span)
        nested.push((binder.id, variable))
        semantic_binders.push(variable)
      }
      let semantic_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              self.finalize_term(
                space,
                nested,
                trigger,
                trigger.result_type is None,
              )
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
        self.finalize_term(space, nested, body, true),
        term.source_span,
      )
    }
    DBinaryTerm(operator, left, right) => {
      let mut left = self.finalize_term(space, values, left, true)
      if operator is DTandAsym || operator is DTorAsym {
        left = left.add_attributes([b"asym_split"])
      }
      @logic.Term::binary(
        match operator {
          DTand | DTandAsym => And
          DTor | DTorAsym => Or
          DTimplies => Implies
          DTiff => Iff
          DTby | DTso => abort("proof-control connective was rejected")
        },
        left,
        self.finalize_term(space, values, right, true),
        term.source_span,
      )
    }
    DNotTerm(inner) =>
      @logic.Term::not(
        self.finalize_term(space, values, inner, true),
        term.source_span,
      )
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
    DCastTerm(inner) => self.finalize_term(space, values, inner, false)
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
) -> @logic.Term raise {
  let delayed = self.type_term(space, locals, term)
  self.expect_formula(space, delayed)
  self.finalize_term(space, values, delayed, true)
}

///|
fn PureTyping::value(
  self : PureTyping,
  space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  values : ArrayView[(Int, @logic.VSymbol)],
  term : @parser.Term,
  expected : Dty,
) -> @logic.Term raise {
  let delayed = self.type_term(space, locals, term)
  self.expect_value(space, delayed, expected)
  self.finalize_term(space, values, delayed, false)
}

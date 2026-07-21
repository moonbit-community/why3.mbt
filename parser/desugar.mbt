// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

// Parsing-time Why3 Ptree desugaring helpers.

///|
fn make_expr(desc : ExprDesc, span : Span) -> Expr {
  { desc, span }
}

///|
fn anonymous_ident(span : Span) -> Ident {
  { name: b"_", attributes: [], span }
}

///|
fn term_with_cast(term : Term, ty : Pty) -> Term {
  { desc: Tcast(term, ty), span: term.span }
}

///|
fn unfold_term_pattern_let(
  pattern : Pattern,
  value : Term,
  body : Term,
) -> TermDesc {
  fn unfold(
    original : Pattern,
    value : Term,
    current : Pattern,
    body : Term,
  ) -> TermDesc {
    match current.desc {
      Pparen(inner) | Pscope(_, inner) => unfold(original, value, inner, body)
      Pcast(inner, ty) =>
        unfold(original, term_with_cast(value, ty), inner, body)
      Ptuple([]) =>
        unfold(
          original,
          term_with_cast(value, PTtuple([])),
          { ..current, desc: Pwild },
          body,
        )
      Pvar(ident) => Tlet(ident, value, body)
      Pwild => Tlet(anonymous_ident(current.span), value, body)
      _ => Tcase(value, [(original, body)])
    }
  }

  unfold(pattern, value, pattern, body)
}

///|
fn decimal_index_term(index : Int, span : Span) -> Term {
  {
    desc: Tconst(ConstInt({ kind: ILitDec, value: BigInt::from_int(index) })),
    span,
  }
}

///|
fn indexed_term_values(values : Array[Term]) -> Array[(Term, Term)] {
  let mappings : Array[(Term, Term)] = []
  for index, value in values {
    mappings.push((decimal_index_term(index, value.span), value))
  }
  mappings
}

///|
fn function_literal_condition(variable : Term, key : Term) -> Term {
  let equality = Ident::{ name: op_infix(b"="), attributes: [], span: key.span }
  { desc: Tinfix(variable, equality, key), span: key.span }
}

///|
fn function_literal_branch(
  variable : Term,
  mapping : (Term, Term),
  otherwise : Term,
) -> Term {
  let (key, value) = mapping
  {
    desc: Tif(function_literal_condition(variable, key), value, otherwise),
    span: key.span.join(otherwise.span),
  }
}

///|
fn reduce_term_function_literal(
  variable : Term,
  mappings : Array[(Term, Term)],
  default : Term?,
) -> Term {
  if mappings.is_empty() {
    guard default is Some(default) else {
      abort("empty function literal without a default")
    }
    return default
  }
  let mut index = mappings.length() - 1
  let mut result = if default is Some(default) {
    default
  } else {
    let last = mappings[index]
    index = index - 1
    function_literal_branch(variable, last, last.1)
  }
  while index >= 0 {
    result = function_literal_branch(variable, mappings[index], result)
    index = index - 1
  }
  result
}

///|
fn desugar_term_function_literal(
  opening_span : Span,
  closing_span : Span,
  mappings : Array[(Term, Term)],
  default : Term?,
) -> Term {
  let name = if mappings.is_empty() { b"_" } else { b"x'x" }
  let ident = Ident::{ name, attributes: [], span: opening_span }
  let variable = Term::{ desc: Tident(Qident(ident)), span: opening_span }
  let body = reduce_term_function_literal(variable, mappings, default)
  let binder = make_binder(opening_span, Some(ident), false, None)
  let full_span = opening_span.join(closing_span)
  let lambda = Term::{
    desc: Tquant(DTlambda, [binder], [], body),
    span: full_span,
  }
  { desc: Tattr(Text(function_literal_attribute), lambda), span: full_span }
}

///|
priv enum Partiality {
  RegularModifier
  PartialModifier
  GhostModifier
}

///|
fn Partiality::is_ghost(self : Partiality) -> Bool {
  self is GhostModifier
}

///|
fn apply_partial_spec(partiality : Partiality, spec : Spec) -> Spec {
  if partiality is PartialModifier {
    { ..spec, partial: true }
  } else {
    spec
  }
}

///|
fn apply_partial_expr(
  partiality : Partiality,
  expression : Expr,
) -> Expr raise ParseError {
  guard partiality is PartialModifier else { return expression }
  let desc = match expression.desc {
    Efun([_, ..] as binders, return_type, pattern, mask, spec, body) =>
      Efun(
        binders,
        return_type,
        pattern,
        mask,
        apply_partial_spec(partiality, spec),
        body,
      )
    Eany([_, ..] as params, kind, return_type, pattern, mask, spec) =>
      Eany(
        params,
        kind,
        return_type,
        pattern,
        mask,
        apply_partial_spec(partiality, spec),
      )
    _ =>
      return fail_with_diagnostic(
        make_parse_diagnostic(InvalidPartialDeclaration, expression.span),
      )
  }
  { ..expression, desc, }
}

///|
fn expr_with_cast(expression : Expr, ty : Pty) -> Expr {
  { desc: Ecast(expression, ty), span: expression.span }
}

///|
fn push_ghost_pattern(pattern : Pattern) -> Pattern {
  let desc = match pattern.desc {
    Ptuple([first, ..] as elements) => {
      let pushed : Array[Pattern] = [push_ghost_pattern(first)]
      for index = 1; index < elements.length(); index = index + 1 {
        pushed.push(elements[index])
      }
      Ptuple(pushed)
    }
    Pcast(inner, ty) => Pcast(push_ghost_pattern(inner), ty)
    Pas(inner, ident, ghost) => Pas(push_ghost_pattern(inner), ident, ghost)
    Por(left, right) => Por(push_ghost_pattern(left), right)
    _ => Pghost(pattern)
  }
  { ..pattern, desc, }
}

///|
fn simplify_expr_pattern_let(
  kind : RoutineKind,
  value : Expr,
  pattern : Pattern,
  body : Expr,
  kind_span : Span,
) -> ExprDesc raise ParseError {
  fn unfold(
    original : Pattern,
    kind : RoutineKind,
    value : Expr,
    current : Pattern,
    body : Expr,
    ghost : Bool,
    kind_span : Span,
  ) -> ExprDesc raise ParseError {
    match current.desc {
      Pparen(inner) | Pscope(_, inner) =>
        unfold(original, kind, value, inner, body, ghost, kind_span)
      Pghost(inner) =>
        unfold(original, kind, value, inner, body, true, kind_span)
      Pcast(inner, ty) =>
        unfold(
          original,
          kind,
          expr_with_cast(value, ty),
          inner,
          body,
          ghost,
          kind_span,
        )
      Ptuple([]) =>
        unfold(
          original,
          kind,
          expr_with_cast(value, PTtuple([])),
          { ..current, desc: Pwild },
          body,
          ghost,
          kind_span,
        )
      Pvar(ident) => Elet(ident, ghost, kind, value, body)
      Pwild => Elet(anonymous_ident(current.span), ghost, kind, value, body)
      _ =>
        if kind is RKnone {
          Ematch(value, [{ pattern: original, body }], [])
        } else {
          fail_with_diagnostic(
            make_parse_diagnostic(IllegalKindQualifier, kind_span),
          )
        }
    }
  }

  unfold(pattern, kind, value, pattern, body, false, kind_span)
}

///|
fn any_result_term(span : Span) -> Term {
  let ident = Ident::{ name: b"result", attributes: [], span }
  make_term(Tident(Qident(ident)), span)
}

///|
fn any_postcondition_term(post : PostCondition) -> Term {
  let result = any_result_term(post.span)
  guard post.branches is [(pattern, formula)] else {
    return make_term(Tcase(result, post.branches), post.span)
  }
  fn unfold(
    branches : Array[(Pattern, Term)],
    value : Term,
    pattern : Pattern,
    formula : Term,
    span : Span,
  ) -> Term {
    match pattern.desc {
      Pparen(inner) | Pscope(_, inner) =>
        unfold(branches, value, inner, formula, span)
      Pcast(inner, ty) =>
        unfold(branches, term_with_cast(value, ty), inner, formula, span)
      Ptuple([]) =>
        unfold(
          branches,
          term_with_cast(value, PTtuple([])),
          { ..pattern, desc: Pwild },
          formula,
          span,
        )
      Pvar({ name: b"result", .. }) | Pwild =>
        if value.desc is Tident(Qident(_)) {
          formula
        } else {
          make_term(Tlet(anonymous_ident(pattern.span), value, formula), span)
        }
      Pvar(ident) => make_term(Tlet(ident, value, formula), span)
      _ => make_term(Tcase(value, branches), span)
    }
  }

  unfold(post.branches, result, pattern, formula, post.span)
}

///|
fn preconditions_of_any(
  any_span : Span,
  return_type : Pty,
  postconditions : Array[PostCondition],
) -> Array[Term] {
  guard !postconditions.is_empty() else { return [] }
  let mut index = postconditions.length() - 1
  let mut conjunction = any_postcondition_term(postconditions[index])
  while index > 0 {
    index = index - 1
    conjunction = make_term(
      Tbinop(
        any_postcondition_term(postconditions[index]),
        DTandAsym,
        conjunction,
      ),
      any_span,
    )
  }
  let result_ident = Ident::{
    name: b"result",
    attributes: [Text(break_attribute)],
    span: any_span,
  }
  let binder = make_binder(
    any_span,
    Some(result_ident),
    false,
    Some(return_type),
  )
  let quantified = make_term(
    Tquant(DTexists, [binder], [], conjunction),
    any_span,
  )
  [make_term(Tattr(Text(witness_existence_attribute), quantified), any_span)]
}

///|
fn assignment_get_parts(expression : Expr) -> (Ident, Expr, Expr)? {
  guard expression.desc is Eidapp(Qident(ident), [base, index]) &&
    notation_decode(ident.name) is SNget(_) else {
    return None
  }
  Some((ident, base, index))
}

///|
fn assignment_item(
  left : Expr,
  right : Expr,
  attributes : Array[Attribute],
) -> Assignment raise ParseError {
  let mut target = left
  while target.desc is Eattr(attribute, inner) {
    attributes.push(attribute)
    target = inner
  }
  match target.desc {
    Eident(path) => {
      let reference = { ..target, desc: Easref(path) }
      { target: reference, field: None, value: right }
    }
    Eidapp(path, [base]) => { target: base, field: Some(path), value: right }
    Eidapp(Qident(ident), [_, _]) =>
      if notation_decode(ident.name) is SNget(_) {
        fail_with_diagnostic(
          make_parse_diagnostic(InvalidParallelAssignment, target.span),
        )
      } else {
        fail_with_diagnostic(
          make_parse_diagnostic(InvalidAssignment, target.span),
        )
      }
    _ =>
      fail_with_diagnostic(
        make_parse_diagnostic(InvalidAssignment, target.span),
      )
  }
}

///|
fn desugar_assignment(
  left : Expr,
  right : Expr,
  full_span : Span,
) -> ExprDesc raise ParseError {
  match assignment_get_parts(left) {
    Some((ident, base, index)) => {
      let suffix = match notation_decode(ident.name) {
        SNget(suffix) => suffix
        _ => abort("assignment_get_parts returned a non-getter")
      }
      let set_ident = { ..ident, name: op_set(suffix) }
      return Eidapp(Qident(set_ident), [base, index, right])
    }
    None => ()
  }
  let (lefts, rights) = match (left.desc, right.desc) {
    (Etuple(lefts), Etuple(rights)) => (lefts, rights)
    (Etuple(_), _) =>
      return fail_with_diagnostic(
        make_parse_diagnostic(InvalidParallelAssignment, full_span),
      )
    _ => ([left], [right])
  }
  guard lefts.length() == rights.length() else {
    return fail_with_diagnostic(
      make_parse_diagnostic(InvalidParallelAssignment, full_span),
    )
  }
  let assignments : Array[Assignment] = []
  let attributes : Array[Attribute] = []
  for index = 0; index < lefts.length(); index = index + 1 {
    assignments.push(assignment_item(lefts[index], rights[index], attributes))
  }
  let mut desc : ExprDesc = Eassign(assignments)
  let mut index = attributes.length() - 1
  while index >= 0 {
    desc = Eattr(attributes[index], make_expr(desc, full_span))
    index = index - 1
  }
  desc
}

///|
fn decimal_index_expr(index : Int, span : Span) -> Expr {
  make_expr(
    Econst(ConstInt({ kind: ILitDec, value: BigInt::from_int(index) })),
    span,
  )
}

///|
fn indexed_expr_values(values : Array[Expr]) -> Array[(Expr, Expr)] {
  let mappings : Array[(Expr, Expr)] = []
  for index, value in values {
    mappings.push((decimal_index_expr(index, value.span), value))
  }
  mappings
}

///|
fn proxy_expr(name : Bytes, span : Span) -> Expr {
  let ident = Ident::{ name, attributes: [Text(proxy_attribute)], span }
  make_expr(Eident(Qident(ident)), span)
}

///|
fn plain_expr_variable(ident : Ident, span : Span) -> Expr {
  make_expr(Eident(Qident(ident)), span)
}

///|
fn expr_proxy_ident(expression : Expr) -> Ident {
  guard expression.desc is Eident(Qident(ident)) else {
    abort("expected an expression proxy variable")
  }
  ident
}

///|
fn function_literal_expr_branch(
  variable : Expr,
  mapping : (Expr, Expr),
  otherwise : Expr,
) -> Expr {
  let (key, value) = mapping
  let equality = Ident::{ name: op_infix(b"="), attributes: [], span: key.span }
  let condition = make_expr(Einfix(variable, equality, key), key.span)
  make_expr(Eif(condition, value, otherwise), key.span.join(otherwise.span))
}

///|
fn reduce_expr_function_literal(
  variable : Expr,
  mappings : Array[(Expr, Expr)],
  default : Expr?,
) -> Expr {
  if mappings.is_empty() {
    guard default is Some(default) else {
      abort("empty expression function literal without a default")
    }
    return default
  }
  let mut index = mappings.length() - 1
  let mut result = if default is Some(default) {
    default
  } else {
    let last = mappings[index]
    index = index - 1
    function_literal_expr_branch(variable, last, last.1)
  }
  while index >= 0 {
    result = function_literal_expr_branch(variable, mappings[index], result)
    index = index - 1
  }
  result
}

///|
fn desugar_expr_function_literal(
  opening_span : Span,
  closing_span : Span,
  mappings : Array[(Expr, Expr)],
  default : Expr?,
) -> Expr {
  let full_span = opening_span.join(closing_span)
  let proxies : Array[(Expr, Expr)] = []
  for index, mapping in mappings {
    let decimal = @utf8.encode(index.to_string()[:])
    proxies.push(
      (
        proxy_expr(b"d'i" + decimal, mapping.0.span),
        proxy_expr(b"r'i" + decimal, mapping.1.span),
      ),
    )
  }
  let default_proxy = if default is Some(value) {
    Some(proxy_expr(b"def'e", value.span))
  } else {
    None
  }
  let function_ident = Ident::{
    name: if mappings.is_empty() {
      b"_"
    } else {
      b"x'x"
    },
    attributes: [],
    span: opening_span,
  }
  let function_variable = plain_expr_variable(function_ident, opening_span)
  let body = reduce_expr_function_literal(
    function_variable, proxies, default_proxy,
  )
  let binder = make_binder(opening_span, Some(function_ident), false, None)
  let return_pattern = make_pattern(Pvar(function_ident), opening_span)
  let mut expression = make_expr(
    Efun([binder], None, return_pattern, MaskVisible, Spec::empty(), body),
    full_span,
  )
  for index = 0; index < mappings.length(); index = index + 1 {
    let range_ident = expr_proxy_ident(proxies[index].1)
    expression = make_expr(
      Elet(range_ident, false, RKnone, mappings[index].1, expression),
      full_span,
    )
    let domain_ident = expr_proxy_ident(proxies[index].0)
    expression = make_expr(
      Elet(domain_ident, false, RKnone, mappings[index].0, expression),
      full_span,
    )
  }
  match (default, default_proxy) {
    (Some(default), Some(proxy)) =>
      expression = make_expr(
        Elet(expr_proxy_ident(proxy), false, RKnone, default, expression),
        full_span,
      )
    _ => ()
  }
  make_expr(Eattr(Text(function_literal_attribute), expression), full_span)
}

///|
fn optional_exception(ident : Ident, mask : Mask, expression : Expr) -> Expr {
  { ..expression, desc: Eoptexn(ident, mask, expression) }
}

///|
fn append_control_suffix(ident : Ident, suffix : Bytes) -> Ident {
  { ..ident, name: ident.name + suffix }
}

///|
fn label_over_loop(label : Ident, expression : Expr) -> Expr {
  fn continue_body(label : Ident, body : Expr) -> Expr {
    optional_exception(
      append_control_suffix(label, continue_label),
      MaskVisible,
      body,
    )
  }

  fn over(label : Ident, expression : Expr) -> Expr {
    let desc = match expression.desc {
      Escope(path, inner) => Escope(path, over(label, inner))
      Eattr(attribute, inner) => Eattr(attribute, over(label, inner))
      Ecast(inner, ty) => Ecast(over(label, inner), ty)
      Eghost(inner) => Eghost(over(label, inner))
      Esequence(left, right) => Esequence(over(label, left), right)
      Eoptexn(ident, mask, inner) => Eoptexn(ident, mask, over(label, inner))
      Ewhile(condition, invariant, variant, body) => {
        let loop_expression = {
          ..expression,
          desc: Ewhile(
            condition,
            invariant,
            variant,
            continue_body(label, body),
          ),
        }
        Eoptexn(
          append_control_suffix(label, break_label),
          MaskVisible,
          loop_expression,
        )
      }
      Efor(ident, from, direction, to, invariant, body) => {
        let loop_expression = {
          ..expression,
          desc: Efor(
            ident,
            from,
            direction,
            to,
            invariant,
            continue_body(label, body),
          ),
        }
        Eoptexn(
          append_control_suffix(label, break_label),
          MaskVisible,
          loop_expression,
        )
      }
      desc => desc
    }
    { ..expression, desc, }
  }

  make_expr(
    Elabel(label, over(label, expression)),
    label.span.join(expression.span),
  )
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum Quantifier {
  ForallQuantifier
  ExistsQuantifier
} derive(Eq, Debug)

///|
pub(all) enum BinaryLogicOp {
  And
  Or
  Implies
  Iff
} derive(Eq, Debug)

///|
struct TermBranch {
  pattern : Pattern
  body : Term
}

///|
priv enum TermNode {
  VariableTerm(VSymbol)
  ConstantTerm(Constant)
  ApplicationTerm(LSymbol, Array[(TyVarSymbol, Ty)], Array[Term])
  IfTerm(Term, Term, Term)
  LetTerm(VSymbol, Term, Term)
  CaseTerm(Term, Array[TermBranch])
  EpsilonTerm(VSymbol, Term)
  QuantifiedTerm(Quantifier, Array[VSymbol], Array[Array[Term]], Term)
  BinaryTerm(BinaryLogicOp, Term, Term)
  NotTerm(Term)
  TrueTerm
  FalseTerm
}

///|
/// An immutable typed value term or formula. `result_type = None` denotes a
/// formula and is never interchangeable with a value of boolean type.
struct Term {
  node : TermNode
  result_type : Ty?
  origin : @identity.Origin?
  source_span : @identity.SourceSpan?
  attributes : @identity.SemanticAttributes
}

///|
pub(all) struct TermBranchView {
  pattern : Pattern
  body : Term
}

///|
pub(all) enum TermView {
  Tvar(VSymbol)
  Tconst(Constant)
  Tapp(LSymbol, ArrayView[(TyVarSymbol, Ty)], ArrayView[Term])
  Tif(Term, Term, Term)
  Tlet(VSymbol, Term, Term)
  Tcase(Term, ArrayView[TermBranch])
  Teps(VSymbol, Term)
  Tquant(Quantifier, ArrayView[VSymbol], ArrayView[Array[Term]], Term)
  Tbinop(BinaryLogicOp, Term, Term)
  Tnot(Term)
  Ttrue
  Tfalse
}

///|
fn make_term(node : TermNode, result_type : Ty?) -> Term {
  {
    node,
    result_type,
    origin: None,
    source_span: None,
    attributes: @identity.SemanticAttributes::empty(),
  }
}

///|
fn Term::copy_decoration(self : Term, replacement : Term) -> Term {
  let attributes = replacement.attributes.items().to_owned()
  for attribute in self.attributes.items() {
    attributes.push(attribute)
  }
  {
    ..replacement,
    origin: match replacement.origin {
      Some(_) => replacement.origin
      None => self.origin
    },
    source_span: match replacement.source_span {
      Some(_) => replacement.source_span
      None => self.source_span
    },
    attributes: @identity.SemanticAttributes::from_array(attributes),
  }
}

///|
pub fn Term::ty(self : Term) -> Ty? {
  self.result_type
}

///|
pub fn Term::is_formula(self : Term) -> Bool {
  self.result_type is None
}

///|
pub fn Term::is_value(self : Term) -> Bool {
  self.result_type is Some(_)
}

///|
pub fn Term::origin(self : Term) -> @identity.Origin? {
  self.origin
}

///|
pub fn Term::source_span(self : Term) -> @identity.SourceSpan? {
  self.source_span
}

///|
pub fn Term::attributes(self : Term) -> ArrayView[Bytes] {
  self.attributes.items()
}

///|
/// Adds semantic decoration without changing the typed node.
pub fn Term::decorate(
  self : Term,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> Term {
  {
    ..self,
    origin: Some(origin),
    attributes: @identity.SemanticAttributes::from_array(attributes),
  }
}

///|
/// Adds source attributes while preserving existing decoration. This mirrors
/// Why3's set-union behavior for nested `Tattr` nodes.
pub fn Term::add_attributes(self : Term, attributes : ArrayView[Bytes]) -> Term {
  let combined = self.attributes.items().to_owned()
  for attribute in attributes {
    combined.push(attribute)
  }
  { ..self, attributes: @identity.SemanticAttributes::from_array(combined) }
}

///|
/// Attaches a user source location independently from symbol provenance.
pub fn Term::source_decorate(
  self : Term,
  source_span : @identity.SourceSpan?,
  attributes : ArrayView[Bytes],
) -> Term {
  {
    ..self,
    source_span,
    attributes: @identity.SemanticAttributes::from_array(attributes),
  }
}

///|
/// Restores the independent source location and attributes carried by the
/// frozen Why3 term graph. The symbol origin remains unchanged because terms
/// are not global catalog entries.
pub fn Term::trusted_snapshot_decorate(
  self : Term,
  source_span : @identity.SourceSpan?,
  attributes : ArrayView[Bytes],
) -> Term {
  {
    ..self,
    source_span,
    attributes: @identity.SemanticAttributes::from_array(attributes),
  }
}

///|
pub fn Term::view(self : Term) -> TermView {
  match self.node {
    VariableTerm(variable) => Tvar(variable)
    ConstantTerm(constant) => Tconst(constant)
    ApplicationTerm(symbol, instantiation, arguments) =>
      Tapp(symbol, instantiation[:], arguments[:])
    IfTerm(condition, then_branch, else_branch) =>
      Tif(condition, then_branch, else_branch)
    LetTerm(variable, value, body) => Tlet(variable, value, body)
    CaseTerm(scrutinee, branches) => Tcase(scrutinee, branches[:])
    EpsilonTerm(variable, body) => Teps(variable, body)
    QuantifiedTerm(quantifier, binders, triggers, body) =>
      Tquant(quantifier, binders[:], triggers[:], body)
    BinaryTerm(operator, left, right) => Tbinop(operator, left, right)
    NotTerm(term) => Tnot(term)
    TrueTerm => Ttrue
    FalseTerm => Tfalse
  }
}

///|
pub fn TermBranch::view(self : TermBranch) -> TermBranchView {
  { pattern: self.pattern, body: self.body }
}

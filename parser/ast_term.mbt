///|
pub(all) struct Term {
  desc : TermDesc
  span : Span
} derive(Debug, Eq)

///|
pub(all) enum TermDesc {
  Ttrue
  Tfalse
  Tconst(Constant)
  Tident(QualId)
  Tasref(QualId)
  Tidapp(QualId, Array[Term])
  Tapply(Term, Term)
  Tinfix(Term, Ident, Term)
  Tinnfix(Term, Ident, Term)
  Tbinop(Term, BinaryLogicOp, Term)
  Tbinnop(Term, BinaryLogicOp, Term)
  Tnot(Term)
  Tif(Term, Term, Term)
  Tquant(Quantifier, Array[Binder], Array[Array[Term]], Term)
  Teps(Ident, Pty, Term)
  Tattr(Attribute, Term)
  Tlet(Ident, Term, Term)
  Tcase(Term, Array[(Pattern, Term)])
  Tcast(Term, Pty)
  Ttuple(Array[Term])
  Trecord(Array[(QualId, Term)])
  Tupdate(Term, Array[(QualId, Term)])
  Tscope(QualId, Term)
  Tat(Term, Ident)
} derive(Debug, Eq)

///|
pub(all) struct Invariant {
  terms : Array[Term]
} derive(Debug, Eq)

///|
pub(all) struct Variant {
  items : Array[(Term, QualId?)]
} derive(Debug, Eq)

///|
pub(all) struct PostCondition {
  span : Span
  branches : Array[(Pattern, Term)]
} derive(Debug, Eq)

///|
pub(all) struct ExceptionalPostCondition {
  span : Span
  branches : Array[(QualId, (Pattern, Term)?)]
} derive(Debug, Eq)

///|
pub(all) struct Spec {
  preconditions : Array[Term]
  postconditions : Array[PostCondition]
  exceptional_postconditions : Array[ExceptionalPostCondition]
  reads : Array[QualId]
  writes : Array[Term]
  aliases : Array[(Term, Term)]
  variant : Variant
  check_reads_writes : Bool
  diverges : Bool
  partial : Bool
} derive(Debug, Eq)

///|
pub fn Spec::empty() -> Spec {
  {
    preconditions: [],
    postconditions: [],
    exceptional_postconditions: [],
    reads: [],
    writes: [],
    aliases: [],
    variant: { items: [] },
    check_reads_writes: false,
    diverges: false,
    partial: false,
  }
}

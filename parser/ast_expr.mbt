// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub(all) struct Expr {
  desc : ExprDesc
  span : Span
} derive(Debug, Eq)

///|
pub(all) struct RegularBranch {
  pattern : Pattern
  body : Expr
} derive(Debug, Eq)

///|
pub(all) struct ExceptionBranch {
  exception : QualId
  pattern : Pattern?
  body : Expr
} derive(Debug, Eq)

///|
pub(all) struct FunctionDef {
  name : Ident
  ghost : Bool
  kind : RoutineKind
  binders : Array[Binder]
  return_type : Pty?
  return_pattern : Pattern
  mask : Mask
  spec : Spec
  body : Expr
} derive(Debug, Eq)

///|
pub(all) struct Assignment {
  target : Expr
  field : QualId?
  value : Expr
} derive(Debug, Eq)

///|
pub(all) enum ExprDesc {
  Eref
  Etrue
  Efalse
  Econst(Constant)
  Eident(QualId)
  Easref(QualId)
  Eidapp(QualId, Array[Expr])
  Eapply(Expr, Expr)
  Einfix(Expr, Ident, Expr)
  Einnfix(Expr, Ident, Expr)
  Elet(Ident, Bool, RoutineKind, Expr, Expr)
  Erec(Array[FunctionDef], Expr)
  Efun(Array[Binder], Pty?, Pattern, Mask, Spec, Expr)
  Eany(Array[Param], RoutineKind, Pty?, Pattern, Mask, Spec)
  Etuple(Array[Expr])
  Erecord(Array[(QualId, Expr)])
  Eupdate(Expr, Array[(QualId, Expr)])
  Eassign(Array[Assignment])
  Esequence(Expr, Expr)
  Eif(Expr, Expr, Expr)
  Ewhile(Expr, Invariant, Variant, Expr)
  Eand(Expr, Expr)
  Eor(Expr, Expr)
  Enot(Expr)
  Ematch(Expr, Array[RegularBranch], Array[ExceptionBranch])
  Eabsurd
  Epure(Term)
  Eidpur(QualId)
  Eraise(QualId, Expr?)
  Eexn(Ident, Pty, Mask, Expr)
  Eoptexn(Ident, Mask, Expr)
  Efor(Ident, Expr, ForDirection, Expr, Invariant, Expr)
  Eassert(AssertionKind, Term)
  Escope(QualId, Expr)
  Elabel(Ident, Expr)
  Ecast(Expr, Pty)
  Eghost(Expr)
  Eattr(Attribute, Expr)
} derive(Debug, Eq)

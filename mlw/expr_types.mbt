// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum PatternGhost {
  PGfail
  PGlast
  PGnone
} derive(Eq, Debug)

///|
pub(all) enum PrePattern {
  PPwild
  PPvar(@theory.SemanticName, Bool)
  PPapp(RoutineSymbol, Array[PrePattern])
  PPas(PrePattern, @theory.SemanticName, Bool)
  PPor(PrePattern, PrePattern)
}

///|
struct ProgramPattern {
  pattern : @logic.Pattern
  ity : Ity
  mask : ProgramMask
  failure : PatternGhost
  variables : Array[PVariable]
}

///|
pub(all) struct ProgramPatternView {
  pattern : @logic.Pattern
  ity : Ity
  mask : ProgramMask
  failure : PatternGhost
  variables : ArrayView[PVariable]
}

///|
pub(all) enum AssertionKind {
  Assert
  Assume
  Check
} derive(Eq, Debug)

///|
pub(all) enum ForDirection {
  To
  DownTo
} derive(Eq, Debug)

///|
struct ForBounds {
  first : PVariable
  direction : ForDirection
  last : PVariable
}

///|
pub(all) struct ForBoundsView {
  first : PVariable
  direction : ForDirection
  last : PVariable
}

///|
struct ProgramVariant {
  term : @logic.Term
  relation : @logic.LSymbol?
}

///|
pub(all) struct ProgramVariantView {
  term : @logic.Term
  relation : @logic.LSymbol?
}

///|
struct Assignment {
  region : PVariable
  field : RoutineSymbol
  value : PVariable
}

///|
pub(all) struct AssignmentView {
  region : PVariable
  field : RoutineSymbol
  value : PVariable
}

///|
priv enum CexpNode {
  CallCexp(RoutineSymbol, Array[PVariable])
  PureCexp(@logic.LSymbol, Array[PVariable])
  FunctionCexp(Expr)
  AnyCexp
}

///|
struct Cexp {
  node : CexpNode
  mut cty : Cty
}

///|
pub(all) enum CexpView {
  Capp(RoutineSymbol, ArrayView[PVariable])
  Cpur(@logic.LSymbol, ArrayView[PVariable])
  Cfun(Expr)
  Cany
}

///|
priv enum LetDefinitionNode {
  VariableDefinition(PVariable, Expr)
  SymbolDefinition(RoutineSymbol, Cexp)
  RecursiveDefinitions(Array[RecursiveDefinition])
}

///|
struct LetDefinition {
  definition_node : LetDefinitionNode
}

///|
pub(all) enum LetDefinitionView {
  LDvar(PVariable, Expr)
  LDsym(RoutineSymbol, Cexp)
  LDrec(ArrayView[RecursiveDefinition])
}

///|
struct RecursiveDefinition {
  symbol : RoutineSymbol
  internal_symbol : RoutineSymbol
  function_ : Cexp
  variants : Array[ProgramVariant]
}

///|
pub(all) struct RecursiveDefinitionView {
  symbol : RoutineSymbol
  internal_symbol : RoutineSymbol
  function_ : Cexp
  variants : ArrayView[ProgramVariant]
}

///|
struct RegularBranch {
  pattern : ProgramPattern
  body : Expr
}

///|
pub(all) struct RegularBranchView {
  pattern : ProgramPattern
  body : Expr
}

///|
struct ExceptionalBranch {
  exception : XSymbol
  variables : Array[PVariable]
  body : Expr
}

///|
pub(all) struct ExceptionalBranchView {
  exception : XSymbol
  variables : ArrayView[PVariable]
  body : Expr
}

///|
priv enum ExprNode {
  VariableExpr(PVariable)
  ConstantExpr(@logic.Constant)
  ExecuteExpr(Cexp, Cty)
  AssignmentExpr(Array[Assignment])
  LetExpr(LetDefinition, Expr)
  IfExpr(Expr, Expr, Expr)
  MatchExpr(Expr, Array[RegularBranch], Array[ExceptionalBranch])
  WhileExpr(Expr, Array[@logic.Term], Array[ProgramVariant], Expr)
  ForExpr(PVariable, ForBounds, PVariable, Array[@logic.Term], Expr)
  RaiseExpr(XSymbol, Expr)
  ExceptionExpr(XSymbol, Expr)
  AssertionExpr(AssertionKind, @logic.Term)
  GhostExpr(Expr)
  PureExpr(@logic.Term)
  AbsurdExpr
}

///|
pub(all) enum ExprView {
  Evar(PVariable)
  Econst(@logic.Constant)
  Eexec(Cexp, Cty)
  Eassign(ArrayView[Assignment])
  Elet(LetDefinition, Expr)
  Eif(Expr, Expr, Expr)
  Ematch(Expr, ArrayView[RegularBranch], ArrayView[ExceptionalBranch])
  Ewhile(Expr, ArrayView[@logic.Term], ArrayView[ProgramVariant], Expr)
  Efor(PVariable, ForBounds, PVariable, ArrayView[@logic.Term], Expr)
  Eraise(XSymbol, Expr)
  Eexn(XSymbol, Expr)
  Eassert(AssertionKind, @logic.Term)
  Eghost(Expr)
  Epure(@logic.Term)
  Eabsurd
}

///|
struct Expr {
  mut node : ExprNode
  ity : Ity
  origin : @identity.Origin
  attributes : @identity.SemanticAttributes
  mut effect : Effect
  mask : ProgramMask
}

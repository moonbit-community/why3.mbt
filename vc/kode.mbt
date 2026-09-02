// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub(all) enum VcMode {
  ClassicalWp
  EfficientSp
} derive(Eq, Debug)

///|
pub struct VcOptions {
  mode : VcMode
  keep_trace : Bool
  evaluate_matches : Bool
} derive(Eq, Debug)

///|
pub fn VcOptions::classical() -> VcOptions {
  { mode: ClassicalWp, keep_trace: true, evaluate_matches: true }
}

///|
pub fn VcOptions::efficient() -> VcOptions {
  { mode: EfficientSp, keep_trace: true, evaluate_matches: true }
}

///|
pub fn VcOptions::uses_efficient_sp(self : VcOptions) -> Bool {
  self.mode == EfficientSp
}

///|
pub fn VcOptions::with_keep_trace(
  self : VcOptions,
  keep_trace : Bool,
) -> VcOptions {
  { ..self, keep_trace, }
}

///|
pub fn VcOptions::with_match_evaluation(
  self : VcOptions,
  evaluate_matches : Bool,
) -> VcOptions {
  { ..self, evaluate_matches, }
}

///|
fn VcOptions::vc_mode(self : VcOptions) -> VcMode {
  self.mode
}

///|
fn VcOptions::keeps_trace(self : VcOptions) -> Bool {
  self.keep_trace
}

///|
fn VcOptions::evaluates_matches(self : VcOptions) -> Bool {
  self.evaluate_matches
}

///|
pub(all) struct VcHavocWrite {
  region : @mlw.Region
  fields : Array[@mlw.PVariable]
}

///|
priv enum KodeNode {
  Seq(Kode, Int, Kode)
  Par(Kode, Kode)
  If(@mlw.PVariable, Kode, Kode)
  Case(@mlw.PVariable, Array[(@logic.Pattern, Kode)])
  Havoc(Array[@mlw.PVariable], Array[VcHavocWrite], @identity.SourceSpan?)
  Let(@mlw.PVariable, @logic.Term, @logic.Term)
  Val(Array[@mlw.PVariable], @logic.Term)
  Cut(@logic.Term)
  Stop(@logic.Term)
  Cont(Int)
  ExplanationOffset(Bytes, Kode)
  Mode(VcMode, Kode)
  OutcomeFilter(Array[Int], Kode)
  PushContinuation(Bool, Kode)
}

///|
struct Kode {
  node : KodeNode
}

///|
pub(all) enum KodeView {
  Kseq(Kode, Int, Kode)
  Kpar(Kode, Kode)
  Kif(@mlw.PVariable, Kode, Kode)
  Kcase(@mlw.PVariable, ArrayView[(@logic.Pattern, Kode)])
  Khavoc(
    ArrayView[@mlw.PVariable],
    ArrayView[VcHavocWrite],
    @identity.SourceSpan?
  )
  Klet(@mlw.PVariable, @logic.Term, @logic.Term)
  Kval(ArrayView[@mlw.PVariable], @logic.Term)
  Kcut(@logic.Term)
  Kstop(@logic.Term)
  Kcont(Int)
  Koff(BytesView, Kode)
  Kmode(VcMode, Kode)
  Kout(ArrayView[Int], Kode)
  Kpush(Bool, Kode)
}

///|
fn kseq(first : Kode, continuation : Int, second : Kode) -> Kode {
  { node: Seq(first, continuation, second) }
}

///|
fn kpar(left : Kode, right : Kode) -> Kode {
  { node: Par(left, right) }
}

///|
fn kif(condition : @mlw.PVariable, yes : Kode, no : Kode) -> Kode {
  { node: If(condition, yes, no) }
}

///|
fn kcase(
  scrutinee : @mlw.PVariable,
  branches : ArrayView[(@logic.Pattern, Kode)],
) -> Kode {
  { node: Case(scrutinee, branches.to_owned()) }
}

///|
fn khavoc(
  affected : ArrayView[@mlw.PVariable],
  writes : ArrayView[VcHavocWrite],
  span : @identity.SourceSpan?,
) -> Kode {
  { node: Havoc(affected.to_owned(), writes.to_owned(), span) }
}

///|
fn klet(
  binder : @mlw.PVariable,
  value : @logic.Term,
  constraint : @logic.Term,
) -> Kode {
  { node: Let(binder, value, constraint) }
}

///|
fn kval(binders : ArrayView[@mlw.PVariable], constraint : @logic.Term) -> Kode {
  { node: Val(binders.to_owned(), constraint) }
}

///|
fn kcut(formula : @logic.Term) -> Kode {
  { node: Cut(formula) }
}

///|
fn kstop(formula : @logic.Term) -> Kode {
  { node: Stop(formula) }
}

///|
fn kcont(index : Int) -> Kode {
  { node: Cont(index) }
}

///|
fn koff(explanation : BytesView, kode : Kode) -> Kode {
  { node: ExplanationOffset(explanation.to_owned(), kode) }
}

///|
fn kmode(mode : VcMode, kode : Kode) -> Kode {
  { node: Mode(mode, kode) }
}

///|
fn kout(outcomes : ArrayView[Int], kode : Kode) -> Kode {
  { node: OutcomeFilter(outcomes.to_owned(), kode) }
}

///|
fn kpush(closed : Bool, kode : Kode) -> Kode {
  { node: PushContinuation(closed, kode) }
}

///|
pub fn Kode::continue_normally() -> Kode {
  kcont(0)
}

///|
pub fn Kode::view(self : Kode) -> KodeView {
  match self.node {
    Seq(first, continuation, second) => Kseq(first, continuation, second)
    Par(left, right) => Kpar(left, right)
    If(condition, yes, no) => Kif(condition, yes, no)
    Case(scrutinee, branches) => Kcase(scrutinee, branches[:])
    Havoc(affected, writes, span) => Khavoc(affected[:], writes[:], span)
    Let(binder, value, constraint) => Klet(binder, value, constraint)
    Val(binders, constraint) => Kval(binders[:], constraint)
    Cut(formula) => Kcut(formula)
    Stop(formula) => Kstop(formula)
    Cont(index) => Kcont(index)
    ExplanationOffset(explanation, kode) => Koff(explanation[:], kode)
    Mode(mode, kode) => Kmode(mode, kode)
    OutcomeFilter(outcomes, kode) => Kout(outcomes[:], kode)
    PushContinuation(closed, kode) => Kpush(closed, kode)
  }
}

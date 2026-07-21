// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv enum KodeNode {
  Seq(Kode, Int, Kode)
  Par(Kode, Kode)
  If(@mlw.PVariable, Kode, Kode)
  Let(@mlw.PVariable, @logic.Term, @logic.Term)
  Val(Array[@mlw.PVariable], @logic.Term)
  Cut(@logic.Term)
  Stop(@logic.Term)
  Cont(Int)
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
  Klet(@mlw.PVariable, @logic.Term, @logic.Term)
  Kval(ArrayView[@mlw.PVariable], @logic.Term)
  Kcut(@logic.Term)
  Kstop(@logic.Term)
  Kcont(Int)
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
pub fn Kode::continue_normally() -> Kode {
  { node: Cont(0) }
}

///|
pub fn Kode::view(self : Kode) -> KodeView {
  match self.node {
    Seq(first, continuation, second) => Kseq(first, continuation, second)
    Par(left, right) => Kpar(left, right)
    If(condition, yes, no) => Kif(condition, yes, no)
    Let(binder, value, constraint) => Klet(binder, value, constraint)
    Val(binders, constraint) => Kval(binders[:], constraint)
    Cut(formula) => Kcut(formula)
    Stop(formula) => Kstop(formula)
    Cont(index) => Kcont(index)
  }
}

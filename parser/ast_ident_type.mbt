// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub(all) enum Attribute {
  Text(Bytes)
  Position(Span)
} derive(Debug, Eq)

///|
pub(all) struct Ident {
  name : Bytes
  attributes : Array[Attribute]
  span : Span
} derive(Debug, Eq)

///|
pub(all) enum QualId {
  Qident(Ident)
  Qdot(QualId, Ident)
} derive(Debug, Eq)

///|
pub(all) enum Pty {
  PTtyvar(Ident)
  PTtyapp(QualId, Array[Pty])
  PTtuple(Array[Pty])
  PTref(Array[Pty])
  PTarrow(Pty, Pty)
  PTscope(QualId, Pty)
  PTparen(Pty)
  PTpure(Pty)
} derive(Debug, Eq)

///|
pub(all) struct Pattern {
  desc : PatternDesc
  span : Span
} derive(Debug, Eq)

///|
pub(all) enum PatternDesc {
  Pwild
  Pvar(Ident)
  Papp(QualId, Array[Pattern])
  Prec(Array[(QualId, Pattern)])
  Ptuple(Array[Pattern])
  Pas(Pattern, Ident, Bool)
  Por(Pattern, Pattern)
  Pcast(Pattern, Pty)
  Pscope(QualId, Pattern)
  Pparen(Pattern)
  Pghost(Pattern)
} derive(Debug, Eq)

///|
/// A logical binder. Why3's Ptree deliberately permits an anonymous,
/// untyped binder for syntax such as `fun _ -> value`.
pub struct Binder {
  span : Span
  ident : Ident?
  ghost : Bool
  binder_type : Pty?
} derive(Debug, Eq)

///|
fn make_binder(
  span : Span,
  ident : Ident?,
  ghost : Bool,
  binder_type : Pty?,
) -> Binder {
  { span, ident, ghost, binder_type }
}

///|
/// A program parameter always has a type, even when it is anonymous.
pub(all) struct Param {
  span : Span
  ident : Ident?
  ghost : Bool
  param_type : Pty
} derive(Debug, Eq)

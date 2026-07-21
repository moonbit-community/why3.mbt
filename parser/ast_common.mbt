// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub(all) enum BinaryLogicOp {
  DTand
  DTandAsym
  DTor
  DTorAsym
  DTimplies
  DTiff
  DTby
  DTso
} derive(Debug, Eq)

///|
pub(all) enum Quantifier {
  DTforall
  DTexists
  DTlambda
} derive(Debug, Eq)

///|
pub(all) enum RoutineKind {
  RKnone
  RKlocal
  RKfunc
  RKpred
  RKlemma
} derive(Debug, Eq)

///|
pub(all) enum AssertionKind {
  Assert
  Assume
  Check
} derive(Debug, Eq)

///|
pub(all) enum ForDirection {
  To
  DownTo
} derive(Debug, Eq)

///|
pub(all) enum Mask {
  MaskVisible
  MaskTuple(Array[Mask])
  MaskGhost
} derive(Debug, Eq)

///|
pub(all) enum InductiveSign {
  Ind
  Coind
} derive(Debug, Eq)

///|
pub(all) enum PropositionKind {
  Plemma
  Paxiom
  Pgoal
} derive(Debug, Eq)

///|
pub(all) enum Visibility {
  Public
  Private
  Abstract
} derive(Debug, Eq)

///|
pub(all) enum ModuleKind {
  Theory
  Module
} derive(Debug, Eq)

///|
let reference_attribute : Bytes = b"mlw:reference_var"

///|
let break_attribute : Bytes = b"vc:break_me"

///|
let white_box_attribute : Bytes = b"vc:white_box"

///|
let unused_variable_attribute : Bytes = b"W:unused_variable:N"

///|
let proxy_attribute : Bytes = b"mlw:proxy_symbol"

///|
let user_axiom_attribute : Bytes = b"useraxiom"

///|
let function_literal_attribute : Bytes = b"funlit"

///|
let witness_existence_attribute : Bytes = b"expl:witness existence"

///|
let old_label : Bytes = b"'Old"

///|
let return_label : Bytes = b"'Return"

///|
let break_label : Bytes = b"'Break"

///|
let continue_label : Bytes = b"'Continue"

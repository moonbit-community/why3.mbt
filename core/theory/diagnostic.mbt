// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum TheoryErrorKind {
  DuplicateName
  AmbiguousName
  UnboundName
  InvalidQualifiedName
  ContextMismatch
  BuilderSealed
  NoOpenedNamespace
  InvalidTheoryItem
  GoalNotLast
  MissingGoal
  MultipleGoals
} derive(Eq, Debug)

///|
pub(all) struct TheoryDiagnostic {
  kind : TheoryErrorKind
  span : @identity.SourceSpan?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror TheoryError {
  TheoryError(TheoryDiagnostic)
} derive(Eq, Debug)

///|
fn[A] fail_theory(
  kind : TheoryErrorKind,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise TheoryError {
  raise TheoryError({ kind, span, message })
}

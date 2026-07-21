// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// Stable classes for type construction, matching, and elaboration failures.
pub(all) enum TypeErrorKind {
  ArityMismatch
  DuplicateTypeParameter
  UnboundTypeVariable
  ContextMismatch
  SnapshotOriginRequired
  InvalidRange
  InvalidFloat
  TypeMismatch
  OccursCheck
  UnresolvedTypeVariable
  PolymorphicProgramRoutine
  ValueExpected
  FormulaExpected
  FunctionExpected
  PredicateExpected
  InvalidConstantType
  ConstantOutOfRange
  NonRepresentableFloat
  DuplicateBinder
  InvalidTrigger
  UnboundVariable
  DuplicateDeclarationSymbol
  UnknownDependency
  CyclicDefinition
  InvalidDeclaration
  EmptyDeclaration
} derive(Eq, Debug)

///|
/// A type failure paired with its source position when one is available.
pub(all) struct TypeDiagnostic {
  kind : TypeErrorKind
  span : @identity.SourceSpan?
  actual_type : Bytes?
  expected_type : Bytes?
  message : String
} derive(Eq, Debug)

///|
/// The checked error shared by immutable semantic types and delayed types.
pub(all) suberror TypeError {
  TypeError(TypeDiagnostic)
} derive(Eq, Debug)

///|
/// Raises a stable type diagnostic without exposing representation details.
pub fn[A] fail_type(
  kind : TypeErrorKind,
  span : @identity.SourceSpan?,
  message : String,
) -> A raise TypeError {
  raise TypeError({
    kind,
    span,
    actual_type: None,
    expected_type: None,
    message,
  })
}

///|
/// Raises a type diagnostic at an elaboration comparison boundary while
/// retaining the two stable, byte-oriented type renderings.
pub fn[A] fail_type_with_types(
  kind : TypeErrorKind,
  span : @identity.SourceSpan?,
  actual_type : BytesView,
  expected_type : BytesView,
  message : String,
) -> A raise TypeError {
  raise TypeError({
    kind,
    span,
    actual_type: Some(actual_type.to_owned()),
    expected_type: Some(expected_type.to_owned()),
    message,
  })
}

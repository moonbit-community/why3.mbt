// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn match_type_into(
  substitution : TySubstitution,
  pattern : Ty,
  subject : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  match pattern.node {
    VariableNode(variable) =>
      match substitution.get(variable) {
        None => substitution.bind(variable, subject, span)
        Some(previous) =>
          if previous == subject {
            substitution
          } else {
            fail_type(
              TypeMismatch,
              span,
              "type variable matched two different semantic types",
            )
          }
      }
    ApplicationNode(pattern_symbol, pattern_arguments) =>
      match subject.node {
        ApplicationNode(subject_symbol, subject_arguments) => {
          if pattern_symbol != subject_symbol ||
            pattern_arguments.length() != subject_arguments.length() {
            fail_type(TypeMismatch, span, "type constructors do not match")
          }
          let mut result = substitution
          for index, argument in pattern_arguments {
            result = match_type_into(
              result,
              argument,
              subject_arguments[index],
              span,
            )
          }
          result
        }
        VariableNode(_) =>
          fail_type(
            TypeMismatch,
            span,
            "type application cannot match a type variable",
          )
      }
  }
}

///|
/// Computes an immutable substitution that instantiates `pattern` to
/// `subject`, extending the supplied substitution.
pub fn TySubstitution::match_type(
  self : TySubstitution,
  pattern : Ty,
  subject : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  if !self.order.is_empty() &&
    !self.order[0].semantic_id().same_context(pattern.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "initial type substitution belongs to another compilation context",
    )
  }
  if !pattern.context_anchor().same_context(subject.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "type matching combines different compilation contexts",
    )
  }
  match_type_into(self, pattern, subject, span)
}

///|
pub fn type_match(
  pattern : Ty,
  subject : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  TySubstitution::new().match_type(pattern, subject, span)
}

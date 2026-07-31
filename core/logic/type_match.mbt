// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn diagnostic_type_shape(ty : Ty) -> String {
  match ty.node {
    VariableNode(variable) =>
      "'\{variable.name()}#\{variable.semantic_id().local_id()}"
    ApplicationNode(symbol, arguments) => {
      let components = arguments.map(diagnostic_type_shape)
      if components.is_empty() {
        "\{symbol.name()}"
      } else {
        "\{symbol.name()}<\{components.join(",")}>"
      }
    }
  }
}

///|
fn is_logic_inference_type_variable(variable : TyVarSymbol) -> Bool {
  variable
  .origin()
  .attributes()
  .any(attribute => attribute == b"mlw:inference_type_variable")
}

///|
fn match_inference_type(
  substitution : TySubstitution,
  left : Ty,
  right : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  if left == right {
    return substitution
  }
  match (left.node, right.node) {
    (VariableNode(variable), _) if is_logic_inference_type_variable(variable) =>
      match substitution.get(variable) {
        None => substitution.bind(variable, right, span)
        Some(previous) =>
          if previous == left {
            substitution.bind(variable, right, span)
          } else {
            match_inference_type(substitution, previous, right, span)
          }
      }
    (_, VariableNode(variable)) if is_logic_inference_type_variable(variable) =>
      match substitution.get(variable) {
        None => substitution.bind(variable, left, span)
        Some(previous) =>
          if previous == right {
            substitution.bind(variable, left, span)
          } else {
            match_inference_type(substitution, left, previous, span)
          }
      }
    (
      ApplicationNode(left_symbol, left_arguments),
      ApplicationNode(right_symbol, right_arguments),
    ) if left_symbol == right_symbol &&
      left_arguments.length() == right_arguments.length() => {
      let mut result = substitution
      for index, argument in left_arguments {
        result = match_inference_type(
          result,
          argument,
          right_arguments[index],
          span,
        )
      }
      result
    }
    _ =>
      fail_type(
        TypeMismatch,
        span,
        "inferred semantic types do not match: \{diagnostic_type_shape(left)} vs \{diagnostic_type_shape(right)}",
      )
  }
}

///|
/// Reconciles two already-semantic types while treating only MLW inference
/// variables as flexible. Ordinary semantic type variables remain rigid.
pub fn TySubstitution::match_inference_types(
  self : TySubstitution,
  left : Ty,
  right : Ty,
  span : @identity.SourceSpan?,
) -> TySubstitution raise TypeError {
  if !self.order.is_empty() &&
    !self.order[0].semantic_id().same_context(left.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "initial inference substitution belongs to another compilation context",
    )
  }
  if !left.context_anchor().same_context(right.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "inference matching combines different compilation contexts",
    )
  }
  match_inference_type(self, left, right, span)
}

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
          } else if previous
            .free_variables()
            .any(is_logic_inference_type_variable) ||
            subject.free_variables().any(is_logic_inference_type_variable) {
            match_inference_type(substitution, previous, subject, span)
          } else {
            fail_type(
              TypeMismatch,
              span,
              "type variable '\{variable.name()}#\{variable.semantic_id().local_id()} matched \{diagnostic_type_shape(previous)} and \{diagnostic_type_shape(subject)}",
            )
          }
      }
    ApplicationNode(pattern_symbol, pattern_arguments) =>
      match subject.node {
        VariableNode(variable) if is_logic_inference_type_variable(variable) =>
          match_inference_type(substitution, pattern, subject, span)
        VariableNode(variable) =>
          fail_type(
            TypeMismatch,
            span,
            "type constructor \{diagnostic_type_shape(pattern)} cannot match rigid variable '\{variable.name()}#\{variable.semantic_id().local_id()}",
          )
        ApplicationNode(subject_symbol, subject_arguments) => {
          if pattern_symbol != subject_symbol ||
            pattern_arguments.length() != subject_arguments.length() {
            fail_type(
              TypeMismatch,
              span,
              "type constructors do not match: \{diagnostic_type_shape(pattern)} vs \{diagnostic_type_shape(subject)}",
            )
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

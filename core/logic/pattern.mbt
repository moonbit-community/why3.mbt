// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv enum PatternNode {
  WildPattern
  VariablePattern(VSymbol)
  ApplicationPattern(LSymbol, Array[Pattern])
  OrPattern(Pattern, Pattern)
  AsPattern(Pattern, VSymbol)
}

///|
struct Pattern {
  node : PatternNode
  ty : Ty
  bound_variables : Array[VSymbol]
}

///|
pub(all) enum PatternView {
  Pwild(Ty)
  Pvar(VSymbol)
  Papp(LSymbol, ArrayView[Pattern], Ty)
  Por(Pattern, Pattern, Ty)
  Pas(Pattern, VSymbol, Ty)
}

///|
pub fn Pattern::ty(self : Pattern) -> Ty {
  self.ty
}

///|
pub fn Pattern::bound_variables(self : Pattern) -> ArrayView[VSymbol] {
  self.bound_variables[:]
}

///|
pub fn Pattern::view(self : Pattern) -> PatternView {
  match self.node {
    WildPattern => Pwild(self.ty)
    VariablePattern(variable) => Pvar(variable)
    ApplicationPattern(symbol, arguments) => Papp(symbol, arguments[:], self.ty)
    OrPattern(left, right) => Por(left, right, self.ty)
    AsPattern(pattern, variable) => Pas(pattern, variable, self.ty)
  }
}

///|
pub fn Pattern::trusted_wild(ty : Ty) -> Pattern {
  { node: WildPattern, ty, bound_variables: [] }
}

///|
pub fn Pattern::trusted_variable(variable : VSymbol) -> Pattern {
  {
    node: VariablePattern(variable),
    ty: variable.ty,
    bound_variables: [variable],
  }
}

///|
fn merge_pattern_variables(
  patterns : ArrayView[Pattern],
  span : @identity.SourceSpan?,
) -> Array[VSymbol] raise TypeError {
  let variables : Array[VSymbol] = []
  let seen : Map[VSymbol, Unit] = Map([])
  for pattern in patterns {
    for variable in pattern.bound_variables {
      if seen.contains(variable) {
        fail_type(
          DuplicateBinder,
          span,
          "pattern binds the same variable more than once",
        )
      }
      seen[variable] = ()
      variables.push(variable)
    }
  }
  variables
}

///|
pub fn Pattern::trusted_app(
  symbol : LSymbol,
  arguments : ArrayView[Pattern],
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> Pattern raise TypeError {
  guard symbol.role is ConstructorRole(_) else {
    fail_type(
      InvalidDeclaration,
      span,
      "pattern application requires a trusted constructor",
    )
  }
  if arguments.length() != symbol.argument_types.length() {
    fail_type(ArityMismatch, span, "constructor pattern has the wrong arity")
  }
  let mut substitution = TySubstitution::new()
  for index, formal in symbol.argument_types {
    substitution = substitution.match_type(formal, arguments[index].ty, span)
  }
  guard symbol.result_type is Some(formal_result) else {
    fail_type(
      FunctionExpected,
      span,
      "constructor pattern requires a value result",
    )
  }
  substitution = substitution.match_type(formal_result, result_type, span)
  let copied = arguments.to_owned()
  {
    node: ApplicationPattern(symbol, copied),
    ty: result_type,
    bound_variables: merge_pattern_variables(copied, span),
  }
}

///|
fn same_bound_variables(left : Pattern, right : Pattern) -> Bool {
  if left.bound_variables.length() != right.bound_variables.length() {
    return false
  }
  let right_set : Map[VSymbol, Unit] = Map([])
  for variable in right.bound_variables {
    right_set[variable] = ()
  }
  left.bound_variables.all(variable => right_set.contains(variable))
}

///|
pub fn Pattern::trusted_or(
  left : Pattern,
  right : Pattern,
  span : @identity.SourceSpan?,
) -> Pattern raise TypeError {
  if left.ty != right.ty || !same_bound_variables(left, right) {
    fail_type(
      InvalidDeclaration,
      span,
      "or-pattern branches must have the same type and binders",
    )
  }
  {
    node: OrPattern(left, right),
    ty: left.ty,
    bound_variables: left.bound_variables.copy(),
  }
}

///|
pub fn Pattern::trusted_as(
  pattern : Pattern,
  variable : VSymbol,
  span : @identity.SourceSpan?,
) -> Pattern raise TypeError {
  if pattern.ty != variable.ty {
    fail_type(TypeMismatch, span, "as-pattern variable has the wrong type")
  }
  if pattern.bound_variables.contains(variable) {
    fail_type(DuplicateBinder, span, "as-pattern duplicates a binder")
  }
  let variables = pattern.bound_variables.copy()
  variables.push(variable)
  {
    node: AsPattern(pattern, variable),
    ty: pattern.ty,
    bound_variables: variables,
  }
}

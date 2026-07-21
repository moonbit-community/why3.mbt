// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct InlineDefinition {
  parameters : Array[@logic.VSymbol]
  body : @logic.Term
}

///|
fn inline_type_substitution(
  instantiation : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
) -> @logic.TySubstitution raise TransformError {
  let mut substitution = @logic.TySubstitution::new()
  for entry in instantiation {
    substitution = substitution.bind(entry.0, entry.1, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.InlineTrivial,
          "invalid inline type instantiation",
        )
    }
  }
  substitution
}

///|
fn unfold_application(
  context : @identity.CompilationContext,
  definition : InlineDefinition,
  instantiation : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
  arguments : ArrayView[@logic.Term],
) -> @logic.Term raise TransformError {
  if definition.parameters.length() != arguments.length() {
    fail_transform(
      InvariantFailure,
      @identity.InlineTrivial,
      "inline definition application has the wrong arity",
    )
  }
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  for index, parameter in definition.parameters {
    values[parameter] = arguments[index]
  }
  instantiate_term(
    context,
    inline_type_substitution(instantiation),
    values,
    definition.body,
    @identity.InlineTrivial,
  )
}

///|
fn rewrite_inline_term(
  context : @identity.CompilationContext,
  environment : Map[@logic.LSymbol, InlineDefinition],
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.InlineTrivial
  let recurse = fn(child) -> @logic.Term raise TransformError {
    rewrite_inline_term(context, environment, child)
  }
  let mapped = map_plain(term, recurse, stage)
  match mapped.view() {
    Tapp(symbol, instantiation, arguments) =>
      match environment.get(symbol) {
        None => mapped
        Some(definition) =>
          copy_term_decoration(
            mapped,
            unfold_application(context, definition, instantiation, arguments),
          )
      }
    _ => mapped
  }
}

///|
fn rebuild_logic_definition(
  context : @identity.CompilationContext,
  definition : @logic.LogicDefinition,
  body : @logic.Term,
) -> @logic.LogicDefinition raise TransformError {
  let view = definition.view()
  match view.symbol.view().origin.kind().view() {
    SnapshotKind =>
      @logic.LogicDefinition::trusted_recursive(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.InlineTrivial,
            "cannot rebuild trusted logic definition",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.LogicDefinition::new(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.InlineTrivial,
            "cannot rebuild logic definition",
          )
      }
  }
}

///|
fn rewrite_inline_declaration(
  context : @identity.CompilationContext,
  environment : Map[@logic.LSymbol, InlineDefinition],
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  let rewrite = fn(term) -> @logic.Term raise TransformError {
    rewrite_inline_term(context, environment, term)
  }
  match declaration.view() {
    Dtype(_) | Ddata(_) | Dparam(_) => declaration
    Dlogic(definitions) => {
      let mapped = [
        for definition in definitions => {
          rebuild_logic_definition(
            context,
            definition,
            rewrite(definition.view().body),
          )
        }
      ]
      match declaration.origin().kind().view() {
        SnapshotKind =>
          @logic.Decl::trusted_logic(
            context,
            declaration.origin(),
            mapped,
            None,
          ) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                @identity.InlineTrivial,
                "cannot rebuild trusted logic declaration",
              )
          }
        UserKind | GeneratedKind(_) =>
          @logic.Decl::logic(context, declaration.origin(), mapped, None) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                @identity.InlineTrivial,
                "cannot rebuild logic declaration",
              )
          }
      }
    }
    Dind(declarations) => {
      let mapped : Array[@logic.InductiveDeclaration] = []
      for inductive in declarations {
        let view = inductive.view()
        let cases : Array[@logic.InductiveCase] = []
        for case_ in view.cases {
          let case_view = case_.view()
          cases.push(
            @logic.InductiveCase::trusted_new(
              context,
              case_view.proposition,
              rewrite(case_view.formula),
              None,
            ) catch {
              _ =>
                fail_transform(
                  InvariantFailure,
                  @identity.InlineTrivial,
                  "cannot rebuild inductive case",
                )
            },
          )
        }
        mapped.push(
          @logic.InductiveDeclaration::trusted_new(view.predicate, cases, None) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                @identity.InlineTrivial,
                "cannot rebuild inductive declaration",
              )
          },
        )
      }
      @logic.Decl::trusted_inductive(
        context,
        declaration.origin(),
        mapped,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.InlineTrivial,
            "cannot rebuild inductive group",
          )
      }
    }
    Dprop(kind, proposition, formula) =>
      @logic.Decl::proposition(
        context,
        declaration.origin(),
        kind,
        proposition,
        rewrite(formula),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.InlineTrivial,
            "cannot rebuild proposition",
          )
      }
  }
}

///|
fn trivial_arguments(arguments : ArrayView[@logic.Term]) -> Bool {
  let variables : Map[@logic.VSymbol, Unit] = Map([])
  for argument in arguments {
    match argument.view() {
      Tvar(variable) => {
        if variables.contains(variable) {
          return false
        }
        variables[variable] = ()
      }
      Teps(_, _) => return false
      _ => if !argument.free_variables().is_empty() { return false }
    }
  }
  true
}

///|
fn is_trivial_definition(body : @logic.Term) -> Bool {
  if body.attributes().any(attribute => attribute == b"inline:trivial") {
    return true
  }
  match body.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => true
    Tapp(_, _, arguments) => trivial_arguments(arguments)
    _ => false
  }
}

///|
fn inline_forbidden_symbols(task : @theory.Task) -> Map[@logic.LSymbol, Unit] {
  let result : Map[@logic.LSymbol, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"inline:no", arguments: [MetaLogicSymbol(symbol)] } {
      result[symbol] = ()
    }
  }
  result
}

///|
pub fn inline_trivial(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.InlineTrivial
  require_task_context(context, task, stage)
  let forbidden = inline_forbidden_symbols(task)
  let environment : Map[@logic.LSymbol, InlineDefinition] = Map([])
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) => {
        let mapped = rewrite_inline_declaration(
          context, environment, declaration,
        )
        match mapped.view() {
          Dlogic(definitions) if definitions.length() == 1 => {
            let definition = definitions[0].view()
            let body = definition.body.add_attributes(
              definition.symbol.view().origin.attributes(),
            )
            if !definition.body.contains_logic_symbol(definition.symbol) &&
              !forbidden.contains(definition.symbol) &&
              is_trivial_definition(body) {
              environment[definition.symbol] = {
                parameters: definition.parameters.to_owned(),
                body,
              }
            } else {
              result.push(TheoryDecl(mapped))
            }
          }
          _ => result.push(TheoryDecl(mapped))
        }
      }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => result.push(item)
    }
  }
  checked_task(task.context_anchor(), result, stage)
}

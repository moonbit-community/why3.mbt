// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct Environment {
  context : @identity.CompilationContext
  source_environment : @env.CoreEnvironment
  anchor : @identity.SemanticId
  typed_libraries : @env.LibraryCache[TypedLibrary]
  builtins : @env.BuiltinRegistry[TypedLibrary]
  theories : Map[@theory.TheoryKey, @theory.Theory]
  modules : Map[@theory.TheoryKey, @mlw.Pmodule]
  theory_aliases : Map[@theory.TheoryKey, @theory.TheoryKey]
  module_aliases : Map[@theory.TheoryKey, @theory.TheoryKey]
  hidden_theories : Map[@theory.TheoryKey, Unit]
  hidden_modules : Map[@theory.TheoryKey, Unit]
  type_variables : Array[(Bytes, @logic.TyVarSymbol)]
  tuple_modules : Map[Int, @mlw.Pmodule]
  mut reference_module : @mlw.Pmodule?
  mut high_order_module : @mlw.Pmodule?
  mut well_founded_module : @mlw.Pmodule?
}

///|
pub(all) struct EnvironmentView {
  theory_keys : Array[@theory.TheoryKey]
  module_keys : Array[@theory.TheoryKey]
  visible_theory_aliases : Array[(@theory.TheoryKey, @theory.TheoryKey)]
  visible_module_aliases : Array[(@theory.TheoryKey, @theory.TheoryKey)]
}

///|
pub fn Environment::new(context : @identity.CompilationContext) -> Environment {
  Environment::from_core(@env.CoreEnvironment::empty(context))
}

///|
/// Creates an independently-owned typed environment over an all-target source
/// provider.
pub fn Environment::with_source(
  provider : @env.SourceProvider,
) -> Environment raise {
  let environment = Environment::from_core(@env.CoreEnvironment::new(provider))
  environment.install_language_builtins()
  environment
}

///|
/// Creates a typed source environment in an existing compilation context.
/// This is primarily useful to compose an embedded provider with a pipeline
/// that owns the context used for every resulting semantic object.
pub fn Environment::with_source_in_context(
  context : @identity.CompilationContext,
  provider : @env.SourceProvider,
) -> Environment raise {
  let environment = Environment::from_core(
    @env.CoreEnvironment::with_context(context, provider),
  )
  environment.install_language_builtins()
  environment
}

///|
pub fn Environment::from_core(
  source_environment : @env.CoreEnvironment,
) -> Environment {
  let context = source_environment.compilation_context()
  {
    context,
    source_environment,
    anchor: context.fresh_id(),
    typed_libraries: @env.LibraryCache::new(),
    builtins: @env.BuiltinRegistry::new(),
    theories: Map([]),
    modules: Map([]),
    theory_aliases: Map([]),
    module_aliases: Map([]),
    hidden_theories: Map([]),
    hidden_modules: Map([]),
    type_variables: [],
    tuple_modules: Map([]),
    reference_module: None,
    high_order_module: None,
    well_founded_module: None,
  }
}

///|
pub fn Environment::compilation_context(
  self : Environment,
) -> @identity.CompilationContext {
  self.context
}

///|
pub fn Environment::source_environment(
  self : Environment,
) -> @env.CoreEnvironment {
  self.source_environment
}

///|
pub fn Environment::context_anchor(self : Environment) -> @identity.SemanticId {
  self.anchor
}

///|
fn Environment::index_type_variable(
  self : Environment,
  variable : @logic.TyVarSymbol,
) -> Unit {
  for entry in self.type_variables {
    if entry.0[:] == variable.name() {
      return
    }
  }
  self.type_variables.push((variable.name().to_owned(), variable))
}

///|
fn source_type_variable_owner(origin : @identity.Origin) -> Bool {
  match origin.kind().view() {
    UserKind => origin.source_span() is Some(_)
    GeneratedKind(_) => false
  }
}

///|
fn Environment::index_dependency(
  self : Environment,
  dependency : @logic.DeclDependency,
) -> Unit {
  match dependency {
    TypeDependency(symbol) => {
      let view = symbol.view()
      if source_type_variable_owner(view.origin) {
        for parameter in view.parameters {
          self.index_type_variable(parameter)
        }
      }
    }
    LogicDependency(symbol) => {
      let view = symbol.view()
      if source_type_variable_owner(view.origin) {
        for parameter in view.type_parameters {
          self.index_type_variable(parameter)
        }
      }
    }
    PropositionDependency(_) => ()
  }
}

///|
fn Environment::index_theory_type_variables(
  self : Environment,
  theory : @theory.Theory,
) -> Unit {
  for item in theory.view().items {
    match item {
      TheoryDecl(declaration) => {
        for dependency in declaration.dependencies() {
          self.index_dependency(dependency)
        }
        for introduced in declaration.introduced_symbols() {
          self.index_dependency(introduced)
        }
      }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => ()
    }
  }
}

///|
/// Why3 interns source type-variable spellings globally, but its synthetic
/// builtins and clone machinery allocate distinct variables with the same
/// spelling. Reuse only variables that carry a real source location.
pub fn Environment::intern_type_variable(
  self : Environment,
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> @logic.TyVarSymbol raise EnvironmentError {
  if !context.contains(self.anchor) {
    fail_environment(
      EnvironmentContextMismatch,
      span,
      "type-variable interner belongs to another compilation context",
    )
  }
  for entry in self.type_variables {
    if entry.0[:] == name {
      return entry.1
    }
  }
  let variable = @logic.TyVarSymbol::new(context, name, origin)
  self.type_variables.push((name.to_owned(), variable))
  variable
}

///|
fn Environment::require_context(
  self : Environment,
  id : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  if !self.anchor.same_context(id) {
    fail_environment(
      EnvironmentContextMismatch,
      span,
      "environment and semantic object belong to different contexts",
    )
  }
}

///|
pub fn Environment::register_theory(
  self : Environment,
  theory : @theory.Theory,
  user_visible : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  self.require_context(theory.context_anchor(), span)
  let key = theory.key()
  if self.theories.contains(key) {
    fail_environment(DuplicateTheory, span, "theory key is already registered")
  }
  self.index_theory_type_variables(theory)
  self.theories[key] = theory
  if user_visible {
    self.theory_aliases[key] = key
  } else {
    self.hidden_theories[key] = ()
  }
}

///|
pub fn Environment::register_module(
  self : Environment,
  pmodule : @mlw.Pmodule,
  user_visible : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  self.require_context(pmodule.context_anchor(), span)
  let key = pmodule.key()
  if self.modules.contains(key) {
    fail_environment(DuplicateModule, span, "module key is already registered")
  }
  self.modules[key] = pmodule
  if user_visible {
    self.module_aliases[key] = key
  } else {
    self.hidden_modules[key] = ()
  }
}

///|
pub fn Environment::add_theory_alias(
  self : Environment,
  alias_key : @theory.TheoryKey,
  target : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  if !self.theories.contains(target) {
    fail_environment(
      ResolveError,
      span,
      "theory alias target is not registered",
    )
  }
  if self.theory_aliases.contains(alias_key) {
    fail_environment(
      DuplicateTheory,
      span,
      "theory alias is already registered",
    )
  }
  self.theory_aliases[alias_key] = target
  self.hidden_theories.remove(alias_key)
}

///|
pub fn Environment::add_module_alias(
  self : Environment,
  alias_key : @theory.TheoryKey,
  target : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> Unit raise EnvironmentError {
  if !self.modules.contains(target) {
    fail_environment(
      ResolveError,
      span,
      "module alias target is not registered",
    )
  }
  if self.module_aliases.contains(alias_key) {
    fail_environment(
      DuplicateModule,
      span,
      "module alias is already registered",
    )
  }
  self.module_aliases[alias_key] = target
  self.hidden_modules.remove(alias_key)
}

///|
pub fn Environment::resolve_theory(
  self : Environment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @theory.Theory raise EnvironmentError {
  match self.theory_aliases.get(key) {
    Some(target) => self.theories[target]
    None =>
      if self.theories.contains(key) || self.hidden_theories.contains(key) {
        fail_environment(
          DriverOnlyTheory,
          span,
          "theory is present only for the private driver closure",
        )
      } else {
        fail_environment(ResolveError, span, "unknown theory")
      }
  }
}

///|
/// Reports whether a key is known only inside the private driver closure.
pub fn Environment::is_driver_only_theory(
  self : Environment,
  key : @theory.TheoryKey,
) -> Bool {
  (self.theories.contains(key) || self.hidden_theories.contains(key)) &&
  !self.theory_aliases.contains(key)
}

///|
pub fn Environment::resolve_module(
  self : Environment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule raise EnvironmentError {
  match self.module_aliases.get(key) {
    Some(target) => self.modules[target]
    None =>
      if self.modules.contains(key) || self.hidden_modules.contains(key) {
        fail_environment(
          DriverOnlyTheory,
          span,
          "module is present only for the private driver closure",
        )
      } else {
        fail_environment(ResolveError, span, "unknown module")
      }
  }
}

///|
pub fn Environment::use_theory(
  self : Environment,
  builder : @theory.TheoryBuilder,
  key : @theory.TheoryKey,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let theory = self.resolve_theory(key, span)
  builder.add_use(theory, import_, span)
}

///|
pub fn Environment::use_module(
  self : Environment,
  builder : @mlw.PmoduleBuilder,
  key : @theory.TheoryKey,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let pmodule = self.resolve_module(key, span)
  builder.add_use(pmodule, import_, span)
}

///|
pub fn Environment::view(self : Environment) -> EnvironmentView {
  let theory_keys = self.theories.keys().to_array()
  theory_keys.sort_by((left, right) => left.lexical_compare(right))
  let module_keys = self.modules.keys().to_array()
  module_keys.sort_by((left, right) => left.lexical_compare(right))
  let theory_aliases = self.theory_aliases.to_array()
  theory_aliases.sort_by((left, right) => left.0.lexical_compare(right.0))
  let module_aliases = self.module_aliases.to_array()
  module_aliases.sort_by((left, right) => left.0.lexical_compare(right.0))
  {
    theory_keys,
    module_keys,
    visible_theory_aliases: theory_aliases,
    visible_module_aliases: module_aliases,
  }
}

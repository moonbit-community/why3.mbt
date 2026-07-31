// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// Symbol correspondence obtained by checking an implementation namespace
/// against the declarations exposed by a module interface.
struct ProgramInterfaceMatch {
  interface_module : Pmodule
  implementation_module : Pmodule
  pure_type_instantiations : Array[(@logic.TypeSymbol, @logic.TypeSymbol)]
  program_type_instantiations : Array[(@logic.TypeSymbol, ProgramTypeSymbol)]
  logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)]
  program_variable_instantiations : Array[(PVariable, PVariable)]
  routine_instantiations : Array[(RoutineSymbol, RoutineSymbol)]
}

///|
pub(all) struct ProgramInterfaceMatchView {
  interface_module : Pmodule
  implementation_module : Pmodule
  pure_type_instantiations : ArrayView[(@logic.TypeSymbol, @logic.TypeSymbol)]
  program_type_instantiations : ArrayView[
    (@logic.TypeSymbol, ProgramTypeSymbol),
  ]
  logic_instantiations : ArrayView[(@logic.LSymbol, @logic.LSymbol)]
  program_variable_instantiations : ArrayView[(PVariable, PVariable)]
  routine_instantiations : ArrayView[(RoutineSymbol, RoutineSymbol)]
}

///|
pub fn ProgramInterfaceMatch::view(
  self : ProgramInterfaceMatch,
) -> ProgramInterfaceMatchView {
  {
    interface_module: self.interface_module,
    implementation_module: self.implementation_module,
    pure_type_instantiations: self.pure_type_instantiations[:],
    program_type_instantiations: self.program_type_instantiations[:],
    logic_instantiations: self.logic_instantiations[:],
    program_variable_instantiations: self.program_variable_instantiations[:],
    routine_instantiations: self.routine_instantiations[:],
  }
}

///|
priv struct InterfaceMatchCollector {
  implementation_module : Pmodule
  pure_type_instantiations : Array[(@logic.TypeSymbol, @logic.TypeSymbol)]
  program_type_instantiations : Array[(@logic.TypeSymbol, ProgramTypeSymbol)]
  logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)]
  program_variable_instantiations : Array[(PVariable, PVariable)]
  routine_instantiations : Array[(RoutineSymbol, RoutineSymbol)]
}

///|
fn append_interface_path(
  path : ArrayView[Bytes],
  name : BytesView,
) -> Array[Bytes] {
  let result = path.to_owned()
  result.push(name.to_owned())
  result
}

///|
fn InterfaceMatchCollector::find_program_type(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  self.implementation_module.export_namespace().find_type(path, span) catch {
    _ =>
      fail_mlw(
        ProgramInterfaceSymbolNotFound,
        span,
        "interface type is absent from its implementation",
      )
  }
}

///|
fn InterfaceMatchCollector::find_routine(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  interface_routine : RoutineSymbol,
  span : @identity.SourceSpan?,
) -> RoutineSymbol? raise MlwError {
  match
    self.implementation_module.export_namespace().find_routine_option(path) {
    Some(routine) => Some(routine)
    None =>
      if interface_routine.view().name.has_suffix(b"'lemma") {
        None
      } else {
        fail_mlw(
          ProgramInterfaceSymbolNotFound,
          span,
          "interface routine is absent from its implementation",
        )
      }
  }
}

///|
fn InterfaceMatchCollector::find_variable(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> PVariable raise MlwError {
  self.implementation_module.export_namespace().find_variable(path, span) catch {
    _ =>
      fail_mlw(
        ProgramInterfaceSymbolNotFound,
        span,
        "interface program variable is absent from its implementation",
      )
  }
}

///|
fn InterfaceMatchCollector::find_pure_type(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.TypeSymbol raise MlwError {
  self.implementation_module
  .pure_theory()
  .export_namespace()
  .find_type(path, span) catch {
    _ =>
      fail_mlw(
        ProgramInterfaceSymbolNotFound,
        span,
        "interface logical type is absent from its implementation",
      )
  }
}

///|
fn InterfaceMatchCollector::find_logic(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.LSymbol raise MlwError {
  self.implementation_module
  .pure_theory()
  .export_namespace()
  .find_logic(path, span) catch {
    _ =>
      fail_mlw(
        ProgramInterfaceSymbolNotFound,
        span,
        "interface logical symbol is absent from its implementation",
      )
  }
}

///|
fn InterfaceMatchCollector::add_pure_declaration(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  match declaration.view() {
    Dtype(symbols) =>
      for symbol in symbols {
        self.pure_type_instantiations.push(
          (
            symbol,
            self.find_pure_type(
              append_interface_path(path, symbol.name()),
              span,
            ),
          ),
        )
      }
    Dparam(symbol) =>
      self.logic_instantiations.push(
        (
          symbol,
          self.find_logic(append_interface_path(path, symbol.view().name), span),
        ),
      )
    Dlogic(_) | Dprop(_, _, _) => ()
    Ddata(_) | Dind(_, _) =>
      fail_mlw(
        UnsupportedProgramInterfaceUnit,
        span,
        "unsupported pure declaration in module interface",
      )
  }
}

///|
fn InterfaceMatchCollector::add_program_declaration(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  declaration : ProgramDeclaration,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  match declaration {
    PDtype(declarations, _, _) =>
      for declaration in declarations {
        let interface_symbol = declaration.view().symbol
        let name = interface_symbol.view().logic_type.name()
        let implementation_symbol = self.find_program_type(
          append_interface_path(path, name),
          span,
        )
        self.program_type_instantiations.push(
          (interface_symbol.view().logic_type, implementation_symbol),
        )
      }
    PDlet(interface_routine, _, _, _) => {
      let symbol_path = append_interface_path(
        path,
        interface_routine.view().name,
      )
      match self.find_routine(symbol_path, interface_routine, span) {
        Some(implementation_routine) =>
          self.routine_instantiations.push(
            (interface_routine, implementation_routine),
          )
        None => ()
      }
    }
    PDvar(interface_variable, _, _, _) => {
      let name = interface_variable.view().name.view().name
      self.program_variable_instantiations.push(
        (
          interface_variable,
          self.find_variable(append_interface_path(path, name), span),
        ),
      )
    }
    PDrec(definitions, _, _) =>
      for definition in definitions {
        let interface_routine = definition.view().symbol
        let symbol_path = append_interface_path(
          path,
          interface_routine.view().name,
        )
        match self.find_routine(symbol_path, interface_routine, span) {
          Some(implementation_routine) =>
            self.routine_instantiations.push(
              (interface_routine, implementation_routine),
            )
          None => ()
        }
      }
    PDpure(declarations, _) =>
      for declaration in declarations {
        self.add_pure_declaration(path, declaration, span)
      }
    PDexn(_, _, _) =>
      fail_mlw(
        UnsupportedProgramInterfaceUnit,
        span,
        "exceptions are not valid interface implementation units",
      )
  }
}

///|
fn InterfaceMatchCollector::add_items(
  self : InterfaceMatchCollector,
  path : ArrayView[Bytes],
  items : ArrayView[ModuleItem],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for item in items {
    match item {
      Udecl(declaration) =>
        self.add_program_declaration(path, declaration, span)
      Uuse(_) | Umeta(_) | Uclone(_) => ()
      Uscope(_, [Uuse(_)]) => ()
      Uscope(name, nested) =>
        self.add_items(append_interface_path(path, name), nested, span)
    }
  }
}

///|
/// Implements the symbol-discovery phase of Why3's `intf_mod_inst`.
pub fn Pmodule::match_interface(
  self : Pmodule,
  interface_module : Pmodule,
  span : @identity.SourceSpan?,
) -> ProgramInterfaceMatch raise MlwError {
  require_mlw_context(self.anchor, interface_module.anchor, span)
  let collector = InterfaceMatchCollector::{
    implementation_module: self,
    pure_type_instantiations: [],
    program_type_instantiations: [],
    logic_instantiations: [],
    program_variable_instantiations: [],
    routine_instantiations: [],
  }
  collector.add_items([], interface_module.view().items, span)
  {
    interface_module,
    implementation_module: self,
    pure_type_instantiations: collector.pure_type_instantiations,
    program_type_instantiations: collector.program_type_instantiations,
    logic_instantiations: collector.logic_instantiations,
    program_variable_instantiations: collector.program_variable_instantiations,
    routine_instantiations: collector.routine_instantiations,
  }
}

///|
pub fn ProgramInterfaceMatch::pure_instantiation(
  self : ProgramInterfaceMatch,
  default_proposition_kind? : @logic.PropositionKind = Plemma,
  span? : @identity.SourceSpan? = None,
) -> @theory.TheoryInstantiation raise {
  let type_symbols = self.pure_type_instantiations.copy()
  for entry in self.program_type_instantiations {
    let replacement = entry.1.view().logic_type
    if !type_symbols.any(existing => existing.0 == entry.0) {
      type_symbols.push((entry.0, replacement))
    }
  }
  @theory.TheoryInstantiation::new(
    [],
    type_symbols,
    self.logic_instantiations,
    [],
    default_proposition_kind,
    span,
  )
}

///|
pub fn ProgramInterfaceMatch::clone_witness(
  self : ProgramInterfaceMatch,
  context_anchor : @identity.SemanticId,
  default_proposition_kind? : @logic.PropositionKind = Plemma,
  span? : @identity.SourceSpan? = None,
) -> ProgramCloneWitness raise MlwError {
  ProgramCloneWitness::trusted_new(
    context_anchor,
    self.interface_module.key(),
    [],
    self.program_type_instantiations,
    self.logic_instantiations,
    [],
    [],
    [
      for entry in self.program_variable_instantiations => {
        (entry.0.view().pure_symbol, entry.1)
      }
    ],
    self.routine_instantiations,
    [],
    default_proposition_kind,
    span,
  )
}

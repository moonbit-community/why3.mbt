// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// The complete correspondence produced by cloning a theory. `sm_ty` contains
/// abstract type constructors instantiated by arbitrary types; `sm_ts`,
/// `sm_ls`, and `sm_pr` contain constructor/symbol correspondences, including
/// freshly cloned symbols.
struct SymbolMap {
  sm_ty : Array[(@logic.TypeSymbol, @logic.Ty)]
  sm_ts : Array[(@logic.TypeSymbol, @logic.TypeSymbol)]
  sm_ls : Array[(@logic.LSymbol, @logic.LSymbol)]
  sm_pr : Array[(@logic.PrSymbol, @logic.PrSymbol)]
  // Absolute target-theory item positions for every boundary in the cloned
  // source theory. This operational map is intentionally absent from
  // `SymbolMapView`, whose canonical symbol correspondence stays unchanged.
  item_boundaries : Array[Int]
}

///|
pub(all) struct SymbolMapView {
  sm_ty : ArrayView[(@logic.TypeSymbol, @logic.Ty)]
  sm_ts : ArrayView[(@logic.TypeSymbol, @logic.TypeSymbol)]
  sm_ls : ArrayView[(@logic.LSymbol, @logic.LSymbol)]
  sm_pr : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)]
}

///|
pub fn SymbolMap::empty() -> SymbolMap {
  { sm_ty: [], sm_ts: [], sm_ls: [], sm_pr: [], item_boundaries: [] }
}

///|
pub fn SymbolMap::view(self : SymbolMap) -> SymbolMapView {
  {
    sm_ty: self.sm_ty[:],
    sm_ts: self.sm_ts[:],
    sm_ls: self.sm_ls[:],
    sm_pr: self.sm_pr[:],
  }
}

///|
/// Returns the target-theory position corresponding to a boundary between
/// source theory items during the clone that produced this symbol map.
pub fn SymbolMap::cloned_item_boundary(
  self : SymbolMap,
  source_boundary : Int,
) -> Int? {
  if source_boundary < 0 || source_boundary >= self.item_boundaries.length() {
    None
  } else {
    Some(self.item_boundaries[source_boundary])
  }
}

///|
pub fn SymbolMap::find_type(
  self : SymbolMap,
  symbol : @logic.TypeSymbol,
) -> @logic.Ty? {
  for entry in self.sm_ty {
    if entry.0 == symbol {
      return Some(entry.1)
    }
  }
  None
}

///|
pub fn SymbolMap::find_type_symbol(
  self : SymbolMap,
  symbol : @logic.TypeSymbol,
) -> @logic.TypeSymbol? {
  for entry in self.sm_ts {
    if entry.0 == symbol {
      return Some(entry.1)
    }
  }
  None
}

///|
pub fn SymbolMap::find_logic_symbol(
  self : SymbolMap,
  symbol : @logic.LSymbol,
) -> @logic.LSymbol? {
  for entry in self.sm_ls {
    if entry.0 == symbol {
      return Some(entry.1)
    }
  }
  None
}

///|
pub fn SymbolMap::find_proposition(
  self : SymbolMap,
  symbol : @logic.PrSymbol,
) -> @logic.PrSymbol? {
  for entry in self.sm_pr {
    if entry.0 == symbol {
      return Some(entry.1)
    }
  }
  None
}

///|
priv struct SymbolMapTranslation {
  context : @identity.CompilationContext
  symbols : SymbolMap
}

///|
fn SymbolMapTranslation::ty(
  self : SymbolMapTranslation,
  source : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  self.symbols.translate_type_only(source, span)
}

///|
fn SymbolMap::translate_type_only(
  self : SymbolMap,
  source : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  match source.view() {
    TyVar(_) => source
    TyApp(symbol, arguments) => {
      let translated = arguments.map(argument => {
        self.translate_type_only(argument, span)
      })
      match self.find_type_symbol(symbol) {
        Some(replacement) => @logic.Ty::app(replacement, translated, span)
        None =>
          match self.find_type(symbol) {
            Some(replacement) => {
              let parameters = symbol.view().parameters
              if parameters.length() != translated.length() {
                fail_theory(
                  CloneTypeArityMismatch,
                  span,
                  "cloned type constructor has the wrong arity",
                )
              }
              let mut substitution = @logic.TySubstitution::new()
              for index, parameter in parameters {
                substitution = substitution.bind(
                  parameter,
                  translated[index],
                  span,
                )
              }
              substitution.apply(replacement, span)
            }
            None => @logic.Ty::app(symbol, translated, span)
          }
      }
    }
  }
}

///|
fn SymbolMapTranslation::variable(
  self : SymbolMapTranslation,
  source : @logic.VSymbol,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  let view = source.view()
  let translated_type = self.ty(view.ty, span)
  if translated_type == view.ty {
    source
  } else {
    @logic.VSymbol::new(
      self.context,
      view.name,
      view.origin,
      translated_type,
      span,
    )
  }
}

///|
fn SymbolMapTranslation::pattern(
  self : SymbolMapTranslation,
  source : @logic.Pattern,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  match source.view() {
    Pwild(ty) => @logic.Pattern::wild(self.ty(ty, span))
    Pvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Pattern::variable(replacement)
        None =>
          fail_theory(
            MissingCloneSymbol,
            span,
            "translated pattern variable has no correspondence",
          )
      }
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        match self.symbols.find_logic_symbol(symbol) {
          Some(replacement) => replacement
          None => symbol
        },
        arguments.map(argument => self.pattern(argument, variables, span)),
        self.ty(ty, span),
        span,
      )
    Por(left, right, _) =>
      @logic.Pattern::or(
        self.pattern(left, variables, span),
        self.pattern(right, variables, span),
        span,
      )
    Pas(inner, variable, _) =>
      match variables.get(variable) {
        Some(replacement) =>
          @logic.Pattern::as_pattern(
            self.pattern(inner, variables, span),
            replacement,
            span,
          )
        None =>
          fail_theory(
            MissingCloneSymbol,
            span,
            "translated as-pattern variable has no correspondence",
          )
      }
  }
}

///|
fn clone_pattern_bound_variables(
  pattern : @logic.Pattern,
) -> Array[@logic.VSymbol] {
  let variables = pattern.bound_variables().to_owned()
  variables.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  variables
}

///|
fn SymbolMapTranslation::term(
  self : SymbolMapTranslation,
  source : @logic.Term,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let translated = match source.view() {
    Tvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Term::variable(replacement)
        None => {
          let replacement = self.variable(variable, span)
          variables[variable] = replacement
          @logic.Term::variable(replacement)
        }
      }
    Tconst(constant) => {
      guard source.ty() is Some(ty) else {
        abort("validated constant term lost its value type")
      }
      @logic.Term::constant(constant, self.ty(ty, span), span)
    }
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        match self.symbols.find_logic_symbol(symbol) {
          Some(replacement) => replacement
          None => symbol
        },
        arguments.map(argument => self.term(argument, variables, span)),
        match source.ty() {
          Some(ty) => Some(self.ty(ty, span))
          None => None
        },
        span,
      )
    Tif(condition, consequent, alternative) =>
      @logic.Term::if_then_else(
        self.term(condition, variables, span),
        self.term(consequent, variables, span),
        self.term(alternative, variables, span),
        span,
      )
    Tlet(variable, value, body) => {
      let replacement = self.variable(variable, span)
      let nested = variables.copy()
      nested[variable] = replacement
      @logic.Term::let_in(
        replacement,
        self.term(value, variables, span),
        self.term(body, nested, span),
        span,
      )
    }
    Tcase(scrutinee, branches) => {
      let translated_branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        let nested = variables.copy()
        for variable in clone_pattern_bound_variables(view.pattern) {
          nested[variable] = self.variable(variable, span)
        }
        translated_branches.push(
          (
            self.pattern(view.pattern, nested, span),
            self.term(view.body, nested, span),
          ),
        )
      }
      @logic.Term::case(
        self.term(scrutinee, variables, span),
        translated_branches,
        span,
      )
    }
    Teps(variable, body) => {
      let replacement = self.variable(variable, span)
      let nested = variables.copy()
      nested[variable] = replacement
      @logic.Term::epsilon(replacement, self.term(body, nested, span), span)
    }
    Tquant(quantifier, binders, triggers, body) => {
      let nested = variables.copy()
      let translated_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let replacement = self.variable(binder, span)
        translated_binders.push(replacement)
        nested[binder] = replacement
      }
      @logic.Term::quantify(
        quantifier,
        translated_binders,
        triggers.map(group => {
          group.map(trigger => self.term(trigger, nested, span))
        }),
        self.term(body, nested, span),
        span,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(
        operator,
        self.term(left, variables, span),
        self.term(right, variables, span),
        span,
      )
    Tnot(inner) => @logic.Term::not(self.term(inner, variables, span), span)
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  let translated = match source.origin() {
    Some(origin) => translated.decorate(origin, [])
    None => translated
  }
  translated.source_decorate(source.source_span(), source.attributes())
}

///|
pub fn SymbolMap::translate_type(
  self : SymbolMap,
  context : @identity.CompilationContext,
  source : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  if !context.contains(source.context_anchor()) {
    fail_theory(
      ContextMismatch,
      span,
      "translated type belongs to another compilation context",
    )
  }
  self.translate_type_only(source, span)
}

///|
pub fn SymbolMap::translate_term(
  self : SymbolMap,
  context : @identity.CompilationContext,
  source : @logic.Term,
  variable_instantiations : ArrayView[(@logic.VSymbol, @logic.VSymbol)],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let variables : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
  for entry in variable_instantiations {
    variables[entry.0] = entry.1
  }
  SymbolMapTranslation::{ context, symbols: self }.term(source, variables, span)
}

///|
/// Translates a pure pattern with an explicit correspondence for its bound
/// variables. This is the pattern counterpart of `translate_term`.
pub fn SymbolMap::translate_pattern(
  self : SymbolMap,
  context : @identity.CompilationContext,
  source : @logic.Pattern,
  variable_instantiations : ArrayView[(@logic.VSymbol, @logic.VSymbol)],
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  let variables : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
  for entry in variable_instantiations {
    variables[entry.0] = entry.1
  }
  SymbolMapTranslation::{ context, symbols: self }.pattern(
    source, variables, span,
  )
}

///|
pub fn CloneWitness::symbol_map(self : CloneWitness) -> SymbolMap {
  let view = self.view()
  let sm_ty : Array[(@logic.TypeSymbol, @logic.Ty)] = []
  let sm_ts : Array[(@logic.TypeSymbol, @logic.TypeSymbol)] = []
  for instantiation in view.type_instantiations {
    match instantiation {
      CloneType(source, target) => sm_ty.push((source, target))
      CloneTypeSymbol(source, target) => sm_ts.push((source, target))
    }
  }
  {
    sm_ty,
    sm_ts,
    sm_ls: view.logic_instantiations.to_owned(),
    sm_pr: view.proposition_instantiations.to_owned(),
    item_boundaries: [],
  }
}

///|
/// Rewrites a driver/theory meta through an already completed clone. Symbols
/// local to the cloned theory must have a witness correspondence; imported
/// symbols are preserved, matching Why3's `Theory.clone_meta`.
pub fn Meta::clone_through(
  self : Meta,
  source : Theory,
  witness : CloneWitness,
  span : @identity.SourceSpan?,
) -> Meta? raise TheoryError {
  if witness.view().source != source.key() {
    fail_theory(
      InvalidTheoryItem,
      span,
      "meta clone witness references a different source theory",
    )
  }
  if !source.context_anchor().same_context(witness.context_anchor()) {
    fail_theory(
      ContextMismatch,
      span,
      "meta clone source and witness belong to different contexts",
    )
  }
  let symbols = witness.symbol_map()
  let arguments : Array[MetaArgument] = []
  for argument in self.arguments {
    match argument {
      MetaType(ty) =>
        arguments.push(
          MetaType(
            symbols.translate_type_only(ty, span) catch {
              _ =>
                fail_theory(
                  CloneLogicTypeMismatch,
                  span,
                  "cannot translate a cloned meta type",
                )
            },
          ),
        )
      MetaTypeSymbol(symbol) =>
        if source.is_local_id(symbol.semantic_id()) {
          match symbols.find_type_symbol(symbol) {
            Some(replacement) => arguments.push(MetaTypeSymbol(replacement))
            None => return None
          }
        } else {
          arguments.push(argument)
        }
      MetaLogicSymbol(symbol) =>
        if source.is_local_id(symbol.semantic_id()) {
          match symbols.find_logic_symbol(symbol) {
            Some(replacement) => arguments.push(MetaLogicSymbol(replacement))
            None => return None
          }
        } else {
          arguments.push(argument)
        }
      MetaPropositionSymbol(symbol) =>
        if source.is_local_id(symbol.semantic_id()) {
          match symbols.find_proposition(symbol) {
            Some(replacement) =>
              arguments.push(MetaPropositionSymbol(replacement))
            None => return None
          }
        } else {
          arguments.push(argument)
        }
      MetaString(_) | MetaInteger(_) | MetaIdentifier(_) =>
        arguments.push(argument)
    }
  }
  Some({
    name: self.name,
    argument_types: self.argument_types.copy(),
    exclusive: self.exclusive,
    arguments,
  })
}

///|
/// User-provided substitutions for a theory clone. Proposition entries map a
/// source proposition to its requested kind, exactly like Why3's `th_inst`;
/// they do not substitute proposition symbols.
struct TheoryInstantiation {
  inst_ty : Array[(@logic.TypeSymbol, @logic.Ty)]
  inst_ts : Array[(@logic.TypeSymbol, @logic.TypeSymbol)]
  inst_ls : Array[(@logic.LSymbol, @logic.LSymbol)]
  inst_pr : Array[(@logic.PrSymbol, @logic.PropositionKind)]
  inst_df : @logic.PropositionKind
}

///|
pub(all) struct TheoryInstantiationView {
  inst_ty : ArrayView[(@logic.TypeSymbol, @logic.Ty)]
  inst_ts : ArrayView[(@logic.TypeSymbol, @logic.TypeSymbol)]
  inst_ls : ArrayView[(@logic.LSymbol, @logic.LSymbol)]
  inst_pr : ArrayView[(@logic.PrSymbol, @logic.PropositionKind)]
  inst_df : @logic.PropositionKind
}

///|
pub fn TheoryInstantiation::empty() -> TheoryInstantiation {
  { inst_ty: [], inst_ts: [], inst_ls: [], inst_pr: [], inst_df: Plemma }
}

///|
pub fn TheoryInstantiation::new(
  inst_ty : ArrayView[(@logic.TypeSymbol, @logic.Ty)],
  inst_ts : ArrayView[(@logic.TypeSymbol, @logic.TypeSymbol)],
  inst_ls : ArrayView[(@logic.LSymbol, @logic.LSymbol)],
  inst_pr : ArrayView[(@logic.PrSymbol, @logic.PropositionKind)],
  inst_df : @logic.PropositionKind,
  span : @identity.SourceSpan?,
) -> TheoryInstantiation raise TheoryError {
  let seen_types : Map[@logic.TypeSymbol, Unit] = Map([])
  for entry in inst_ty {
    let (source, target) = entry
    if seen_types.contains(source) {
      fail_theory(
        DuplicateCloneInstantiation,
        span,
        "clone contains two substitutions for one type symbol",
      )
    }
    require_same_id(source.semantic_id(), target.context_anchor(), span)
    seen_types[source] = ()
  }
  for entry in inst_ts {
    let (source, target) = entry
    if seen_types.contains(source) {
      fail_theory(
        DuplicateCloneInstantiation,
        span,
        "clone contains two substitutions for one type symbol",
      )
    }
    require_same_id(source.semantic_id(), target.semantic_id(), span)
    seen_types[source] = ()
  }
  let seen_logic : Map[@logic.LSymbol, Unit] = Map([])
  for entry in inst_ls {
    let (source, target) = entry
    if seen_logic.contains(source) {
      fail_theory(
        DuplicateCloneInstantiation,
        span,
        "clone contains two substitutions for one logic symbol",
      )
    }
    require_same_id(source.semantic_id(), target.semantic_id(), span)
    seen_logic[source] = ()
  }
  let seen_propositions : Map[@logic.PrSymbol, Unit] = Map([])
  for entry in inst_pr {
    let source = entry.0
    if seen_propositions.contains(source) {
      fail_theory(
        DuplicateCloneInstantiation,
        span,
        "clone contains two substitutions for one proposition",
      )
    }
    seen_propositions[source] = ()
  }
  {
    inst_ty: inst_ty.to_owned(),
    inst_ts: inst_ts.to_owned(),
    inst_ls: inst_ls.to_owned(),
    inst_pr: inst_pr.to_owned(),
    inst_df,
  }
}

///|
pub fn TheoryInstantiation::view(
  self : TheoryInstantiation,
) -> TheoryInstantiationView {
  {
    inst_ty: self.inst_ty[:],
    inst_ts: self.inst_ts[:],
    inst_ls: self.inst_ls[:],
    inst_pr: self.inst_pr[:],
    inst_df: self.inst_df,
  }
}

///|
priv struct CloneState {
  context : @identity.CompilationContext
  source : Theory
  target_known : @logic.KnownMap
  type_instances : Map[@logic.TypeSymbol, @logic.Ty]
  instantiated_type_symbols : Map[@logic.TypeSymbol, Unit]
  type_symbols : Map[@logic.TypeSymbol, @logic.TypeSymbol]
  instantiated_logic_symbols : Map[@logic.LSymbol, Unit]
  logic_symbols : Map[@logic.LSymbol, @logic.LSymbol]
  logic_origin_overrides : Map[@logic.LSymbol, @identity.Origin]
  proposition_kinds : Map[@logic.PrSymbol, @logic.PropositionKind]
  proposition_symbols : Map[@logic.PrSymbol, @logic.PrSymbol]
  proposition_origin_overrides : Map[@logic.PrSymbol, @identity.Origin]
  omitted_propositions : Map[@logic.PrSymbol, Unit]
  logic_definition_overrides : Array[
    (Array[@logic.LogicDefinition], Array[@logic.PrSymbol]),
  ]
  logic_definition_groups : Map[@logic.LSymbol, Int]
  logic_definition_propositions : Map[@logic.PrSymbol, Int]
  promoted_logic_definition_groups : Map[Int, Unit]
  rejected_logic_definition_groups : Map[Int, Unit]
  default_proposition_kind : @logic.PropositionKind
}

///|
pub fn Theory::is_local_id(self : Theory, id : @identity.SemanticId) -> Bool {
  self.local_symbols.contains(id)
}

///|
fn require_local_clone_symbol(
  source : Theory,
  id : @identity.SemanticId,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  if !source.is_local_id(id) {
    fail_theory(
      NonLocalCloneSymbol,
      span,
      "only a symbol local to the cloned theory can be instantiated",
    )
  }
}

///|
fn clone_type_variables_are_valid(
  symbol : @logic.TypeSymbol,
  replacement : @logic.Ty,
) -> Bool {
  let allowed : Map[@logic.TyVarSymbol, Unit] = Map([])
  for variable in symbol.view().parameters {
    allowed[variable] = ()
  }
  replacement.free_variables().all(variable => allowed.contains(variable))
}

///|
fn signature_type_matches(
  bindings : Map[@logic.TyVarSymbol, @logic.Ty],
  pattern : @logic.Ty,
  subject : @logic.Ty,
) -> Bool {
  match pattern.view() {
    TyVar(variable) =>
      match bindings.get(variable) {
        Some(previous) => previous == subject
        None => {
          bindings[variable] = subject
          true
        }
      }
    TyApp(pattern_symbol, pattern_arguments) =>
      match subject.view() {
        TyVar(_) => false
        TyApp(subject_symbol, subject_arguments) => {
          if pattern_symbol != subject_symbol ||
            pattern_arguments.length() != subject_arguments.length() {
            return false
          }
          for index, argument in pattern_arguments {
            if !signature_type_matches(
                bindings,
                argument,
                subject_arguments[index],
              ) {
              return false
            }
          }
          true
        }
      }
  }
}

///|
fn CloneState::translate_type(
  self : CloneState,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise {
  match ty.view() {
    TyVar(_) => ty
    TyApp(symbol, arguments) => {
      let translated = arguments.map(argument => {
        self.translate_type(argument, span)
      })
      match self.type_symbols.get(symbol) {
        Some(replacement) => @logic.Ty::app(replacement, translated, span)
        None =>
          match self.type_instances.get(symbol) {
            Some(replacement) => {
              let parameters = symbol.view().parameters
              if parameters.length() != translated.length() {
                fail_theory(
                  CloneTypeArityMismatch,
                  span,
                  "instantiated type constructor has the wrong arity",
                )
              }
              let mut substitution = @logic.TySubstitution::new()
              for index, parameter in parameters {
                substitution = substitution.bind(
                  parameter,
                  translated[index],
                  span,
                )
              }
              substitution.apply(replacement, span)
            }
            None => @logic.Ty::app(symbol, translated, span)
          }
      }
    }
  }
}

///|
fn CloneState::validate_logic_instantiation(
  self : CloneState,
  source : @logic.LSymbol,
  target : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let source_view = source.view()
  let target_view = target.view()
  if source_view.argument_types.length() != target_view.argument_types.length() {
    fail_theory(
      CloneLogicArityMismatch,
      span,
      "instantiated logic symbol has the wrong arity",
    )
  }
  match (source_view.result_type, target_view.result_type) {
    (None, Some(_)) | (Some(_), None) =>
      fail_theory(
        CloneLogicKindMismatch,
        span,
        "function and predicate symbols cannot instantiate one another",
      )
    _ => ()
  }
  let bindings : Map[@logic.TyVarSymbol, @logic.Ty] = Map([])
  // Why3 matches the replacement signature against the translated source:
  // a replacement may be more polymorphic, provided one consistent instance
  // of it has exactly the source signature.
  match (source_view.result_type, target_view.result_type) {
    (Some(source_result), Some(target_result)) =>
      if !signature_type_matches(
          bindings,
          target_result,
          self.translate_type(source_result, span),
        ) {
        fail_theory(
          CloneLogicTypeMismatch,
          span,
          "instantiated logic symbol '\{source_view.name}' -> '\{target_view.name}' has an incompatible result type",
        )
      }
    _ => ()
  }
  for index, source_argument in source_view.argument_types {
    if !signature_type_matches(
        bindings,
        target_view.argument_types[index],
        self.translate_type(source_argument, span),
      ) {
      fail_theory(
        CloneLogicTypeMismatch,
        span,
        "instantiated logic symbol '\{source_view.name}' -> '\{target_view.name}' has incompatible argument \{index}",
      )
    }
  }
}

///|
fn CloneState::new(
  context : @identity.CompilationContext,
  source : Theory,
  target_known : @logic.KnownMap,
  instantiation : TheoryInstantiation,
  span : @identity.SourceSpan?,
  logic_origin_overrides : ArrayView[(@logic.LSymbol, @identity.Origin)],
  proposition_origin_overrides : ArrayView[(@logic.PrSymbol, @identity.Origin)],
  omitted_propositions : ArrayView[@logic.PrSymbol],
  logic_definition_overrides : ArrayView[
    (Array[@logic.LogicDefinition], Array[@logic.PrSymbol]),
  ],
) -> CloneState raise {
  if !context.contains(source.anchor) {
    fail_theory(
      ContextMismatch,
      span,
      "cloned theory belongs to another compilation context",
    )
  }
  let state : CloneState = {
    context,
    source,
    target_known,
    type_instances: Map([]),
    instantiated_type_symbols: Map([]),
    type_symbols: Map([]),
    instantiated_logic_symbols: Map([]),
    logic_symbols: Map([]),
    logic_origin_overrides: Map([]),
    proposition_kinds: Map([]),
    proposition_symbols: Map([]),
    proposition_origin_overrides: Map([]),
    omitted_propositions: Map([]),
    logic_definition_overrides: logic_definition_overrides.to_owned(),
    logic_definition_groups: Map([]),
    logic_definition_propositions: Map([]),
    promoted_logic_definition_groups: Map([]),
    rejected_logic_definition_groups: Map([]),
    default_proposition_kind: instantiation.inst_df,
  }
  for entry in logic_origin_overrides {
    let (symbol, origin) = entry
    require_local_clone_symbol(source, symbol.semantic_id(), span)
    state.logic_origin_overrides[symbol] = origin
  }
  for entry in proposition_origin_overrides {
    let (symbol, origin) = entry
    require_local_clone_symbol(source, symbol.semantic_id(), span)
    state.proposition_origin_overrides[symbol] = origin
  }
  for proposition in omitted_propositions {
    require_local_clone_symbol(source, proposition.semantic_id(), span)
    state.omitted_propositions[proposition] = ()
  }
  for group_index, definition_group in logic_definition_overrides {
    if definition_group.0.is_empty() {
      fail_theory(
        InvalidTheoryItem,
        span,
        "a clone logic-definition override group cannot be empty",
      )
    }
    for definition in definition_group.0 {
      let symbol = definition.view().symbol
      require_local_clone_symbol(source, symbol.semantic_id(), span)
      if state.logic_definition_groups.contains(symbol) {
        fail_theory(
          InvalidTheoryItem,
          span,
          "a logic symbol occurs in two clone definition override groups",
        )
      }
      state.logic_definition_groups[symbol] = group_index
    }
    for proposition in definition_group.1 {
      require_local_clone_symbol(source, proposition.semantic_id(), span)
      if state.logic_definition_propositions.contains(proposition) {
        fail_theory(
          InvalidTheoryItem,
          span,
          "a proposition occurs in two clone definition override groups",
        )
      }
      state.logic_definition_propositions[proposition] = group_index
    }
  }
  for entry in instantiation.inst_ty {
    let (symbol, replacement) = entry
    require_local_clone_symbol(source, symbol.semantic_id(), span)
    if !clone_type_variables_are_valid(symbol, replacement) {
      fail_theory(
        CloneTypeVariableMismatch,
        span,
        "type instance contains a variable not bound by the source symbol",
      )
    }
    state.type_instances[symbol] = replacement
  }
  for entry in instantiation.inst_ts {
    let (symbol, replacement) = entry
    require_local_clone_symbol(source, symbol.semantic_id(), span)
    if symbol.arity() != replacement.arity() {
      fail_theory(
        CloneTypeArityMismatch,
        span,
        "instantiated type symbols have different arities",
      )
    }
    state.instantiated_type_symbols[symbol] = ()
    state.type_symbols[symbol] = replacement
  }
  for entry in instantiation.inst_ls {
    let (symbol, replacement) = entry
    require_local_clone_symbol(source, symbol.semantic_id(), span)
    state.validate_logic_instantiation(symbol, replacement, span)
    state.instantiated_logic_symbols[symbol] = ()
    state.logic_symbols[symbol] = replacement
  }
  for entry in instantiation.inst_pr {
    require_local_clone_symbol(source, entry.0.semantic_id(), span)
    state.proposition_kinds[entry.0] = entry.1
  }
  state
}

///|
fn CloneState::clone_type_symbol(
  self : CloneState,
  symbol : @logic.TypeSymbol,
  span : @identity.SourceSpan?,
) -> @logic.TypeSymbol? raise {
  if self.type_instances.contains(symbol) ||
    self.instantiated_type_symbols.contains(symbol) {
    if symbol.view().definition is NoDef {
      return None
    }
    fail_theory(
      CannotInstantiate,
      span,
      "a defined type symbol cannot be instantiated",
    )
  }
  if self.type_symbols.get(symbol) is Some(cloned) {
    return Some(cloned)
  }
  let view = symbol.view()
  let cloned = match (symbol.builtin_kind(), view.definition) {
    (Some(kind), NoDef) =>
      @logic.TypeSymbol::new_builtin(self.context, view.name, view.origin, kind)
    (None, NoDef) =>
      @logic.TypeSymbol::new_abstract(
        self.context,
        view.name,
        view.origin,
        view.parameters,
        span,
      )
    (None, Alias(target)) =>
      @logic.TypeSymbol::new_alias(
        self.context,
        view.name,
        view.origin,
        view.parameters,
        self.translate_type(target, span),
        span,
      )
    (None, Range(lower, upper)) =>
      @logic.TypeSymbol::new_range(
        self.context,
        view.name,
        view.origin,
        lower,
        upper,
        span,
      )
    (None, Float(exponent_digits, significand_digits)) =>
      @logic.TypeSymbol::new_float(
        self.context,
        view.name,
        view.origin,
        exponent_digits,
        significand_digits,
        span,
      )
    (Some(_), _) =>
      fail_theory(
        CannotInstantiate,
        span,
        "builtin type has an invalid clone definition",
      )
  }
  self.type_symbols[symbol] = cloned
  Some(cloned)
}

///|
fn CloneState::find_type_symbol(
  self : CloneState,
  symbol : @logic.TypeSymbol,
  span : @identity.SourceSpan?,
) -> @logic.TypeSymbol? raise TheoryError {
  match self.type_symbols.get(symbol) {
    Some(replacement) => Some(replacement)
    None =>
      if self.type_instances.contains(symbol) {
        None
      } else if self.source.is_local_id(symbol.semantic_id()) {
        fail_theory(
          MissingCloneSymbol,
          span,
          "local type symbol has no clone correspondence",
        )
      } else {
        Some(symbol)
      }
  }
}

///|
fn CloneState::clone_logic_symbol(
  self : CloneState,
  symbol : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> @logic.LSymbol raise {
  match self.logic_symbols.get(symbol) {
    Some(replacement) => return replacement
    None => ()
  }
  if !self.source.is_local_id(symbol.semantic_id()) {
    return symbol
  }
  let view = symbol.view()
  let origin = match self.logic_origin_overrides.get(symbol) {
    Some(origin) => origin
    None => view.origin
  }
  let arguments = view.argument_types.map(ty => self.translate_type(ty, span))
  let result_type = match view.result_type {
    Some(ty) => Some(self.translate_type(ty, span))
    None => None
  }
  let cloned = match (view.role, result_type) {
    (Ordinary, Some(result)) =>
      @logic.LSymbol::new_function(
        self.context,
        view.name,
        origin,
        arguments,
        result,
        span,
      )
    (Ordinary, None) =>
      @logic.LSymbol::new_predicate(
        self.context,
        view.name,
        origin,
        arguments,
        span,
      )
    (Constructor(count), Some(result)) =>
      @logic.LSymbol::new_constructor(
        self.context,
        view.name,
        origin,
        arguments,
        result,
        count,
        span,
      )
    (Projection, Some(result)) => {
      guard arguments is [source_type] else {
        fail_theory(
          CloneLogicArityMismatch,
          span,
          "projection clone does not have one argument",
        )
      }
      @logic.LSymbol::new_projection(
        self.context,
        view.name,
        origin,
        source_type,
        result,
        span,
      )
    }
    (Constructor(_), None) | (Projection, None) =>
      fail_theory(
        CloneLogicKindMismatch,
        span,
        "constructor or projection clone is not a function",
      )
  }
  self.logic_symbols[symbol] = cloned
  cloned
}

///|
fn CloneState::find_logic_symbol(
  self : CloneState,
  symbol : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> @logic.LSymbol raise TheoryError {
  match self.logic_symbols.get(symbol) {
    Some(replacement) => replacement
    None =>
      if self.source.is_local_id(symbol.semantic_id()) {
        fail_theory(
          MissingCloneSymbol,
          span,
          "local logic symbol has no clone correspondence",
        )
      } else {
        symbol
      }
  }
}

///|
fn clone_proposition_origin(origin : @identity.Origin) -> @identity.Origin {
  let attributes : Array[Bytes] = []
  for attribute in origin.attributes() {
    if attribute != b"useraxiom" {
      attributes.push(attribute)
    }
  }
  match origin.view() {
    UserOrigin(name, source_span, _) =>
      @identity.Origin::user(name, source_span, attributes)
    GeneratedOrigin(stage, name, source_span, _) =>
      @identity.Origin::generated(stage, name, source_span, attributes)
  }
}

///|
fn CloneState::clone_proposition_symbol(
  self : CloneState,
  symbol : @logic.PrSymbol,
) -> @logic.PrSymbol {
  match self.proposition_symbols.get(symbol) {
    Some(replacement) => replacement
    None => {
      let view = symbol.view()
      let origin = match self.proposition_origin_overrides.get(symbol) {
        Some(origin) => origin
        None => view.origin
      }
      let replacement = @logic.PrSymbol::new(
        self.context,
        view.name,
        clone_proposition_origin(origin),
      )
      self.proposition_symbols[symbol] = replacement
      replacement
    }
  }
}

///|
fn CloneState::find_proposition_symbol(
  self : CloneState,
  symbol : @logic.PrSymbol,
  span : @identity.SourceSpan?,
) -> @logic.PrSymbol raise TheoryError {
  match self.proposition_symbols.get(symbol) {
    Some(replacement) => replacement
    None =>
      if self.source.is_local_id(symbol.semantic_id()) {
        fail_theory(
          MissingCloneSymbol,
          span,
          "local proposition has no clone correspondence",
        )
      } else {
        symbol
      }
  }
}

///|
fn CloneState::optional_logic_symbol(
  self : CloneState,
  symbol : @logic.LSymbol,
) -> @logic.LSymbol? {
  match self.logic_symbols.get(symbol) {
    Some(replacement) => Some(replacement)
    None =>
      if self.source.is_local_id(symbol.semantic_id()) {
        None
      } else {
        Some(symbol)
      }
  }
}

///|
fn CloneState::optional_proposition_symbol(
  self : CloneState,
  symbol : @logic.PrSymbol,
) -> @logic.PrSymbol? {
  match self.proposition_symbols.get(symbol) {
    Some(replacement) => Some(replacement)
    None =>
      if self.source.is_local_id(symbol.semantic_id()) {
        None
      } else {
        Some(symbol)
      }
  }
}

///|
fn source_dependency_locator_sort_key(
  source : Theory,
  dependency : @logic.DeclDependency,
) -> (Int, Int) {
  for item_ordinal, item in source.items {
    guard item is TheoryDecl(declaration) else { continue }
    for inner_ordinal, introduced in declaration.introduced_symbols() {
      if introduced == dependency {
        return (item_ordinal, inner_ordinal)
      }
    }
  }
  abort("validated clone source lost a local symbol locator")
}

///|
fn sort_clone_type_instantiations(
  source : Theory,
  entries : ArrayView[CloneTypeInstantiation],
) -> Array[CloneTypeInstantiation] {
  let keyed = [
    for entry in entries => {
      let symbol = match entry {
        CloneType(symbol, _) | CloneTypeSymbol(symbol, _) => symbol
      }
      (
        source_dependency_locator_sort_key(source, TypeDependency(symbol)),
        entry,
      )
    }
  ]
  keyed.sort_by((left, right) => {
    let item_order = left.0.0.compare(right.0.0)
    if item_order != 0 {
      item_order
    } else {
      left.0.1.compare(right.0.1)
    }
  })
  [
    for entry in keyed => entry.1
  ]
}

///|
fn sort_clone_logic_instantiations(
  _source : Theory,
  entries : ArrayView[(@logic.LSymbol, @logic.LSymbol)],
) -> Array[(@logic.LSymbol, @logic.LSymbol)] {
  let sorted = entries.to_owned()
  // Why3's Mls map is ordered by the source symbol's allocation identity.
  // This differs from declaration-introduction order for records: their
  // projections are allocated before the synthetic constructor.
  sorted.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(
      right.0.semantic_id().local_id(),
    )
  })
  sorted
}

///|
fn sort_clone_proposition_instantiations(
  source : Theory,
  entries : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)],
) -> Array[(@logic.PrSymbol, @logic.PrSymbol)] {
  let keyed = [
    for entry in entries => {
      (
        source_dependency_locator_sort_key(
          source,
          PropositionDependency(entry.0),
        ),
        entry,
      )
    }
  ]
  keyed.sort_by((left, right) => {
    let item_order = left.0.0.compare(right.0.0)
    if item_order != 0 {
      item_order
    } else {
      left.0.1.compare(right.0.1)
    }
  })
  [
    for entry in keyed => entry.1
  ]
}

///|
fn CloneState::clone_variable(
  self : CloneState,
  variable : @logic.VSymbol,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  let view = variable.view()
  let translated_type = self.translate_type(view.ty, span)
  if translated_type == view.ty {
    variable
  } else {
    @logic.VSymbol::new(
      self.context,
      view.name,
      view.origin,
      translated_type,
      span,
    )
  }
}

///|
fn CloneState::clone_pattern(
  self : CloneState,
  pattern : @logic.Pattern,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  match pattern.view() {
    Pwild(ty) => @logic.Pattern::wild(self.translate_type(ty, span))
    Pvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Pattern::variable(replacement)
        None =>
          fail_theory(
            MissingCloneSymbol,
            span,
            "pattern variable has no clone correspondence",
          )
      }
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        self.clone_logic_symbol(symbol, span),
        arguments.map(argument => self.clone_pattern(argument, variables, span)),
        self.translate_type(ty, span),
        span,
      )
    Por(left, right, _) =>
      @logic.Pattern::or(
        self.clone_pattern(left, variables, span),
        self.clone_pattern(right, variables, span),
        span,
      )
    Pas(inner, variable, _) =>
      match variables.get(variable) {
        Some(replacement) =>
          @logic.Pattern::as_pattern(
            self.clone_pattern(inner, variables, span),
            replacement,
            span,
          )
        None =>
          fail_theory(
            MissingCloneSymbol,
            span,
            "as-pattern variable has no clone correspondence",
          )
      }
  }
}

///|
fn copy_term_decoration(
  source : @logic.Term,
  replacement : @logic.Term,
) -> @logic.Term {
  let replacement = match source.origin() {
    Some(origin) => replacement.decorate(origin, [])
    None => replacement
  }
  replacement.source_decorate(source.source_span(), source.attributes())
}

///|
fn CloneState::clone_term(
  self : CloneState,
  term : @logic.Term,
  variables : Map[@logic.VSymbol, @logic.VSymbol],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let cloned = match term.view() {
    Tvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => @logic.Term::variable(replacement)
        None => {
          let translated_type = self.translate_type(variable.ty(), span)
          if translated_type == variable.ty() {
            @logic.Term::variable(variable)
          } else {
            let replacement = self.clone_variable(variable, span)
            variables[variable] = replacement
            @logic.Term::variable(replacement)
          }
        }
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) else {
        abort("validated constant term lost its value type")
      }
      @logic.Term::constant(constant, self.translate_type(ty, span), span)
    }
    Tapp(symbol, _, arguments) => {
      let result_type = match term.ty() {
        Some(ty) => Some(self.translate_type(ty, span))
        None => None
      }
      @logic.Term::elaborated_apply(
        self.clone_logic_symbol(symbol, span),
        arguments.map(argument => self.clone_term(argument, variables, span)),
        result_type,
        span,
      )
    }
    Tif(condition, then_branch, else_branch) =>
      @logic.Term::if_then_else(
        self.clone_term(condition, variables, span),
        self.clone_term(then_branch, variables, span),
        self.clone_term(else_branch, variables, span),
        span,
      )
    Tlet(variable, value, body) => {
      let replacement = self.clone_variable(variable, span)
      let body_variables = variables.copy()
      body_variables[variable] = replacement
      @logic.Term::let_in(
        replacement,
        self.clone_term(value, variables, span),
        self.clone_term(body, body_variables, span),
        span,
      )
    }
    Tcase(scrutinee, branches) => {
      let cloned_branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        let branch_variables = variables.copy()
        for variable in clone_pattern_bound_variables(view.pattern) {
          branch_variables[variable] = self.clone_variable(variable, span)
        }
        cloned_branches.push(
          (
            self.clone_pattern(view.pattern, branch_variables, span),
            self.clone_term(view.body, branch_variables, span),
          ),
        )
      }
      @logic.Term::case(
        self.clone_term(scrutinee, variables, span),
        cloned_branches,
        span,
      )
    }
    Teps(variable, body) => {
      let replacement = self.clone_variable(variable, span)
      let body_variables = variables.copy()
      body_variables[variable] = replacement
      @logic.Term::epsilon(
        replacement,
        self.clone_term(body, body_variables, span),
        span,
      )
    }
    Tquant(quantifier, binders, triggers, body) => {
      let body_variables = variables.copy()
      let cloned_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let replacement = self.clone_variable(binder, span)
        cloned_binders.push(replacement)
        body_variables[binder] = replacement
      }
      let cloned_triggers = triggers.map(group => {
        group.map(trigger => self.clone_term(trigger, body_variables, span))
      })
      @logic.Term::quantify(
        quantifier,
        cloned_binders,
        cloned_triggers,
        self.clone_term(body, body_variables, span),
        span,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(
        operator,
        self.clone_term(left, variables, span),
        self.clone_term(right, variables, span),
        span,
      )
    Tnot(inner) =>
      @logic.Term::not(self.clone_term(inner, variables, span), span)
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_term_decoration(term, cloned)
}

///|
fn CloneState::normalize_program_definition_unit(
  self : CloneState,
  body : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  guard body.ty() is Some(result_type) &&
    result_type.view() is TyApp(type_symbol, arguments) &&
    arguments.is_empty() &&
    type_symbol.view().name == b"tuple0" else {
    return body
  }
  let constructors = Some(
    self.target_known.find_constructors(type_symbol, span),
  ) catch {
    _ => None
  }
  guard constructors is Some([data_constructor]) else { return body }
  let symbol = data_constructor.view().symbol
  guard symbol.view().name == b"Tuple0" &&
    symbol.view().argument_types.is_empty() else {
    return body
  }
  copy_term_decoration(
    body,
    @logic.Term::elaborated_apply(
      symbol,
      [],
      Some(result_type),
      body.source_span(),
    ),
  )
}

///|
fn CloneState::clone_logic_definition_declaration(
  self : CloneState,
  definitions : ArrayView[@logic.LogicDefinition],
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
  normalize_program_unit? : Bool = false,
) -> @logic.Decl raise {
  for definition in definitions {
    let symbol = definition.view().symbol
    if self.instantiated_logic_symbols.contains(symbol) {
      fail_theory(
        CannotInstantiate,
        span,
        "a defined logic symbol cannot be instantiated",
      )
    }
  }
  for definition in definitions {
    ignore(self.clone_logic_symbol(definition.view().symbol, span))
  }
  let cloned : Array[@logic.LogicDefinition] = []
  for definition in definitions {
    let view = definition.view()
    let variables : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
    let parameters : Array[@logic.VSymbol] = []
    for parameter in view.parameters {
      let replacement = self.clone_variable(parameter, span)
      parameters.push(replacement)
      variables[parameter] = replacement
    }
    let body = self.clone_term(view.body, variables, span)
    let body = if normalize_program_unit {
      self.normalize_program_definition_unit(body, span)
    } else {
      body
    }
    cloned.push(
      @logic.LogicDefinition::new(
        self.context,
        self.find_logic_symbol(view.symbol, span),
        parameters,
        body,
        span,
      ),
    )
  }
  let cloned_origin = if cloned.is_empty() {
    origin
  } else {
    cloned[0].view().symbol.view().origin
  }
  @logic.Decl::logic(self.context, cloned_origin, cloned, span)
}

///|
fn CloneState::promoted_logic_definition(
  self : CloneState,
  symbol : @logic.LSymbol,
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> @logic.Decl? raise {
  guard self.logic_definition_groups.get(symbol) is Some(group_index) else {
    return None
  }
  if self.promoted_logic_definition_groups.contains(group_index) {
    return None
  }
  if self.rejected_logic_definition_groups.contains(group_index) {
    return None
  }
  let definitions = self.logic_definition_overrides[group_index].0
  let promoted = Some(
    self.clone_logic_definition_declaration(
      definitions,
      origin,
      span,
      normalize_program_unit=true,
    ),
  ) catch {
    @logic.TypeError(diagnostic) =>
      if diagnostic.kind == NoTerminationProof {
        None
      } else {
        raise @logic.TypeError(diagnostic)
      }
    error => raise error
  }
  match promoted {
    Some(declaration) => {
      self.promoted_logic_definition_groups[group_index] = ()
      Some(declaration)
    }
    None => {
      self.rejected_logic_definition_groups[group_index] = ()
      None
    }
  }
}

///|
fn CloneState::clone_declaration(
  self : CloneState,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> @logic.Decl? raise {
  let origin = declaration.origin()
  match declaration.view() {
    Dtype(symbols) => {
      let cloned : Array[@logic.TypeSymbol] = []
      for symbol in symbols {
        if self.clone_type_symbol(symbol, span) is Some(replacement) {
          cloned.push(replacement)
        }
      }
      if cloned.is_empty() {
        None
      } else {
        Some(@logic.Decl::type_declaration(self.context, origin, cloned, span))
      }
    }
    Ddata(declarations) => {
      for declaration in declarations {
        let symbol = declaration.view().type_symbol
        if self.type_instances.contains(symbol) ||
          self.instantiated_type_symbols.contains(symbol) {
          fail_theory(
            CannotInstantiate,
            span,
            "an algebraic data type cannot be instantiated",
          )
        }
        ignore(self.clone_type_symbol(symbol, span))
      }
      for declaration in declarations {
        for data_constructor in declaration.view().constructors {
          let constructor_view = data_constructor.view()
          if self.instantiated_logic_symbols.contains(constructor_view.symbol) {
            fail_theory(
              CannotInstantiate,
              span,
              "a data constructor cannot be instantiated",
            )
          }
          // Why3 evaluates the projection list before the constructor argument
          // while rebuilding a cloned data declaration.  Identifier allocation
          // is observable in clone symbol maps, so preserve that order.
          for projection in constructor_view.projections {
            if projection is Some(projection) {
              if self.instantiated_logic_symbols.contains(projection) {
                fail_theory(
                  CannotInstantiate,
                  span,
                  "a record projection cannot be instantiated",
                )
              }
              ignore(self.clone_logic_symbol(projection, span))
            }
          }
          ignore(self.clone_logic_symbol(constructor_view.symbol, span))
        }
      }
      let cloned : Array[@logic.DataDeclaration] = []
      for declaration in declarations {
        let view = declaration.view()
        guard self.find_type_symbol(view.type_symbol, span) is Some(type_symbol) else {
          abort("data clone unexpectedly erased its type symbol")
        }
        let constructors : Array[@logic.DataConstructor] = []
        for data_constructor in view.constructors {
          let constructor_view = data_constructor.view()
          constructors.push(
            @logic.DataConstructor::new(
              self.find_logic_symbol(constructor_view.symbol, span),
              constructor_view.projections.map(projection => {
                match projection {
                  Some(symbol) => Some(self.find_logic_symbol(symbol, span))
                  None => None
                }
              }),
              span,
            ),
          )
        }
        cloned.push(
          @logic.DataDeclaration::new(type_symbol, constructors, span),
        )
      }
      Some(@logic.Decl::data(self.context, origin, cloned, span))
    }
    Dparam(symbol) =>
      match self.logic_definition_groups.get(symbol) {
        Some(group_index) if self.promoted_logic_definition_groups.contains(
            group_index,
          ) => None
        _ =>
          match self.promoted_logic_definition(symbol, origin, span) {
            Some(declaration) => Some(declaration)
            None =>
              if self.instantiated_logic_symbols.contains(symbol) {
                None
              } else {
                let cloned_symbol = self.clone_logic_symbol(symbol, span)
                Some(
                  @logic.Decl::parameter(
                    self.context,
                    cloned_symbol.view().origin,
                    cloned_symbol,
                    span,
                  ),
                )
              }
          }
      }
    Dlogic(definitions) =>
      Some(self.clone_logic_definition_declaration(definitions, origin, span))
    Dind(sign, declarations) => {
      for declaration in declarations {
        if self.instantiated_logic_symbols.contains(
            declaration.view().predicate,
          ) {
          fail_theory(
            CannotInstantiate,
            span,
            "a defined inductive predicate cannot be instantiated",
          )
        }
        for case_ in declaration.view().cases {
          if self.proposition_kinds.contains(case_.view().proposition) {
            fail_theory(
              CannotInstantiate,
              span,
              "an inductive case proposition cannot be instantiated",
            )
          }
        }
      }
      for declaration in declarations {
        ignore(self.clone_logic_symbol(declaration.view().predicate, span))
        for case_ in declaration.view().cases {
          ignore(self.clone_proposition_symbol(case_.view().proposition))
        }
      }
      let cloned : Array[@logic.InductiveDeclaration] = []
      for declaration in declarations {
        let view = declaration.view()
        let cases : Array[@logic.InductiveCase] = []
        for case_ in view.cases {
          let case_view = case_.view()
          cases.push(
            @logic.InductiveCase::new(
              self.context,
              self.find_proposition_symbol(case_view.proposition, span),
              self.clone_term(case_view.formula, Map([]), span),
              span,
            ),
          )
        }
        cloned.push(
          @logic.InductiveDeclaration::new(
            self.find_logic_symbol(view.predicate, span),
            cases,
            span,
          ),
        )
      }
      Some(@logic.Decl::inductive(self.context, origin, sign, cloned, span))
    }
    Dprop(kind, proposition, formula) => {
      if self.omitted_propositions.contains(proposition) {
        return None
      }
      if self.logic_definition_propositions.get(proposition)
        is Some(group_index) &&
        self.promoted_logic_definition_groups.contains(group_index) {
        return None
      }
      // Program declarations synthesize specification axioms while cloning
      // the routine itself.  Their origin override marks that module-clone
      // path: unlike ordinary theory axioms, they do not inherit the clone's
      // default proposition kind.
      let cloned_kind = if self.proposition_origin_overrides.contains(
          proposition,
        ) {
        match kind {
          Pgoal => None
          Plemma => Some(@logic.Plemma)
          Paxiom => Some(@logic.Paxiom)
        }
      } else {
        match (kind, self.proposition_kinds.get(proposition)) {
          (Pgoal, _) | (Plemma, Some(Pgoal)) => None
          (Plemma, _) => Some(@logic.Plemma)
          (Paxiom, Some(replacement)) => Some(replacement)
          (Paxiom, None) => Some(self.default_proposition_kind)
        }
      }
      match cloned_kind {
        None => None
        Some(cloned_kind) => {
          let cloned_proposition = self.clone_proposition_symbol(proposition)
          let cloned_origin = cloned_proposition.view().origin
          Some(
            @logic.Decl::proposition(
              self.context,
              cloned_origin,
              cloned_kind,
              cloned_proposition,
              self.clone_term(formula, Map([]), span),
              span,
            ),
          )
        }
      }
    }
  }
}

///|
fn CloneState::clone_meta(
  self : CloneState,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Meta? raise {
  let view = meta.view()
  let arguments : Array[MetaArgument] = []
  for argument in view.arguments {
    match argument {
      MetaType(ty) => arguments.push(MetaType(self.translate_type(ty, span)))
      MetaTypeSymbol(symbol) =>
        match self.find_type_symbol(symbol, span) {
          Some(replacement) => arguments.push(MetaTypeSymbol(replacement))
          None => return None
        }
      MetaLogicSymbol(symbol) =>
        match self.optional_logic_symbol(symbol) {
          Some(replacement) => arguments.push(MetaLogicSymbol(replacement))
          None => return None
        }
      MetaPropositionSymbol(symbol) =>
        match self.optional_proposition_symbol(symbol) {
          Some(replacement) =>
            arguments.push(MetaPropositionSymbol(replacement))
          None => return None
        }
      MetaString(value) => arguments.push(MetaString(value))
      MetaInteger(value) => arguments.push(MetaInteger(value))
      MetaIdentifier(value) => arguments.push(MetaIdentifier(value))
    }
  }
  let descriptor = MetaDescriptor::new(
    view.name,
    view.argument_types,
    view.exclusive,
    b"",
    span,
  )
  Some(descriptor.apply(arguments, span))
}

///|
fn CloneState::clone_witness(
  self : CloneState,
  witness : CloneWitness,
  anchor : @identity.SemanticId,
  source_item_identity : UInt,
  span : @identity.SourceSpan?,
) -> CloneWitness? raise {
  let view = witness.view()
  let type_instantiations : Array[CloneTypeInstantiation] = []
  for instantiation in view.type_instantiations {
    match instantiation {
      CloneType(symbol, ty) =>
        type_instantiations.push(
          CloneType(symbol, self.translate_type(ty, span)),
        )
      CloneTypeSymbol(symbol, target) =>
        match self.find_type_symbol(target, span) {
          Some(replacement) =>
            type_instantiations.push(CloneTypeSymbol(symbol, replacement))
          None => return None
        }
    }
  }
  let logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)] = []
  for entry in view.logic_instantiations {
    match self.optional_logic_symbol(entry.1) {
      Some(replacement) => logic_instantiations.push((entry.0, replacement))
      None => return None
    }
  }
  let proposition_instantiations : Array[(@logic.PrSymbol, @logic.PrSymbol)] = []
  for entry in view.proposition_instantiations {
    match self.optional_proposition_symbol(entry.1) {
      Some(replacement) =>
        proposition_instantiations.push((entry.0, replacement))
      None => return None
    }
  }
  let (type_instantiations, logic_instantiations, proposition_instantiations) = match
    self.source.clone_source(view.source) {
    Some(witness_source) =>
      (
        sort_clone_type_instantiations(witness_source, type_instantiations),
        sort_clone_logic_instantiations(witness_source, logic_instantiations),
        sort_clone_proposition_instantiations(
          witness_source, proposition_instantiations,
        ),
      )
    None =>
      (type_instantiations, logic_instantiations, proposition_instantiations)
  }
  Some(
    CloneWitness::trusted_new(
      anchor,
      view.source,
      source_item_identity,
      type_instantiations,
      logic_instantiations,
      proposition_instantiations,
      span,
    ),
  )
}

///|
fn Namespace::is_recursively_empty(self : Namespace) -> Bool {
  if !self.types.is_empty() ||
    !self.logic.is_empty() ||
    !self.propositions.is_empty() {
    return false
  }
  for entry in self.subspaces {
    if !entry.1.is_recursively_empty() {
      return false
    }
  }
  true
}

///|
fn CloneState::clone_namespace(
  self : CloneState,
  exported_namespace : Namespace,
  span : @identity.SourceSpan?,
  omit_empty_source_subspaces : Bool,
) -> Namespace raise TheoryError {
  let types : Array[(Bytes, @logic.TypeSymbol)] = []
  for entry in exported_namespace.types {
    if self.source.is_local_id(entry.1.semantic_id()) &&
      (
        self.type_instances.contains(entry.1) ||
        self.instantiated_type_symbols.contains(entry.1)
      ) {
      continue
    }
    match self.find_type_symbol(entry.1, span) {
      Some(replacement) => types.push((entry.0, replacement))
      None => ()
    }
  }
  let logic : Array[(Bytes, @logic.LSymbol)] = []
  for entry in exported_namespace.logic {
    if self.source.is_local_id(entry.1.semantic_id()) {
      if !self.instantiated_logic_symbols.contains(entry.1) {
        match self.logic_symbols.get(entry.1) {
          Some(replacement) => logic.push((entry.0, replacement))
          None => ()
        }
      }
    } else {
      logic.push(entry)
    }
  }
  let propositions : Array[(Bytes, @logic.PrSymbol)] = []
  for entry in exported_namespace.propositions {
    if self.source.is_local_id(entry.1.semantic_id()) {
      match self.proposition_symbols.get(entry.1) {
        Some(replacement) => propositions.push((entry.0, replacement))
        None => ()
      }
    } else {
      propositions.push(entry)
    }
  }
  let subspaces : Array[(Bytes, Namespace)] = []
  for entry in exported_namespace.subspaces {
    if omit_empty_source_subspaces && entry.1.is_recursively_empty() {
      continue
    }
    subspaces.push(
      (
        entry.0,
        self.clone_namespace(entry.1, span, omit_empty_source_subspaces),
      ),
    )
  }
  { types, logic, propositions, subspaces }
}

///|
fn sorted_type_instances(
  table : Map[@logic.TypeSymbol, @logic.Ty],
) -> Array[(@logic.TypeSymbol, @logic.Ty)] {
  let result = [ for key, value in table => (key, value) ]
  result.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  result
}

///|
fn sorted_type_symbols(
  table : Map[@logic.TypeSymbol, @logic.TypeSymbol],
) -> Array[(@logic.TypeSymbol, @logic.TypeSymbol)] {
  let result = [ for key, value in table => (key, value) ]
  result.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  result
}

///|
fn sorted_logic_symbols(
  table : Map[@logic.LSymbol, @logic.LSymbol],
) -> Array[(@logic.LSymbol, @logic.LSymbol)] {
  let result = [ for key, value in table => (key, value) ]
  result.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  result
}

///|
fn sorted_proposition_symbols(
  table : Map[@logic.PrSymbol, @logic.PrSymbol],
) -> Array[(@logic.PrSymbol, @logic.PrSymbol)] {
  let result = [ for key, value in table => (key, value) ]
  result.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  result
}

///|
fn CloneState::symbol_map(self : CloneState) -> SymbolMap {
  {
    sm_ty: sorted_type_instances(self.type_instances),
    sm_ts: sorted_type_symbols(self.type_symbols),
    sm_ls: sorted_logic_symbols(self.logic_symbols),
    sm_pr: sorted_proposition_symbols(self.proposition_symbols),
    item_boundaries: [],
  }
}

///|
fn TheoryBuilder::add_cloned_declaration(
  self : TheoryBuilder,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.known = self.known.add(declaration, span)
  for introduced in declaration.introduced_symbols() {
    self.local_symbols[introduced.semantic_id()] = ()
  }
  self.items.push(TheoryDecl(declaration))
}

///|
fn TheoryBuilder::add_cloned_use(
  self : TheoryBuilder,
  used : Theory,
  span : @identity.SourceSpan?,
) -> Unit raise {
  if self.used_theories.any(entry => entry.0 == used.key) {
    return
  }
  self.known = self.known.merge(used.known, span)
  self.register_used_theory(used)
  self.items.push(TheoryUse(used.key))
}

///|
/// Clones a closed theory into this builder and exports the translated source
/// namespace. Declarations hidden by the source namespace remain hidden.
fn TheoryBuilder::add_clone_in_place(
  self : TheoryBuilder,
  source : Theory,
  instantiation : TheoryInstantiation,
  span : @identity.SourceSpan?,
  logic_origin_overrides : ArrayView[(@logic.LSymbol, @identity.Origin)],
  proposition_origin_overrides : ArrayView[(@logic.PrSymbol, @identity.Origin)],
  omitted_propositions : ArrayView[@logic.PrSymbol],
  logic_definition_overrides : ArrayView[
    (Array[@logic.LogicDefinition], Array[@logic.PrSymbol]),
  ],
  omit_empty_source_subspaces : Bool,
) -> SymbolMap raise {
  self.require_open(span)
  let state = CloneState::new(
    self.context,
    source,
    self.known,
    instantiation,
    span,
    logic_origin_overrides,
    proposition_origin_overrides,
    omitted_propositions,
    logic_definition_overrides,
  )
  let item_boundaries : Array[Int] = [self.items.length()]
  for item in source.items {
    match item {
      TheoryDecl(declaration) =>
        match state.clone_declaration(declaration, span) {
          Some(cloned) => self.add_cloned_declaration(cloned, span)
          None => ()
        }
      TheoryUse(key) => self.add_cloned_use(source.used_theory(key), span)
      TheoryClone(witness) =>
        match
          state.clone_witness(
            witness,
            self.anchor,
            self.items.length().reinterpret_as_uint(),
            span,
          ) {
          Some(cloned) => {
            if source.clone_source(witness.view().source) is Some(nested) {
              self.register_clone_source(nested)
            }
            self.items.push(TheoryClone(cloned))
          }
          None => ()
        }
      TheoryMeta(meta) =>
        match state.clone_meta(meta, span) {
          Some(cloned) => self.add_meta(cloned, span)
          None => ()
        }
    }
    item_boundaries.push(self.items.length())
  }
  let symbol_map : SymbolMap = { ..state.symbol_map(), item_boundaries, }
  let map_view = symbol_map.view()
  let type_instantiations : Array[CloneTypeInstantiation] = []
  for entry in map_view.sm_ty {
    type_instantiations.push(CloneType(entry.0, entry.1))
  }
  for entry in map_view.sm_ts {
    type_instantiations.push(CloneTypeSymbol(entry.0, entry.1))
  }
  let witness_propositions = [
    for entry in map_view.sm_pr if !state.proposition_origin_overrides.contains(
      entry.0,
    ) => entry
  ]
  self.items.push(
    TheoryClone(
      CloneWitness::trusted_new(
        self.anchor,
        source.key,
        self.items.length().reinterpret_as_uint(),
        sort_clone_type_instantiations(source, type_instantiations),
        sort_clone_logic_instantiations(source, map_view.sm_ls),
        sort_clone_proposition_instantiations(source, witness_propositions),
        span,
      ),
    ),
  )
  self.register_clone_source(source)
  let cloned_namespace = state.clone_namespace(
    source.export_namespace,
    span,
    omit_empty_source_subspaces,
  )
  let index = self.import_namespaces.length() - 1
  let exported = self.export_namespaces[index].merge(cloned_namespace, span)
  self.import_namespaces[index] = self.import_namespaces[index].overlay(
    exported,
  )
  self.export_namespaces[index] = exported
  symbol_map
}

///|
fn TheoryBuilder::clone_staging_copy(self : TheoryBuilder) -> TheoryBuilder {
  {
    context: self.context,
    anchor: self.anchor,
    key: self.key,
    name: self.name,
    items: self.items.copy(),
    import_namespaces: self.import_namespaces.copy(),
    export_namespaces: self.export_namespaces.copy(),
    scope_names: self.scope_names.copy(),
    known: self.known,
    local_symbols: self.local_symbols.copy(),
    used_theories: self.used_theories.copy(),
    clone_sources: self.clone_sources.copy(),
    range_projections: self.range_projections.copy(),
    float_projections: self.float_projections.copy(),
    coercions: self.coercions,
    proved_wf: self.proved_wf.copy(),
    closed: self.closed,
  }
}

///|
/// Clones a closed theory transactionally. A rejected instance leaves the
/// mutable builder exactly as it was before the call.
pub fn TheoryBuilder::add_clone(
  self : TheoryBuilder,
  source : Theory,
  instantiation : TheoryInstantiation,
  span : @identity.SourceSpan?,
  logic_origin_overrides? : ArrayView[(@logic.LSymbol, @identity.Origin)] = [],
  proposition_origin_overrides? : ArrayView[(@logic.PrSymbol, @identity.Origin)] = [],
  omitted_propositions? : ArrayView[@logic.PrSymbol] = [],
  logic_definition_overrides? : ArrayView[
    (Array[@logic.LogicDefinition], Array[@logic.PrSymbol]),
  ] = [],
  omit_empty_source_subspaces? : Bool = false,
) -> SymbolMap raise {
  self.require_open(span)
  let old_item_count = self.items.length()
  let old_used_count = self.used_theories.length()
  let old_clone_source_count = self.clone_sources.length()
  let staged = self.clone_staging_copy()
  let result = staged.add_clone_in_place(
    source, instantiation, span, logic_origin_overrides, proposition_origin_overrides,
    omitted_propositions, logic_definition_overrides, omit_empty_source_subspaces,
  )
  for index = old_item_count; index < staged.items.length(); index = index + 1 {
    self.items.push(staged.items[index])
  }
  self.import_namespaces = staged.import_namespaces.copy()
  self.export_namespaces = staged.export_namespaces.copy()
  self.known = staged.known
  for id, _ in staged.local_symbols {
    self.local_symbols[id] = ()
  }
  for index = old_used_count
      index < staged.used_theories.length()
      index = index + 1 {
    self.used_theories.push(staged.used_theories[index])
  }
  for index = old_clone_source_count
      index < staged.clone_sources.length()
      index = index + 1 {
    self.clone_sources.push(staged.clone_sources[index])
  }
  self.range_projections = staged.range_projections
  self.float_projections = staged.float_projections
  self.coercions = staged.coercions
  self.proved_wf = staged.proved_wf
  result
}

// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum PropositionKind {
  Paxiom
  Plemma
  Pgoal
} derive(Eq, Debug)

///|
struct LogicDefinition {
  symbol : LSymbol
  parameters : Array[VSymbol]
  body : Term
}

///|
struct DataConstructor {
  symbol : LSymbol
  projections : Array[LSymbol?]
}

///|
struct DataDeclaration {
  type_symbol : TypeSymbol
  constructors : Array[DataConstructor]
}

///|
struct InductiveCase {
  proposition : PrSymbol
  formula : Term
}

///|
struct InductiveDeclaration {
  predicate : LSymbol
  cases : Array[InductiveCase]
}

///|
priv enum DeclNode {
  TypeDeclaration(Array[TypeSymbol])
  DataDeclarationNode(Array[DataDeclaration])
  ParameterDeclaration(LSymbol)
  LogicDeclaration(Array[LogicDefinition])
  InductiveDeclarationNode(Array[InductiveDeclaration])
  PropositionDeclaration(PropositionKind, PrSymbol, Term)
}

///|
struct Decl {
  origin : @identity.Origin
  dependencies : Array[DeclDependency]
  introduced : Array[DeclDependency]
  node : DeclNode
}

///|
pub(all) struct LogicDefinitionView {
  symbol : LSymbol
  parameters : ArrayView[VSymbol]
  body : Term
}

///|
pub(all) struct DataConstructorView {
  symbol : LSymbol
  projections : ArrayView[LSymbol?]
}

///|
pub(all) struct DataDeclarationView {
  type_symbol : TypeSymbol
  constructors : ArrayView[DataConstructor]
}

///|
pub(all) struct InductiveCaseView {
  proposition : PrSymbol
  formula : Term
}

///|
pub(all) struct InductiveDeclarationView {
  predicate : LSymbol
  cases : ArrayView[InductiveCase]
}

///|
pub(all) enum DeclView {
  Dtype(ArrayView[TypeSymbol])
  Ddata(ArrayView[DataDeclaration])
  Dparam(LSymbol)
  Dlogic(ArrayView[LogicDefinition])
  Dind(ArrayView[InductiveDeclaration])
  Dprop(PropositionKind, PrSymbol, Term)
}

///|
pub fn LogicDefinition::view(self : LogicDefinition) -> LogicDefinitionView {
  { symbol: self.symbol, parameters: self.parameters[:], body: self.body }
}

///|
pub fn DataConstructor::view(self : DataConstructor) -> DataConstructorView {
  { symbol: self.symbol, projections: self.projections[:] }
}

///|
pub fn DataDeclaration::view(self : DataDeclaration) -> DataDeclarationView {
  { type_symbol: self.type_symbol, constructors: self.constructors[:] }
}

///|
pub fn InductiveCase::view(self : InductiveCase) -> InductiveCaseView {
  { proposition: self.proposition, formula: self.formula }
}

///|
pub fn InductiveDeclaration::view(
  self : InductiveDeclaration,
) -> InductiveDeclarationView {
  { predicate: self.predicate, cases: self.cases[:] }
}

///|
pub fn Decl::origin(self : Decl) -> @identity.Origin {
  self.origin
}

///|
pub fn Decl::dependencies(self : Decl) -> ArrayView[DeclDependency] {
  self.dependencies[:]
}

///|
pub fn Decl::introduced_symbols(self : Decl) -> ArrayView[DeclDependency] {
  self.introduced[:]
}

///|
pub fn Decl::view(self : Decl) -> DeclView {
  match self.node {
    TypeDeclaration(symbols) => Dtype(symbols[:])
    DataDeclarationNode(declarations) => Ddata(declarations[:])
    ParameterDeclaration(symbol) => Dparam(symbol)
    LogicDeclaration(definitions) => Dlogic(definitions[:])
    InductiveDeclarationNode(declarations) => Dind(declarations[:])
    PropositionDeclaration(kind, symbol, formula) =>
      Dprop(kind, symbol, formula)
  }
}

///|
fn validate_pattern_context(
  context : @identity.CompilationContext,
  pattern : Pattern,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  require_context_id(
    context,
    pattern.ty.context_anchor(),
    span,
    "pattern type belongs to another compilation context",
  )
  for variable in pattern.bound_variables {
    require_context_id(
      context,
      variable.semantic_id(),
      span,
      "pattern binder belongs to another compilation context",
    )
  }
  match pattern.node {
    WildPattern | VariablePattern(_) => ()
    ApplicationPattern(symbol, arguments) => {
      require_context_id(
        context,
        symbol.semantic_id(),
        span,
        "pattern constructor belongs to another compilation context",
      )
      for argument in arguments {
        validate_pattern_context(context, argument, span)
      }
    }
    OrPattern(left, right) => {
      validate_pattern_context(context, left, span)
      validate_pattern_context(context, right, span)
    }
    AsPattern(inner, _) => validate_pattern_context(context, inner, span)
  }
}

///|
fn validate_term_context(
  context : @identity.CompilationContext,
  term : Term,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  if term.result_type is Some(ty) {
    require_context_id(
      context,
      ty.context_anchor(),
      span,
      "term type belongs to another compilation context",
    )
  }
  let recurse = fn(child) -> Unit raise TypeError {
    validate_term_context(context, child, span)
  }
  match term.node {
    VariableTerm(variable) =>
      require_context_id(
        context,
        variable.semantic_id(),
        span,
        "term variable belongs to another compilation context",
      )
    ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(symbol, _, arguments) => {
      require_context_id(
        context,
        symbol.semantic_id(),
        span,
        "term symbol belongs to another compilation context",
      )
      for argument in arguments {
        recurse(argument)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      recurse(condition)
      recurse(then_branch)
      recurse(else_branch)
    }
    LetTerm(variable, value, body) => {
      require_context_id(
        context,
        variable.semantic_id(),
        span,
        "let binder belongs to another compilation context",
      )
      recurse(value)
      recurse(body)
    }
    CaseTerm(scrutinee, branches) => {
      recurse(scrutinee)
      for branch in branches {
        validate_pattern_context(context, branch.pattern, span)
        recurse(branch.body)
      }
    }
    EpsilonTerm(variable, body) => {
      require_context_id(
        context,
        variable.semantic_id(),
        span,
        "epsilon binder belongs to another compilation context",
      )
      recurse(body)
    }
    QuantifiedTerm(_, binders, triggers, body) => {
      for binder in binders {
        require_context_id(
          context,
          binder.semantic_id(),
          span,
          "quantifier binder belongs to another compilation context",
        )
      }
      for group in triggers {
        for trigger in group {
          recurse(trigger)
        }
      }
      recurse(body)
    }
    BinaryTerm(_, left, right) => {
      recurse(left)
      recurse(right)
    }
    NotTerm(inner) => recurse(inner)
  }
}

///|
fn validate_logic_definition(
  context : @identity.CompilationContext,
  symbol : LSymbol,
  parameters : ArrayView[VSymbol],
  body : Term,
  allow_recursive : Bool,
  span : @identity.SourceSpan?,
) -> LogicDefinition raise TypeError {
  require_context_id(
    context,
    symbol.semantic_id(),
    span,
    "logic definition symbol belongs to another compilation context",
  )
  if !(symbol.role is OrdinaryRole) {
    fail_type(
      InvalidDeclaration,
      span,
      "constructor or projection cannot have a logic definition",
    )
  }
  if parameters.length() != symbol.argument_types.length() {
    fail_type(ArityMismatch, span, "logic definition has the wrong arity")
  }
  let copied = parameters.to_owned()
  let parameter_set : Map[VSymbol, Unit] = Map([])
  for index, parameter in copied {
    require_context_id(
      context,
      parameter.semantic_id(),
      span,
      "logic definition parameter belongs to another compilation context",
    )
    if parameter_set.contains(parameter) {
      fail_type(DuplicateBinder, span, "logic definition repeats a parameter")
    }
    if parameter.ty != symbol.argument_types[index] {
      fail_type(
        TypeMismatch,
        span,
        "logic definition parameter has the wrong type",
      )
    }
    parameter_set[parameter] = ()
  }
  match (symbol.result_type, body.result_type) {
    (None, None) => ()
    (Some(expected), Some(actual)) =>
      if expected != actual {
        fail_type(TypeMismatch, span, "logic definition result type mismatch")
      }
    (None, Some(_)) =>
      fail_type(FormulaExpected, span, "predicate definition must be a formula")
    (Some(_), None) =>
      fail_type(ValueExpected, span, "function definition must be a value")
  }
  validate_term_context(context, body, span)
  for variable in body.free_variables() {
    if !parameter_set.contains(variable) {
      fail_type(
        UnboundVariable,
        span,
        "logic definition contains an unbound value variable",
      )
    }
  }
  let allowed_types : Map[TyVarSymbol, Unit] = Map([])
  for variable in symbol.type_parameters {
    allowed_types[variable] = ()
  }
  for variable in body.free_type_variables() {
    if !allowed_types.contains(variable) {
      fail_type(
        UnboundTypeVariable,
        span,
        "logic definition contains an unbound type variable",
      )
    }
  }
  if !allow_recursive && body.contains_logic_symbol(symbol) {
    fail_type(
      CyclicDefinition,
      span,
      "user logic definitions must be non-recursive",
    )
  }
  { symbol, parameters: copied, body }
}

///|
pub fn LogicDefinition::new(
  context : @identity.CompilationContext,
  symbol : LSymbol,
  parameters : ArrayView[VSymbol],
  body : Term,
  span : @identity.SourceSpan?,
) -> LogicDefinition raise TypeError {
  validate_logic_definition(context, symbol, parameters, body, false, span)
}

///|
pub fn LogicDefinition::trusted_recursive(
  context : @identity.CompilationContext,
  symbol : LSymbol,
  parameters : ArrayView[VSymbol],
  body : Term,
  span : @identity.SourceSpan?,
) -> LogicDefinition raise TypeError {
  require_snapshot_origin(symbol.origin, span)
  validate_logic_definition(context, symbol, parameters, body, true, span)
}

///|
pub fn DataConstructor::trusted_new(
  symbol : LSymbol,
  projections : ArrayView[LSymbol?],
  span : @identity.SourceSpan?,
) -> DataConstructor raise TypeError {
  require_snapshot_origin(symbol.origin, span)
  guard symbol.role is ConstructorRole(_) else {
    fail_type(
      InvalidDeclaration,
      span,
      "data constructor requires a trusted constructor symbol",
    )
  }
  if projections.length() != symbol.argument_types.length() {
    fail_type(
      ArityMismatch,
      span,
      "constructor projection list has the wrong arity",
    )
  }
  let copied = projections.to_owned()
  for projection in copied {
    if projection is Some(projection) {
      require_snapshot_origin(projection.origin, span)
      if !(projection.role is ProjectionRole) {
        fail_type(
          InvalidDeclaration,
          span,
          "data field requires a trusted projection symbol",
        )
      }
    }
  }
  { symbol, projections: copied }
}

///|
pub fn DataDeclaration::trusted_new(
  type_symbol : TypeSymbol,
  constructors : ArrayView[DataConstructor],
  span : @identity.SourceSpan?,
) -> DataDeclaration raise TypeError {
  require_snapshot_origin(type_symbol.origin, span)
  let invalid_builtin = match type_symbol.builtin_kind {
    None => false
    Some(BuiltinBoolean) => false
    Some(_) => true
  }
  if !(type_symbol.definition is DefinitionNone) || invalid_builtin {
    fail_type(
      InvalidDeclaration,
      span,
      "data declaration requires a NoDef type or trusted builtin boolean",
    )
  }
  if constructors.is_empty() {
    fail_type(EmptyDeclaration, span, "data declaration has no constructors")
  }
  let parameter_types = [
    for parameter in type_symbol.parameters => Ty::variable(parameter)
  ]
  let expected_result = Ty::app(type_symbol, parameter_types, span)
  let copied = constructors.to_owned()
  let seen : Map[LSymbol, Unit] = Map([])
  let record_fields : Map[LSymbol, Unit] = Map([])
  for data_constructor in copied {
    for projection in data_constructor.projections {
      if projection is Some(projection) {
        record_fields[projection] = ()
      }
    }
  }
  for data_constructor in copied {
    if seen.contains(data_constructor.symbol) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "data declaration repeats a constructor",
      )
    }
    seen[data_constructor.symbol] = ()
    guard data_constructor.symbol.role is ConstructorRole(count) else {
      abort("validated data constructor lost its role")
    }
    if count != copied.length() ||
      data_constructor.symbol.result_type != Some(expected_result) {
      fail_type(
        InvalidDeclaration,
        span,
        "constructor result or constructor count is invalid",
      )
    }
    let constructor_fields : Map[LSymbol, Unit] = Map([])
    for index, projection in data_constructor.projections {
      if projection is Some(projection) {
        if constructor_fields.contains(projection) {
          fail_type(
            DuplicateDeclarationSymbol,
            span,
            "data constructor repeats a projection",
          )
        }
        constructor_fields[projection] = ()
        if projection.argument_types != [expected_result] ||
          projection.result_type !=
          Some(data_constructor.symbol.argument_types[index]) {
          fail_type(
            InvalidDeclaration,
            span,
            "projection signature does not match its constructor field",
          )
        }
      }
    }
    if constructor_fields.length() != record_fields.length() ||
      record_fields.keys().any(field => !constructor_fields.contains(field)) {
      fail_type(
        InvalidDeclaration,
        span,
        "every constructor of a record type must expose the same projections",
      )
    }
  }
  { type_symbol, constructors: copied }
}

///|
fn validate_data_argument_type(
  ty : Ty,
  data_symbols : Map[TypeSymbol, Unit],
  allowed_variables : Map[TyVarSymbol, Unit],
  below_data_type : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  match ty.node {
    VariableNode(variable) =>
      if !allowed_variables.contains(variable) {
        fail_type(
          UnboundTypeVariable,
          span,
          "data constructor argument contains an unbound type variable",
        )
      }
    ApplicationNode(symbol, arguments) => {
      let is_data_type = data_symbols.contains(symbol)
      if below_data_type && is_data_type {
        fail_type(
          InvalidDeclaration,
          span,
          "data constructor contains a nested recursive data occurrence",
        )
      }
      for argument in arguments {
        validate_data_argument_type(
          argument,
          data_symbols,
          allowed_variables,
          below_data_type || is_data_type,
          span,
        )
      }
    }
  }
}

///|
fn validate_data_declaration_group(
  declarations : ArrayView[DataDeclaration],
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  let data_symbols : Map[TypeSymbol, Unit] = Map([])
  for declaration in declarations {
    data_symbols[declaration.type_symbol] = ()
  }
  for declaration in declarations {
    let allowed_variables : Map[TyVarSymbol, Unit] = Map([])
    for parameter in declaration.type_symbol.parameters {
      allowed_variables[parameter] = ()
    }
    for data_constructor in declaration.constructors {
      for argument_type in data_constructor.symbol.argument_types {
        validate_data_argument_type(
          argument_type, data_symbols, allowed_variables, false, span,
        )
      }
    }
  }
}

///|
pub fn InductiveCase::trusted_new(
  context : @identity.CompilationContext,
  proposition : PrSymbol,
  formula : Term,
  span : @identity.SourceSpan?,
) -> InductiveCase raise TypeError {
  require_snapshot_origin(proposition.origin, span)
  require_formula(formula, span)
  validate_term_context(context, formula, span)
  if !formula.free_variables().is_empty() {
    fail_type(
      UnboundVariable,
      span,
      "inductive case contains an unbound value variable",
    )
  }
  { proposition, formula }
}

///|
pub fn InductiveDeclaration::trusted_new(
  predicate : LSymbol,
  cases : ArrayView[InductiveCase],
  span : @identity.SourceSpan?,
) -> InductiveDeclaration raise TypeError {
  require_snapshot_origin(predicate.origin, span)
  if predicate.result_type is Some(_) {
    fail_type(
      PredicateExpected,
      span,
      "inductive declaration requires a predicate",
    )
  }
  if cases.is_empty() {
    fail_type(EmptyDeclaration, span, "inductive declaration has no cases")
  }
  let copied = cases.to_owned()
  let seen : Map[PrSymbol, Unit] = Map([])
  for case_ in copied {
    if seen.contains(case_.proposition) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "inductive declaration repeats a case proposition",
      )
    }
    seen[case_.proposition] = ()
    guard inductive_case_head(case_.formula) is Some(head) &&
      head.node is ApplicationTerm(head_symbol, _, _) &&
      head_symbol == predicate else {
      fail_type(
        InvalidDeclaration,
        span,
        "inductive case conclusion must apply its declared predicate",
      )
    }
    let head_type_variables : Map[TyVarSymbol, Unit] = Map([])
    for variable in head.free_type_variables() {
      head_type_variables[variable] = ()
    }
    for variable in case_.formula.free_type_variables() {
      if !head_type_variables.contains(variable) {
        fail_type(
          UnboundTypeVariable,
          span,
          "inductive case contains a type variable absent from its head",
        )
      }
    }
  }
  { predicate, cases: copied }
}

///|
fn inductive_case_head(term : Term) -> Term? {
  match term.node {
    QuantifiedTerm(ForallQuantifier, _, _, body) => inductive_case_head(body)
    BinaryTerm(Implies, _, conclusion) => inductive_case_head(conclusion)
    LetTerm(_, _, body) => inductive_case_head(body)
    QuantifiedTerm(ExistsQuantifier, _, _, _) | _ => Some(term)
  }
}

///|
fn inverse_polarity(polarity : Int) -> Int {
  if polarity == 0 {
    0
  } else {
    -polarity
  }
}

///|
fn validate_inductive_polarity(
  term : Term,
  predicates : Map[LSymbol, Unit],
  polarity : Int,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  let neutral = fn(child) -> Unit raise TypeError {
    validate_inductive_polarity(child, predicates, 0, span)
  }
  let same = fn(child) -> Unit raise TypeError {
    validate_inductive_polarity(child, predicates, polarity, span)
  }
  match term.node {
    VariableTerm(_) | ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(symbol, _, arguments) => {
      if predicates.contains(symbol) && polarity != 1 {
        fail_type(
          InvalidDeclaration,
          span,
          "inductive predicate occurs outside a positive position",
        )
      }
      for argument in arguments {
        neutral(argument)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      neutral(condition)
      same(then_branch)
      same(else_branch)
    }
    LetTerm(_, value, body) => {
      neutral(value)
      same(body)
    }
    CaseTerm(scrutinee, branches) => {
      neutral(scrutinee)
      for branch in branches {
        same(branch.body)
      }
    }
    EpsilonTerm(_, body) => neutral(body)
    QuantifiedTerm(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          neutral(trigger)
        }
      }
      same(body)
    }
    BinaryTerm(operator, left, right) =>
      match operator {
        And | Or => {
          same(left)
          same(right)
        }
        Implies => {
          validate_inductive_polarity(
            left,
            predicates,
            inverse_polarity(polarity),
            span,
          )
          same(right)
        }
        Iff => {
          neutral(left)
          neutral(right)
        }
      }
    NotTerm(inner) =>
      validate_inductive_polarity(
        inner,
        predicates,
        inverse_polarity(polarity),
        span,
      )
  }
}

///|
/// Why3 treats the leading implication premises of an inductive clause as
/// positive recursive hypotheses. Polarity is then checked inside each
/// premise and inside the final predicate head independently.
fn validate_inductive_clause_polarity(
  term : Term,
  predicates : Map[LSymbol, Unit],
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  match term.node {
    QuantifiedTerm(ForallQuantifier, _, _, body) =>
      validate_inductive_clause_polarity(body, predicates, span)
    BinaryTerm(Implies, premise, conclusion) => {
      validate_inductive_polarity(premise, predicates, 1, span)
      validate_inductive_clause_polarity(conclusion, predicates, span)
    }
    LetTerm(_, value, body) => {
      validate_inductive_polarity(value, predicates, 0, span)
      validate_inductive_clause_polarity(body, predicates, span)
    }
    _ => validate_inductive_polarity(term, predicates, 1, span)
  }
}

///|
pub fn Decl::type_declaration(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  symbols : ArrayView[TypeSymbol],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  if symbols.is_empty() {
    fail_type(EmptyDeclaration, span, "type declaration is empty")
  }
  let copied = symbols.to_owned()
  for symbol in copied {
    require_context_id(
      context,
      symbol.semantic_id(),
      span,
      "type declaration belongs to another compilation context",
    )
    match symbol.definition {
      DefinitionNone | DefinitionAlias(_) => ()
      DefinitionRange(_, _) | DefinitionFloat(_, _) =>
        fail_type(
          InvalidDeclaration,
          span,
          "user declarations cannot create Range or Float types",
        )
    }
  }
  make_decl(context, origin, TypeDeclaration(copied), span)
}

///|
/// Trusted decoder entry point for snapshot type declarations, including
/// Range and Float definitions that user declarations cannot construct.
pub fn Decl::trusted_type_declaration(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  symbols : ArrayView[TypeSymbol],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_snapshot_origin(origin, span)
  if symbols.is_empty() {
    fail_type(EmptyDeclaration, span, "trusted type declaration is empty")
  }
  let copied = symbols.to_owned()
  for symbol in copied {
    require_snapshot_origin(symbol.origin, span)
    require_context_id(
      context,
      symbol.semantic_id(),
      span,
      "trusted type declaration belongs to another compilation context",
    )
  }
  make_decl(context, origin, TypeDeclaration(copied), span)
}

///|
pub fn Decl::parameter(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  symbol : LSymbol,
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_context_id(
    context,
    symbol.semantic_id(),
    span,
    "parameter declaration belongs to another compilation context",
  )
  if !(symbol.role is OrdinaryRole) {
    fail_type(
      InvalidDeclaration,
      span,
      "user parameter cannot be a constructor or projection",
    )
  }
  make_decl(context, origin, ParameterDeclaration(symbol), span)
}

///|
pub fn Decl::logic(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  definitions : ArrayView[LogicDefinition],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  if definitions.is_empty() {
    fail_type(EmptyDeclaration, span, "logic declaration is empty")
  }
  let copied = definitions.to_owned()
  let defined : Map[LSymbol, Unit] = Map([])
  for definition in copied {
    if defined.contains(definition.symbol) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "logic declaration repeats a symbol",
      )
    }
    defined[definition.symbol] = ()
  }
  for definition in copied {
    for symbol in defined.keys() {
      if definition.body.contains_logic_symbol(symbol) {
        fail_type(CyclicDefinition, span, "user logic declaration is recursive")
      }
    }
  }
  make_decl(context, origin, LogicDeclaration(copied), span)
}

///|
pub fn Decl::trusted_logic(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  definitions : ArrayView[LogicDefinition],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_snapshot_origin(origin, span)
  if definitions.is_empty() {
    fail_type(EmptyDeclaration, span, "trusted logic declaration is empty")
  }
  let copied = definitions.to_owned()
  for definition in copied {
    require_snapshot_origin(definition.symbol.origin, span)
  }
  make_decl(context, origin, LogicDeclaration(copied), span)
}

///|
pub fn Decl::proposition(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  kind : PropositionKind,
  symbol : PrSymbol,
  formula : Term,
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_context_id(
    context,
    symbol.semantic_id(),
    span,
    "proposition belongs to another compilation context",
  )
  require_formula(formula, span)
  validate_term_context(context, formula, span)
  if !formula.free_variables().is_empty() {
    fail_type(
      UnboundVariable,
      span,
      "proposition contains an unbound value variable",
    )
  }
  make_decl(
    context,
    origin,
    PropositionDeclaration(kind, symbol, formula),
    span,
  )
}

///|
/// Reclassifies a validated proposition while preserving its symbol, formula,
/// origin, and dependencies. Theory splitting uses this to turn a lemma into
/// a goal for its own task and into an axiom for subsequent tasks.
pub fn Decl::reclassify_proposition(
  self : Decl,
  context : @identity.CompilationContext,
  kind : PropositionKind,
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  match self.node {
    PropositionDeclaration(_, symbol, formula) =>
      Decl::proposition(context, self.origin, kind, symbol, formula, span)
    _ =>
      fail_type(
        InvalidDeclaration,
        span,
        "only proposition declarations can be reclassified",
      )
  }
}

///|
pub fn Decl::trusted_data(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  declarations : ArrayView[DataDeclaration],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_snapshot_origin(origin, span)
  if declarations.is_empty() {
    fail_type(EmptyDeclaration, span, "trusted data declaration is empty")
  }
  let copied = declarations.to_owned()
  validate_data_declaration_group(copied, span)
  make_decl(context, origin, DataDeclarationNode(copied), span)
}

///|
pub fn Decl::trusted_inductive(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  declarations : ArrayView[InductiveDeclaration],
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  require_snapshot_origin(origin, span)
  if declarations.is_empty() {
    fail_type(EmptyDeclaration, span, "trusted inductive declaration is empty")
  }
  let copied = declarations.to_owned()
  let predicates : Map[LSymbol, Unit] = Map([])
  for declaration in copied {
    predicates[declaration.predicate] = ()
  }
  for declaration in copied {
    for case_ in declaration.cases {
      validate_inductive_clause_polarity(case_.formula, predicates, span)
    }
  }
  make_decl(context, origin, InductiveDeclarationNode(copied), span)
}

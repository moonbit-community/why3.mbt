// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// A declaration-history set used by the derived clone and meta indexes.
/// Canonical encoders intentionally serialize the linked declaration history,
/// not this cache.
struct TDeclSet {
  tds_set : Array[TheoryItem]
}

///|
pub(all) struct TDeclSetView {
  tds_set : ArrayView[TheoryItem]
}

///|
pub fn TDeclSet::view(self : TDeclSet) -> TDeclSetView {
  { tds_set: self.tds_set[:] }
}

///|
struct TaskHead {
  task_decl : TDecl
  task_prev : TaskHead?
  task_known : @logic.KnownMap?
  task_clone : Array[(TheoryKey, TDeclSet)]
  task_meta : Array[(Meta, TDeclSet)]
}

///|
pub(all) struct TaskHeadView {
  task_decl : TDecl
  task_prev : TaskHead?
  task_known : @logic.KnownMap?
  task_clone : ArrayView[(TheoryKey, TDeclSet)]
  task_meta : ArrayView[(Meta, TDeclSet)]
}

///|
struct Task {
  anchor : @identity.SemanticId
  task_hd : TaskHead
  items : Array[TheoryItem]
  dependencies : Array[(TheoryKey, Theory)]
}

///|
pub(all) struct TaskView {
  items : ArrayView[TheoryItem]
  task_hd : TaskHead?
  dependencies : ArrayView[(TheoryKey, Theory)]
}

///|
pub fn Task::context_anchor(self : Task) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn Task::view(self : Task) -> TaskView {
  {
    items: self.items[:],
    task_hd: Some(self.task_hd),
    dependencies: self.dependencies[:],
  }
}

///|
pub fn Task::dependency_theories(self : Task) -> ArrayView[(TheoryKey, Theory)] {
  self.dependencies[:]
}

///|
pub fn Task::referenced_theory(self : Task, key : TheoryKey) -> Theory? {
  for entry in self.dependencies {
    if entry.0 == key {
      return Some(entry.1)
    }
  }
  None
}

///|
pub fn Task::head(self : Task) -> TaskHead? {
  Some(self.task_hd)
}

///|
pub fn TaskHead::view(self : TaskHead) -> TaskHeadView {
  {
    task_decl: self.task_decl,
    task_prev: self.task_prev,
    task_known: self.task_known,
    task_clone: self.task_clone[:],
    task_meta: self.task_meta[:],
  }
}

///|
fn declaration_is_goal(declaration : @logic.Decl) -> Bool {
  declaration.view() is Dprop(Pgoal, _, _)
}

///|
fn validate_task_items(
  items : ArrayView[TheoryItem],
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  let mut goals = 0
  for index, item in items {
    if item is TheoryDecl(declaration) && declaration_is_goal(declaration) {
      goals = goals + 1
      if index + 1 != items.length() {
        fail_theory(GoalNotLast, span, "task goal must be the final item")
      }
    }
  }
  if goals == 0 {
    fail_theory(MissingGoal, span, "task has no goal")
  }
  if goals > 1 {
    fail_theory(MultipleGoals, span, "task contains multiple goals")
  }
}

///|
fn same_meta_descriptor(left : Meta, right : Meta) -> Bool {
  let left_view = left.view()
  let right_view = right.view()
  left_view.name == right_view.name &&
  left_view.argument_types == right_view.argument_types &&
  left_view.exclusive == right_view.exclusive
}

///|
fn clone_history_add(
  history : ArrayView[(TheoryKey, TDeclSet)],
  key : TheoryKey,
  item : TheoryItem,
) -> Array[(TheoryKey, TDeclSet)] {
  let result = history.to_owned()
  for index, entry in result {
    if entry.0 == key {
      let declarations = entry.1.tds_set.copy()
      declarations.push(item)
      result[index] = (key, { tds_set: declarations })
      return result
    }
  }
  result.push((key, { tds_set: [item] }))
  result
}

///|
fn meta_history_add(
  history : ArrayView[(Meta, TDeclSet)],
  meta : Meta,
  item : TheoryItem,
) -> Array[(Meta, TDeclSet)] {
  let result = history.to_owned()
  for index, entry in result {
    if same_meta_descriptor(entry.0, meta) {
      if meta.view().exclusive {
        result[index] = (meta, { tds_set: [item] })
      } else {
        let declarations = entry.1.tds_set.copy()
        declarations.push(item)
        result[index] = (entry.0, { tds_set: declarations })
      }
      return result
    }
  }
  result.push((meta, { tds_set: [item] }))
  result
}

///|
fn next_task_head(
  previous : TaskHead?,
  item : TheoryItem,
  known : @logic.KnownMap?,
) -> TaskHead {
  let mut clone_history : Array[(TheoryKey, TDeclSet)] = []
  let mut meta_history : Array[(Meta, TDeclSet)] = []
  match previous {
    Some(previous) => {
      clone_history = previous.task_clone.copy()
      meta_history = previous.task_meta.copy()
    }
    None => ()
  }
  match item {
    TheoryUse(key) =>
      clone_history = clone_history_add(clone_history, key, item)
    TheoryClone(witness) =>
      clone_history = clone_history_add(
        clone_history,
        witness.view().source,
        item,
      )
    TheoryMeta(meta) =>
      meta_history = meta_history_add(meta_history, meta, item)
    TheoryDecl(_) => ()
  }
  {
    task_decl: TDecl::from_item(item),
    task_prev: previous,
    task_known: known,
    task_clone: clone_history,
    task_meta: meta_history,
  }
}

///|
fn build_unchecked_task_head(items : ArrayView[TheoryItem]) -> TaskHead {
  let mut head : TaskHead? = None
  for item in items {
    head = Some(next_task_head(head, item, None))
  }
  guard head is Some(head) else {
    abort("validated non-empty task lost its final declaration")
  }
  head
}

///|
fn build_checked_task_head(
  context : @identity.CompilationContext,
  items : ArrayView[TheoryItem],
  span : @identity.SourceSpan?,
) -> TaskHead raise {
  let mut known = @logic.KnownMap::new(context)
  let mut head : TaskHead? = None
  for item in items {
    if item is TheoryDecl(declaration) {
      known = known.add(declaration, span)
    }
    head = Some(next_task_head(head, item, Some(known)))
  }
  guard head is Some(head) else {
    abort("validated non-empty task lost its final declaration")
  }
  head
}

///|
pub fn Task::trusted_new(
  anchor : @identity.SemanticId,
  items : ArrayView[TheoryItem],
  span : @identity.SourceSpan?,
) -> Task raise TheoryError {
  Task::trusted_new_with_dependencies(anchor, items, [], span)
}

///|
pub fn Task::trusted_new_with_dependencies(
  anchor : @identity.SemanticId,
  items : ArrayView[TheoryItem],
  dependencies : ArrayView[(TheoryKey, Theory)],
  span : @identity.SourceSpan?,
) -> Task raise TheoryError {
  validate_task_items(items, span)
  {
    anchor,
    task_hd: build_unchecked_task_head(items),
    items: items.to_owned(),
    dependencies: dependencies.to_owned(),
  }
}

///|
fn Task::checked_new(
  context : @identity.CompilationContext,
  anchor : @identity.SemanticId,
  items : ArrayView[TheoryItem],
  dependencies : ArrayView[(TheoryKey, Theory)],
  span : @identity.SourceSpan?,
) -> Task raise {
  validate_task_items(items, span)
  {
    anchor,
    task_hd: build_checked_task_head(context, items, span),
    items: items.to_owned(),
    dependencies: dependencies.to_owned(),
  }
}

///|
pub fn Task::goal(self : Task) -> @logic.PrSymbol raise TheoryError {
  match self.task_hd.task_decl {
    { td_node: TheoryDecl(declaration) } =>
      match declaration.view() {
        Dprop(Pgoal, proposition, _) => proposition
        _ => fail_theory(MissingGoal, None, "task has no final goal")
      }
    _ => fail_theory(MissingGoal, None, "task has no final goal")
  }
}

///|
pub fn Task::goal_formula(self : Task) -> @logic.Term raise TheoryError {
  match self.task_hd.task_decl {
    { td_node: TheoryDecl(declaration) } =>
      match declaration.view() {
        Dprop(Pgoal, _, formula) => formula
        _ => fail_theory(MissingGoal, None, "task has no final goal")
      }
    _ => fail_theory(MissingGoal, None, "task has no final goal")
  }
}

///|
pub fn Task::known(self : Task) -> @logic.KnownMap? {
  self.task_hd.task_known
}

///|
pub fn Task::clone_history(self : Task, source : Theory) -> TDeclSet {
  for entry in self.task_hd.task_clone {
    if entry.0 == source.key {
      return entry.1
    }
  }
  { tds_set: [] }
}

///|
pub fn Task::meta_history(self : Task, meta : Meta) -> TDeclSet {
  for entry in self.task_hd.task_meta {
    if same_meta_descriptor(entry.0, meta) {
      return entry.1
    }
  }
  { tds_set: [] }
}

///|
pub fn Task::meta_applications(
  self : Task,
  meta : Meta,
) -> Array[Array[MetaArgument]] {
  let result : Array[Array[MetaArgument]] = []
  for item in self.meta_history(meta).tds_set {
    if item is TheoryMeta(application) {
      result.push(application.view().arguments.to_owned())
    }
  }
  result
}

///|
pub fn Task::exclusive_meta(
  self : Task,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Array[MetaArgument]? raise TheoryError {
  if !meta.view().exclusive {
    fail_theory(
      NotExclusiveMeta,
      span,
      "exclusive-meta lookup requires an exclusive meta descriptor",
    )
  }
  let applications = self.meta_applications(meta)
  match applications.last() {
    Some(arguments) => Some(arguments)
    None => None
  }
}

///|
pub fn Task::cloned_theory_maps(
  self : Task,
  source : Theory,
) -> Array[SymbolMap] {
  let result : Array[SymbolMap] = []
  for item in self.clone_history(source).tds_set {
    if item is TheoryClone(witness) {
      result.push(witness.symbol_map())
    }
  }
  result
}

///|
pub fn Task::uses_theory(self : Task, source : Theory) -> Bool {
  self.clone_history(source).tds_set.any(item => item is TheoryUse(_))
}

///|
fn require_tagging_meta(
  meta : Meta,
  expected : MetaArgumentType,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  let argument_types = meta.view().argument_types
  guard !argument_types.is_empty() && argument_types[0] == expected else {
    fail_theory(
      NotTaggingMeta,
      span,
      "meta does not tag the requested kind of semantic object",
    )
  }
}

///|
pub fn Task::tagged_types(
  self : Task,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Array[@logic.Ty] raise TheoryError {
  require_tagging_meta(meta, MetaTypeArgument, span)
  let seen : Map[@logic.Ty, Unit] = Map([])
  let result : Array[@logic.Ty] = []
  for arguments in self.meta_applications(meta) {
    if !arguments.is_empty() &&
      arguments[0] is MetaType(ty) &&
      !seen.contains(ty) {
      seen[ty] = ()
      result.push(ty)
    }
  }
  result
}

///|
pub fn Task::tagged_type_symbols(
  self : Task,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Array[@logic.TypeSymbol] raise TheoryError {
  require_tagging_meta(meta, MetaTypeSymbolArgument, span)
  let seen : Map[@logic.TypeSymbol, Unit] = Map([])
  let result : Array[@logic.TypeSymbol] = []
  for arguments in self.meta_applications(meta) {
    if !arguments.is_empty() &&
      arguments[0] is MetaTypeSymbol(symbol) &&
      !seen.contains(symbol) {
      seen[symbol] = ()
      result.push(symbol)
    }
  }
  result
}

///|
pub fn Task::tagged_logic_symbols(
  self : Task,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Array[@logic.LSymbol] raise TheoryError {
  require_tagging_meta(meta, MetaLogicSymbolArgument, span)
  let seen : Map[@logic.LSymbol, Unit] = Map([])
  let result : Array[@logic.LSymbol] = []
  for arguments in self.meta_applications(meta) {
    if !arguments.is_empty() &&
      arguments[0] is MetaLogicSymbol(symbol) &&
      !seen.contains(symbol) {
      seen[symbol] = ()
      result.push(symbol)
    }
  }
  result
}

///|
pub fn Task::tagged_propositions(
  self : Task,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Array[@logic.PrSymbol] raise TheoryError {
  require_tagging_meta(meta, MetaPropositionSymbolArgument, span)
  let seen : Map[@logic.PrSymbol, Unit] = Map([])
  let result : Array[@logic.PrSymbol] = []
  for arguments in self.meta_applications(meta) {
    if !arguments.is_empty() &&
      arguments[0] is MetaPropositionSymbol(symbol) &&
      !seen.contains(symbol) {
      seen[symbol] = ()
      result.push(symbol)
    }
  }
  result
}

///|
priv struct TaskAccumulator {
  context : @identity.CompilationContext
  items : Array[TheoryItem]
  seen_symbols : Map[@identity.SemanticId, Unit]
  seen_uses : Map[TheoryKey, Unit]
  dependencies : Array[(TheoryKey, Theory)]
}

///|
fn TaskAccumulator::new(
  context : @identity.CompilationContext,
) -> TaskAccumulator {
  {
    context,
    items: [],
    seen_symbols: Map([]),
    seen_uses: Map([]),
    dependencies: [],
  }
}

///|
fn TaskAccumulator::remember_theory(
  self : TaskAccumulator,
  theory : Theory,
) -> Unit {
  if !self.dependencies.any(entry => entry.0 == theory.key) {
    self.dependencies.push((theory.key, theory))
  }
}

///|
fn TaskAccumulator::add_declaration(
  self : TaskAccumulator,
  declaration : @logic.Decl,
) -> Unit {
  let introduced = declaration.introduced_symbols()
  if introduced.any(symbol => self.seen_symbols.contains(symbol.semantic_id())) {
    return
  }
  for symbol in introduced {
    self.seen_symbols[symbol.semantic_id()] = ()
  }
  self.items.push(TheoryDecl(declaration))
}

///|
fn TaskAccumulator::add_imported_declaration(
  self : TaskAccumulator,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  match declaration.view() {
    Dprop(Plemma, _, _) =>
      self.add_declaration(
        declaration.reclassify_proposition(self.context, Paxiom, span),
      )
    Dprop(Pgoal, _, _) => ()
    _ => self.add_declaration(declaration)
  }
}

///|
fn TaskAccumulator::flatten_use(
  self : TaskAccumulator,
  theory : Theory,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let key = theory.key
  self.remember_theory(theory)
  if self.seen_uses.contains(key) {
    return
  }
  self.seen_uses[key] = ()
  for item in theory.items {
    match item {
      TheoryDecl(declaration) =>
        self.add_imported_declaration(declaration, span)
      TheoryUse(used_key) =>
        self.flatten_use(theory.used_theory(used_key), span)
      TheoryClone(witness) => {
        if theory.clone_source(witness.view().source) is Some(source) {
          self.remember_theory(source)
        }
        self.items.push(TheoryClone(witness))
      }
      TheoryMeta(meta) => self.items.push(TheoryMeta(meta))
    }
  }
  self.items.push(TheoryUse(key))
}

///|
fn collect_clone_facts(
  theory : Theory,
  witness : CloneWitness,
  facts : Map[@logic.PrSymbol, Unit],
  span : @identity.SourceSpan?,
) -> Unit raise {
  guard theory.clone_source(witness.view().source) is Some(source) else {
    // A directly constructed portable clone witness may omit the optional
    // source graph. The witness remains valid, but there is no source
    // proposition classification available for the proved-fact optimization.
    return
  }
  for entry in witness.symbol_map().view().sm_pr {
    let (kind, _) = source.known.find_proposition(entry.0, span)
    if kind is Plemma || kind is Pgoal {
      facts[entry.1] = ()
    }
  }
}

///|
pub fn split_theory(
  context : @identity.CompilationContext,
  theory : Theory,
  span : @identity.SourceSpan?,
) -> Array[Task] raise {
  if !context.contains(theory.anchor) {
    fail_theory(ContextMismatch, span, "theory belongs to another context")
  }
  let prefix = TaskAccumulator::new(context)
  let facts : Map[@logic.PrSymbol, Unit] = Map([])
  let candidates : Array[(@logic.PrSymbol, Array[TheoryItem])] = []
  for item in theory.items {
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dprop(Plemma, proposition, _) => {
            let task_items = prefix.items.copy()
            task_items.push(
              TheoryDecl(
                declaration.reclassify_proposition(context, Pgoal, span),
              ),
            )
            candidates.push((proposition, task_items))
            prefix.add_declaration(
              declaration.reclassify_proposition(context, Paxiom, span),
            )
          }
          Dprop(Pgoal, proposition, _) => {
            let task_items = prefix.items.copy()
            task_items.push(item)
            candidates.push((proposition, task_items))
          }
          _ => prefix.add_declaration(declaration)
        }
      TheoryUse(key) => prefix.flatten_use(theory.used_theory(key), span)
      TheoryClone(witness) => {
        collect_clone_facts(theory, witness, facts, span)
        if theory.clone_source(witness.view().source) is Some(source) {
          prefix.remember_theory(source)
        }
        prefix.items.push(TheoryClone(witness))
      }
      TheoryMeta(meta) => prefix.items.push(TheoryMeta(meta))
    }
  }
  let tasks : Array[Task] = []
  for candidate in candidates {
    if !facts.contains(candidate.0) {
      tasks.push(
        Task::checked_new(
          context,
          theory.anchor,
          candidate.1,
          prefix.dependencies,
          span,
        ),
      )
    }
  }
  tasks
}

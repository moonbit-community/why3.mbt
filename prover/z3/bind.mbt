// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct TypedDriverMeta {
  meta : @theory.Meta
}

///|
priv struct TypedMetaGroup {
  theory_key : @theory.TheoryKey
  entries : Array[TypedDriverMeta]
}

///|
priv enum TypedSyntaxSymbol {
  TypedSyntaxType(@logic.TypeSymbol)
  TypedSyntaxLogic(@logic.LSymbol)
}

///|
priv struct TypedSyntaxEntry {
  kind : SyntaxKind
  symbol : TypedSyntaxSymbol
  template : Bytes
  overriding : Bool
}

///|
pub(all) enum Z3SyntaxSymbol {
  Z3SyntaxType(@logic.TypeSymbol)
  Z3SyntaxLogic(@logic.LSymbol)
}

///|
pub(all) struct Z3SyntaxEntry {
  kind : SyntaxKind
  symbol : Z3SyntaxSymbol
  template : Bytes
  overriding : Bool
}

///|
struct Z3Profile {
  anchor : @identity.SemanticId
  transforms : Array[TransformId]
  meta_groups : Array[TypedMetaGroup]
  snapshot_meta_groups : Array[TypedMetaGroup]
  syntax : Array[TypedSyntaxEntry]
  remove : Array[@logic.PrSymbol]
  preludes : Array[Bytes]
  theory_preludes : Array[TheoryPrelude]
  result_regexps : Array[ResultRegexp]
  result_exit_codes : Array[ResultExitCode]
  command : Z3CommandTemplate
  monomorphic_checkpoints : Array[Bytes]
  polymorphic_checkpoints : Array[Bytes]
}

///|
pub(all) struct Z3ProfileView {
  context_anchor : @identity.SemanticId
  transforms : ArrayView[TransformId]
  driver_meta_group_count : Int
  driver_meta_count : Int
  validated_snapshot_meta_count : Int
  syntax_count : Int
  remove_count : Int
  preludes : ArrayView[Bytes]
  theory_prelude_count : Int
  result_regexp_count : Int
  result_exit_code_count : Int
  command : Z3CommandTemplate
}

///|
fn typed_meta_count(groups : ArrayView[TypedMetaGroup]) -> Int {
  let mut count = 0
  for group in groups {
    count = count + group.entries.length()
  }
  count
}

///|
pub fn Z3Profile::view(self : Z3Profile) -> Z3ProfileView {
  {
    context_anchor: self.anchor,
    transforms: self.transforms[:],
    driver_meta_group_count: self.meta_groups.length(),
    driver_meta_count: typed_meta_count(self.meta_groups),
    validated_snapshot_meta_count: typed_meta_count(self.snapshot_meta_groups),
    syntax_count: self.syntax.length(),
    remove_count: self.remove.length(),
    preludes: self.preludes[:],
    theory_prelude_count: self.theory_preludes.length(),
    result_regexp_count: self.result_regexps.length(),
    result_exit_code_count: self.result_exit_codes.length(),
    command: self.command,
  }
}

///|
pub fn Z3Profile::syntax_entries(self : Z3Profile) -> Array[Z3SyntaxEntry] {
  self.syntax.map(entry => {
    let symbol = match entry.symbol {
      TypedSyntaxType(symbol) => Z3SyntaxType(symbol)
      TypedSyntaxLogic(symbol) => Z3SyntaxLogic(symbol)
    }
    {
      kind: entry.kind,
      symbol,
      template: entry.template,
      overriding: entry.overriding,
    }
  })
}

///|
pub fn Z3Profile::builtin_type(
  self : Z3Profile,
  kind : @logic.BuiltinTypeKind,
) -> @logic.TypeSymbol? {
  for entry in self.syntax {
    if entry.symbol is TypedSyntaxType(symbol) &&
      symbol.builtin_kind() == Some(kind) {
      return Some(symbol)
    }
  }
  None
}

///|
pub fn Z3Profile::result_regexp_rules(
  self : Z3Profile,
) -> Array[ResultRegexpView] {
  self.result_regexps.map(rule => rule.view())
}

///|
pub fn Z3Profile::result_exit_code_rules(
  self : Z3Profile,
) -> Array[ResultExitCodeView] {
  self.result_exit_codes.map(rule => rule.view())
}

///|
fn bind_unbound_ty(
  ty : UnboundTy,
  resolver : DriverSymbolResolver,
  context : @identity.CompilationContext,
  variables : Map[Bytes, @logic.TyVarSymbol],
  path : String,
) -> @logic.Ty raise BindError {
  match ty {
    UnboundTyVariable(name) => {
      let variable = match variables.get(name) {
        Some(variable) => variable
        None => {
          let variable = @logic.TyVarSymbol::new(
            context,
            name,
            @identity.Origin::generated(DriverUpdate, name, None, []),
          )
          variables[name] = variable
          variable
        }
      }
      @logic.Ty::variable(variable)
    }
    UnboundTyApplication(key, arguments) => {
      let symbol = resolver.resolve_type(key, path=path + ".symbol")
      let typed : Array[@logic.Ty] = []
      for index, argument in arguments {
        typed.push(
          bind_unbound_ty(
            argument,
            resolver,
            context,
            variables,
            path + ".arguments[" + index.to_string() + "]",
          ),
        )
      }
      @logic.Ty::app(symbol, typed, None) catch {
        _ => fail_bind(InvalidProfile, path, "invalid bound driver meta type")
      }
    }
  }
}

///|
fn bind_meta_argument(
  argument : UnboundMetaArgument,
  resolver : DriverSymbolResolver,
  context : @identity.CompilationContext,
  variables : Map[Bytes, @logic.TyVarSymbol],
  path : String,
) -> @theory.MetaArgument raise BindError {
  match argument {
    UnboundMetaType(ty) =>
      MetaType(bind_unbound_ty(ty, resolver, context, variables, path))
    UnboundMetaTypeSymbol(key) =>
      MetaTypeSymbol(resolver.resolve_type(key, path~))
    UnboundMetaLogicSymbol(key) =>
      MetaLogicSymbol(resolver.resolve_logic(key, path~))
    UnboundMetaPropositionSymbol(key) =>
      MetaPropositionSymbol(resolver.resolve_proposition(key, path~))
    UnboundMetaString(value) => MetaString(value)
    UnboundMetaInteger(value) => MetaInteger(value)
    UnboundMetaIdentifier(name) =>
      MetaIdentifier(@theory.SemanticName::new(name, [], None))
  }
}

///|
fn bind_meta_groups(
  groups : ArrayView[UnboundMetaGroup],
  resolver : DriverSymbolResolver,
  context : @identity.CompilationContext,
  path : String,
) -> Array[TypedMetaGroup] raise BindError {
  let result : Array[TypedMetaGroup] = []
  for group_index, group in groups {
    let entries : Array[TypedDriverMeta] = []
    for entry_index, entry in group.entries {
      let variables : Map[Bytes, @logic.TyVarSymbol] = Map([])
      let arguments : Array[@theory.MetaArgument] = []
      for argument_index, argument in entry.arguments {
        arguments.push(
          bind_meta_argument(
            argument,
            resolver,
            context,
            variables,
            path +
            "[" +
            group_index.to_string() +
            "].entries[" +
            entry_index.to_string() +
            "].arguments[" +
            argument_index.to_string() +
            "]",
          ),
        )
      }
      let meta = @theory.Meta::new(entry.name, arguments)
      meta.validate_context(resolver.context_anchor(), None) catch {
        _ =>
          fail_bind(
            ContextMismatch,
            path + "[" + group_index.to_string() + "]",
            "bound meta combines compilation contexts",
          )
      }
      entries.push({ meta, })
    }
    result.push({ theory_key: group.theory_key, entries })
  }
  result
}

///|
pub fn bind_profile(
  spec : Z3StaticSpec,
  resolver : DriverSymbolResolver,
  context : @identity.CompilationContext,
) -> Z3Profile raise BindError {
  if !context.contains(resolver.context_anchor()) {
    fail_bind(
      ContextMismatch,
      "$.resolver",
      "resolver belongs to another context",
    )
  }
  let meta_groups = bind_meta_groups(
    spec.meta_groups,
    resolver,
    context,
    "$.driverMetaGroups",
  )
  let snapshot_meta_groups = bind_meta_groups(
    spec.snapshot_meta_groups,
    resolver,
    context,
    "$.snapshotMetaClosure",
  )
  let syntax : Array[TypedSyntaxEntry] = []
  for index, entry in spec.syntax {
    let path = "$.syntax[" + index.to_string() + "]"
    let symbol = match entry.kind {
      TypeSyntax | LiteralSyntax =>
        TypedSyntaxType(resolver.resolve_type(entry.symbol, path~))
      LogicSyntax =>
        TypedSyntaxLogic(resolver.resolve_logic(entry.symbol, path~))
    }
    syntax.push({
      kind: entry.kind,
      symbol,
      template: entry.template,
      overriding: entry.overriding,
    })
  }
  let remove : Array[@logic.PrSymbol] = []
  for index, key in spec.remove {
    remove.push(
      resolver.resolve_proposition(
        key,
        path="$.remove[" + index.to_string() + "]",
      ),
    )
  }
  {
    anchor: resolver.context_anchor(),
    transforms: spec.transforms.copy(),
    meta_groups,
    snapshot_meta_groups,
    syntax,
    remove,
    preludes: spec.preludes.copy(),
    theory_preludes: spec.theory_preludes.map(group => {
      theory_key: group.theory_key,
      values: group.values.copy(),
    }),
    result_regexps: spec.result_regexps.copy(),
    result_exit_codes: spec.result_exit_codes.copy(),
    command: spec.command,
    monomorphic_checkpoints: spec.monomorphic_checkpoints.copy(),
    polymorphic_checkpoints: spec.polymorphic_checkpoints.copy(),
  }
}

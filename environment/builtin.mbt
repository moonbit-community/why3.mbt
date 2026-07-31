// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn language_builtin_key(name : BytesView) -> @theory.TheoryKey raise {
  @theory.TheoryKey::new([b"why3", name.to_owned()], name)
}

///|
fn language_builtin_origin(
  name : BytesView,
  attributes? : ArrayView[Bytes] = [],
) -> @identity.Origin {
  @identity.Origin::user(name, None, attributes)
}

///|
fn primitive_program_type(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
  origin : @identity.Origin,
) -> @mlw.ProgramTypeSymbol raise {
  @mlw.ProgramTypeSymbol::new(
    context,
    symbol,
    origin,
    {
      nonfree: true,
      private_: true,
      mutable_: false,
      fragile: false,
      argument_flags: [],
      region_flags: [],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
}

///|
fn build_language_builtin_module(
  context : @identity.CompilationContext,
) -> @mlw.Pmodule raise {
  let name = b"BuiltIn"
  let builder = @mlw.PmoduleBuilder::new(
    context,
    language_builtin_key(name),
    @theory.SemanticName::new(name, [], None),
  )
  for
    entry in [
      (b"int", @logic.BuiltinInteger),
      (b"real", @logic.BuiltinReal),
      (b"string", @logic.BuiltinString),
    ] {
    let origin = language_builtin_origin(entry.0)
    let logical = @logic.TypeSymbol::new_builtin(
      context,
      entry.0,
      origin,
      entry.1,
    )
    let pure = @logic.Decl::type_declaration(context, origin, [logical], None)
    builder.add_type_declarations(
      [
        @mlw.ProgramTypeDeclaration::simple(
          primitive_program_type(context, logical, origin),
        ),
      ],
      [pure],
      [],
      None,
    )
  }
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    language_builtin_origin(b"a"),
  )
  let parameter_ty = @logic.Ty::variable(parameter)
  let equality_origin = language_builtin_origin(b"infix =", attributes=[
    b"builtin", b"why3:builtin:equality",
  ])
  let equality = @logic.LSymbol::new_predicate(
    context,
    b"infix =",
    equality_origin,
    [parameter_ty, parameter_ty],
    None,
  )
  builder.add_pure_decl(
    @logic.Decl::parameter(context, equality_origin, equality, None),
    None,
  )
  builder.close()
}

///|
fn build_language_ignore_module(
  context : @identity.CompilationContext,
) -> @mlw.Pmodule raise {
  let name = b"Ignore"
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    language_builtin_origin(b"a"),
  )
  let origin = language_builtin_origin(b"ignore'term")
  let ignore_symbol = @logic.LSymbol::new_predicate(
    context,
    b"ignore'term",
    origin,
    [@logic.Ty::variable(parameter)],
    None,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    language_builtin_key(name),
    @theory.SemanticName::new(name, [], None),
  )
  builder.add_pure_decl(
    @logic.Decl::parameter(context, origin, ignore_symbol, None),
    None,
  )
  builder.close()
}

///|
fn constructor_postcondition(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  constructor_symbol : @logic.LSymbol,
  result_type : @logic.Ty,
) -> @mlw.Postcondition raise {
  let result = @logic.VSymbol::new(
    context,
    b"result",
    language_builtin_origin(b"result"),
    result_type,
    None,
  )
  @mlw.Postcondition::trusted_new(
    result,
    @logic.Term::apply_predicate(
      equality,
      [
        @logic.Term::variable(result),
        @logic.Term::apply_function(constructor_symbol, [], None),
      ],
      None,
    ),
    None,
  )
}

///|
fn build_language_bool_module(
  context : @identity.CompilationContext,
  builtin_module : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  let name = b"Bool"
  let origin = language_builtin_origin(b"bool")
  let logical = @logic.TypeSymbol::new_builtin(
    context,
    b"bool",
    origin,
    @logic.BuiltinBoolean,
  )
  let logical_ty = @logic.Ty::app(logical, [], None)
  let true_origin = language_builtin_origin(b"True", attributes=[
    b"builtin", b"why3:builtin:boolean:true",
  ])
  let false_origin = language_builtin_origin(b"False", attributes=[
    b"builtin", b"why3:builtin:boolean:false",
  ])
  let true_logic = @logic.LSymbol::new_constructor(
    context,
    b"True",
    true_origin,
    [],
    logical_ty,
    2,
    None,
  )
  let false_logic = @logic.LSymbol::new_constructor(
    context,
    b"False",
    false_origin,
    [],
    logical_ty,
    2,
    None,
  )
  let pure = @logic.Decl::data(
    context,
    origin,
    [
      @logic.DataDeclaration::new(
        logical,
        [
          @logic.DataConstructor::new(true_logic, [], None),
          @logic.DataConstructor::new(false_logic, [], None),
        ],
        None,
      ),
    ],
    None,
  )
  let program = @mlw.ProgramTypeSymbol::new_recursive(
    context,
    logical,
    origin,
    None,
  )
  let program_ty = @mlw.Ity::app(program, [], None)
  let equality = builtin_module
    .pure_theory()
    .export_namespace()
    .find_logic([b"infix ="], None)
  let true_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    b"True",
    true_origin,
    @mlw.Cty::new(
      [],
      [],
      [constructor_postcondition(context, equality, true_logic, logical_ty)],
      [],
      [],
      @mlw.Effect::pure(false),
      program_ty,
      None,
    ),
    RLls(true_logic),
    None,
    None,
  )
  let false_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    b"False",
    false_origin,
    @mlw.Cty::new(
      [],
      [],
      [constructor_postcondition(context, equality, false_logic, logical_ty)],
      [],
      [],
      @mlw.Effect::pure(false),
      program_ty,
      None,
    ),
    RLls(false_logic),
    None,
    None,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    language_builtin_key(name),
    @theory.SemanticName::new(name, [], None),
  )
  builder.add_type_declarations(
    [
      @mlw.ProgramTypeDeclaration::new(
        program,
        [],
        [true_routine, false_routine],
        [],
        None,
      ),
    ],
    [pure],
    [],
    None,
  )
  builder.close()
}

///|
fn tuple_builtin_name(arity : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"Tuple")
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn tuple_builtin_key(arity : Int) -> @theory.TheoryKey raise {
  let name = tuple_builtin_name(arity)
  @theory.TheoryKey::new([b"why3", name], name)
}

///|
fn tuple_type_name(arity : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"tuple")
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn tuple_type_origin(arity : Int) -> @identity.Origin {
  let name = tuple_type_name(arity)
  @identity.Origin::user(name, None, [b"builtin", b"why3:builtin:tuple-type"])
}

///|
fn tuple_constructor_origin(arity : Int) -> @identity.Origin {
  let name = tuple_builtin_name(arity)
  @identity.Origin::user(name, None, [
    b"builtin", b"why3:builtin:tuple-constructor",
  ])
}

///|
fn build_tuple_module(
  context : @identity.CompilationContext,
  arity : Int,
  equality : @logic.LSymbol,
) -> @mlw.Pmodule raise {
  let name = tuple_builtin_name(arity)
  let origin = tuple_type_origin(arity)
  let constructor_origin = tuple_constructor_origin(arity)
  let created_type_variables : Array[@logic.TyVarSymbol] = []
  for index = 0; index < arity; index = index + 1 {
    created_type_variables.push(
      @logic.TyVarSymbol::new(
        context,
        b"a",
        @identity.Origin::user(b"a", None, []),
      ),
    )
  }
  let type_variables : Array[@logic.TyVarSymbol] = []
  for reverse_index = 0
      reverse_index < created_type_variables.length()
      reverse_index = reverse_index + 1 {
    type_variables.push(
      created_type_variables[created_type_variables.length() - reverse_index - 1],
    )
  }
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    tuple_type_name(arity),
    origin,
    type_variables,
    None,
  )
  let logical_arguments = type_variables.map(@logic.Ty::variable)
  let logical_result = @logic.Ty::app(type_symbol, logical_arguments, None)
  let constructor_symbol = @logic.LSymbol::new_constructor(
    context,
    name,
    constructor_origin,
    logical_arguments,
    logical_result,
    1,
    None,
  )
  let pure_declaration = @logic.Decl::data(
    context,
    origin,
    [
      @logic.DataDeclaration::new(
        type_symbol,
        [
          @logic.DataConstructor::new(
            constructor_symbol,
            [
              for _ in logical_arguments => None
            ],
            None,
          ),
        ],
        None,
      ),
    ],
    None,
  )

  let program_arguments : Array[@mlw.PVariable] = []
  let program_type_arguments = type_variables.map(@mlw.Ity::variable)
  for argument_type in program_type_arguments {
    program_arguments.push(
      @mlw.PVariable::trusted_new(
        context,
        @theory.SemanticName::new(b"a", [], None),
        argument_type,
        false,
        None,
      ),
    )
  }
  let program_type = @mlw.ProgramTypeSymbol::new_variant(
    context,
    type_symbol,
    origin,
    [program_arguments],
    None,
  )
  let program_result = @mlw.Ity::app(program_type, program_type_arguments, None)
  let constructor_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    name,
    constructor_origin,
    @mlw.Cty::new(
      program_arguments,
      [],
      [
        {
          let result = @logic.VSymbol::new(
            context,
            b"result",
            language_builtin_origin(b"result"),
            logical_result,
            None,
          )
          @mlw.Postcondition::trusted_new(
            result,
            @logic.Term::apply_predicate(
              equality,
              [
                @logic.Term::variable(result),
                @logic.Term::apply_function(
                  constructor_symbol,
                  program_arguments.map(argument => {
                    @logic.Term::variable(argument.view().pure_symbol)
                  }),
                  None,
                ),
              ],
              None,
            ),
            None,
          )
        },
      ],
      [],
      [],
      @mlw.Effect::pure(false),
      program_result,
      None,
    ),
    RLls(constructor_symbol),
    None,
    None,
  )
  let program_declaration = @mlw.ProgramTypeDeclaration::trusted_new(
    program_type,
    [],
    [constructor_routine],
    [],
    None,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    tuple_builtin_key(arity),
    @theory.SemanticName::new(name, [b"builtin"], None),
  )
  builder.add_type_declarations(
    [program_declaration],
    [pure_declaration],
    [],
    None,
  )
  builder.close()
}

///|
pub fn Environment::tuple_module(
  self : Environment,
  arity : Int,
  span? : @identity.SourceSpan? = None,
) -> @mlw.Pmodule raise {
  if arity < 0 {
    fail_environment(ResolveError, span, "tuple arity must be non-negative")
  }
  match self.tuple_modules.get(arity) {
    Some(pmodule) => return pmodule
    None => ()
  }
  let key = tuple_builtin_key(arity)
  let pmodule = match self.modules.get(key) {
    Some(existing) => existing
    None => {
      let equality = self
        .resolve_module(@theory.TheoryKey::new([], b"BuiltIn"), span)
        .pure_theory()
        .export_namespace()
        .find_logic([b"infix ="], span)
      build_tuple_module(self.context, arity, equality)
    }
  }
  self.tuple_modules[arity] = pmodule
  pmodule
}

///|
fn canonical_tuple_builtin_arity(name : BytesView) -> Int? {
  if !name.has_prefix(b"Tuple") || name.length() == 5 {
    return None
  }
  let digits = name[5:]
  if digits.length() > 1 && digits[0] == b'0' {
    return None
  }
  let mut arity = 0
  for digit in digits {
    if digit < b'0' || digit > b'9' || arity > 100000 {
      return None
    }
    arity = arity * 10 + (digit - b'0').to_int()
  }
  Some(arity)
}

///|
fn Environment::tuple_builtin_library(
  self : Environment,
  path : @env.LibraryPath,
) -> TypedLibrary? raise {
  guard path.without_builtin_prefix() is Some(relative) else { return None }
  let segments = relative.view().segments
  guard segments is [name] && canonical_tuple_builtin_arity(name) is Some(arity) else {
    return None
  }
  let pmodule = self.tuple_module(arity)
  Some(TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]))
}

///|
fn build_language_unit_module(
  context : @identity.CompilationContext,
  builtin_module : @mlw.Pmodule,
  tuple_module : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  let name = b"Unit"
  let origin = language_builtin_origin(b"unit", attributes=[b"builtin"])
  let tuple_logic = tuple_module
    .pure_theory()
    .export_namespace()
    .find_type([b"tuple0"], None)
  let tuple_program = tuple_module
    .export_namespace()
    .find_type([b"tuple0"], None)
  let tuple_ty = @logic.Ty::app(tuple_logic, [], None)
  let logical = @logic.TypeSymbol::new_alias(
    context,
    b"unit",
    origin,
    [],
    tuple_ty,
    None,
  )
  let program = @mlw.ProgramTypeSymbol::new_alias(
    context,
    logical,
    origin,
    @mlw.Ity::app(tuple_program, [], None),
    None,
  )
  let pure = @logic.Decl::type_declaration(context, origin, [logical], None)
  let builder = @mlw.PmoduleBuilder::new(
    context,
    language_builtin_key(name),
    @theory.SemanticName::new(name, [], None),
  )
  builder.add_pure_use(builtin_module.pure_theory(), true, None)
  builder.add_use(tuple_module, true, None)
  builder.add_type_declarations(
    [@mlw.ProgramTypeDeclaration::simple(program)],
    [pure],
    [],
    None,
  )
  builder.close()
}

///|
fn Environment::register_language_builtin(
  self : Environment,
  pmodule : @mlw.Pmodule,
  short_alias : Bool,
) -> Unit raise {
  let key = pmodule.key()
  let name = key.view().name
  self.register_typed_library(
    TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]),
    true,
    None,
  )
  if short_alias {
    let alias_key = @theory.TheoryKey::new([], name)
    self.add_theory_alias(alias_key, key, None)
    self.add_module_alias(alias_key, key, None)
  }
}

///|
fn Environment::install_language_builtins(self : Environment) -> Unit raise {
  let builtin = build_language_builtin_module(self.context)
  self.register_language_builtin(builtin, true)
  let ignore = build_language_ignore_module(self.context)
  self.register_language_builtin(ignore, true)
  let boolean = build_language_bool_module(self.context, builtin)
  self.register_language_builtin(boolean, true)
  let tuple = self.tuple_module(0)
  self.register_language_builtin(tuple, false)
  let unit = build_language_unit_module(self.context, builtin, tuple)
  self.register_language_builtin(unit, true)
}

///|
fn Environment::language_builtin_library(
  self : Environment,
  path : @env.LibraryPath,
) -> TypedLibrary? raise {
  guard path.without_builtin_prefix() is Some(relative) &&
    relative.view().segments is [name] &&
    (
      name == b"BuiltIn" ||
      name == b"Ignore" ||
      name == b"Bool" ||
      name == b"Unit"
    ) else {
    return None
  }
  let key = language_builtin_key(name)
  guard self.modules.get(key) is Some(pmodule) else { return None }
  Some(TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]))
}

///|
fn build_reference_module(
  context : @identity.CompilationContext,
  builtin_module : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  let name = b"Ref"
  let type_origin = @identity.Origin::user(b"ref", None, [])
  let builtin_origin = @identity.Origin::user(b"ref", None, [b"builtin"])
  let constructor_origin = @identity.Origin::user(b"ref'mk", None, [b"builtin"])
  let type_variable = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"ref",
    type_origin,
    [type_variable],
    None,
  )
  let logical_argument = @logic.Ty::variable(type_variable)
  let logical_result = @logic.Ty::app(type_symbol, [logical_argument], None)
  let constructor_symbol = @logic.LSymbol::new_constructor(
    context,
    b"ref'mk",
    constructor_origin,
    [logical_argument],
    logical_result,
    1,
    None,
  )
  let projection_symbol = @logic.LSymbol::new_projection(
    context,
    b"contents",
    @identity.Origin::user(b"contents", None, [b"builtin", b"is_field_id"]),
    logical_result,
    logical_argument,
    None,
  )
  let pure_declaration = @logic.Decl::data(
    context,
    type_origin,
    [
      @logic.DataDeclaration::new(
        type_symbol,
        [
          @logic.DataConstructor::new(
            constructor_symbol,
            [Some(projection_symbol)],
            None,
          ),
        ],
        None,
      ),
    ],
    None,
  )
  let field = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"contents", [b"builtin", b"is_field_id"], None),
    @mlw.Ity::variable(type_variable),
    false,
    None,
  )
  let program_type = @mlw.ProgramTypeSymbol::new_record(
    context,
    type_symbol,
    type_origin,
    false,
    true,
    [field],
    [],
    [],
    None,
  )
  // Why3 allocates the projection target before the constructor result for
  // mutable records. Each application owns a distinct fresh region.
  let projection_target_type = @mlw.Ity::instantiate(
    program_type,
    [@mlw.Ity::variable(type_variable)],
    [],
    None,
  )
  let constructor_result_type = @mlw.Ity::instantiate(
    program_type,
    [@mlw.Ity::variable(type_variable)],
    [],
    None,
  )
  let constructor_effect = match constructor_result_type.view() {
    ItyReg(region) => @mlw.Effect::pure(false).reset([region], None)
    _ => @mlw.Effect::pure(false)
  }
  let equality = builtin_module
    .pure_theory()
    .export_namespace()
    .find_logic([b"infix ="], None)
  let constructor_result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    logical_result,
    None,
  )
  let constructor_postcondition = @mlw.Postcondition::trusted_new(
    constructor_result,
    @logic.Term::apply_predicate(
      equality,
      [
        @logic.Term::variable(constructor_result),
        @logic.Term::apply_function(
          constructor_symbol,
          [@logic.Term::variable(field.view().pure_symbol)],
          None,
        ),
      ],
      None,
    ),
    None,
  )
  let constructor_cty = @mlw.Cty::new(
    [field],
    [],
    [constructor_postcondition],
    [],
    [],
    constructor_effect,
    constructor_result_type,
    None,
  )
  let constructor_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    b"ref'mk",
    constructor_origin,
    constructor_cty,
    RLls(constructor_symbol),
    None,
    None,
  )
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"arg", [], None),
    projection_target_type,
    false,
    None,
  )
  let projection_result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    logical_argument,
    None,
  )
  let projection_postcondition = @mlw.Postcondition::trusted_new(
    projection_result,
    @logic.Term::apply_predicate(
      equality,
      [
        @logic.Term::variable(projection_result),
        @logic.Term::apply_function(
          projection_symbol,
          [@logic.Term::variable(target.view().pure_symbol)],
          None,
        ),
      ],
      None,
    ),
    None,
  )
  let projection_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    b"contents",
    projection_symbol.view().origin,
    @mlw.Cty::new(
      [target],
      [],
      [projection_postcondition],
      [],
      [],
      @mlw.Effect::from_reads([target], false),
      field.view().ity,
      None,
    ),
    RLls(projection_symbol),
    Some(field),
    None,
  )
  let type_declaration = @mlw.ProgramTypeDeclaration::new(
    program_type,
    [projection_routine],
    [constructor_routine],
    [],
    None,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"why3", name], name),
    @theory.SemanticName::new(name, [], None),
  )
  // Why3's `empty_module` starts its pure projection with BuiltIn, while
  // `ref_module` records the corresponding program `Uuse` only after the
  // reference type declaration.  Seed the pure half separately to preserve
  // both observable orders.
  builder
  .pure_elaboration_builder()
  .add_use(builtin_module.pure_theory(), true, None)
  builder.add_type_declarations(
    [type_declaration],
    [pure_declaration],
    [],
    None,
  )
  builder.add_use(builtin_module, true, None)
  let reference_routine = @mlw.RoutineSymbol::new_user(
    context,
    b"ref",
    builtin_origin,
    constructor_cty,
    None,
  )
  let reference_computation = @mlw.Cexp::call(
    constructor_routine,
    [],
    [field.view().ity],
    constructor_result_type,
    None,
  )
  builder.add_program_decl(
    reference_routine,
    Cexpression(reference_computation),
    [],
    None,
  )
  builder.close()
}

///|
pub fn Environment::reference_module(
  self : Environment,
  span? : @identity.SourceSpan? = None,
) -> @mlw.Pmodule raise {
  if self.reference_module is Some(pmodule) {
    return pmodule
  }
  let key = @theory.TheoryKey::new([b"why3", b"Ref"], b"Ref")
  let pmodule = match self.modules.get(key) {
    Some(existing) => existing
    None => {
      let builtin = self.resolve_module(
        @theory.TheoryKey::new([], b"BuiltIn"),
        span,
      )
      build_reference_module(self.context, builtin)
    }
  }
  self.reference_module = Some(pmodule)
  pmodule
}

///|
fn Environment::reference_builtin_library(
  self : Environment,
  path : @env.LibraryPath,
) -> TypedLibrary? raise {
  guard path.without_builtin_prefix() is Some(relative) &&
    relative.view().segments is [name] &&
    name == b"Ref" else {
    return None
  }
  let pmodule = self.reference_module()
  Some(TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]))
}

///|
fn build_high_order_module(
  context : @identity.CompilationContext,
  builtin_module : @mlw.Pmodule,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule raise {
  let name = b"HighOrd"
  let function_type_origin = @identity.Origin::user(b"infix ->", None, [
    b"builtin", b"why3:builtin:function-type",
  ])
  let application_origin = @identity.Origin::user(b"infix @", None, [
    b"builtin", b"why3:builtin:function-application",
  ])
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let result = @logic.TyVarSymbol::new(
    context,
    b"b",
    @identity.Origin::user(b"b", None, []),
  )
  let function_type = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    function_type_origin,
    [parameter, result],
    span,
  )
  let application_parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let application_result = @logic.TyVarSymbol::new(
    context,
    b"b",
    @identity.Origin::user(b"b", None, []),
  )
  let parameter_ty = @logic.Ty::variable(application_parameter)
  let result_ty = @logic.Ty::variable(application_result)
  let function_ty = @logic.Ty::app(
    function_type,
    [parameter_ty, result_ty],
    span,
  )
  let application = @logic.LSymbol::new_function(
    context,
    b"infix @",
    application_origin,
    [function_ty, parameter_ty],
    result_ty,
    span,
  )
  let pure_type = @logic.Decl::type_declaration(
    context,
    function_type_origin,
    [function_type],
    span,
  )
  let pure_application = @logic.Decl::parameter(
    context, application_origin, application, span,
  )
  let program_type = @mlw.ProgramTypeSymbol::new_record(
    context,
    function_type,
    function_type_origin,
    true,
    false,
    [],
    [],
    [],
    span,
  )
  let function_ity = @mlw.Ity::app(
    program_type,
    [
      @mlw.Ity::variable(application_parameter),
      @mlw.Ity::variable(application_result),
    ],
    span,
  )
  let function_argument = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"f", [], span),
    function_ity,
    false,
    span,
  )
  let value_argument = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], span),
    @mlw.Ity::variable(application_parameter),
    false,
    span,
  )
  let post_result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    result_ty,
    None,
  )
  let equality = builtin_module
    .pure_theory()
    .export_namespace()
    .find_logic([b"infix ="], span)
  let postcondition = @mlw.Postcondition::trusted_new(
    post_result,
    @logic.Term::apply_predicate(
      equality,
      [
        @logic.Term::variable(post_result),
        @logic.Term::apply_function(
          application,
          [
            @logic.Term::variable(function_argument.view().pure_symbol),
            @logic.Term::variable(value_argument.view().pure_symbol),
          ],
          None,
        ),
      ],
      None,
    ),
    None,
  )
  let result_ity = @mlw.Ity::variable(application_result)
  let computation_type = @mlw.Cty::new(
    [function_argument, value_argument],
    [],
    [postcondition],
    [],
    [],
    @mlw.Effect::pure(false).spoil(result_ity),
    result_ity,
    span,
  )
  let application_routine = @mlw.RoutineSymbol::new_with_logic(
    context,
    b"infix @",
    application_origin,
    computation_type,
    RLls(application),
    None,
    span,
  )
  // `pd_func_app` stores a bare `Cany` implementation alongside the richer
  // public routine type produced by `rs_of_ls`.
  let implementation_type = @mlw.Cty::new(
    [function_argument, value_argument],
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    result_ity,
    span,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"why3", name], name),
    @theory.SemanticName::new(name, [], span),
  )
  builder.add_type_declarations(
    [@mlw.ProgramTypeDeclaration::simple(program_type)],
    [pure_type],
    [],
    span,
  )
  builder.add_program_decl(
    application_routine,
    Cany(implementation_type),
    [pure_application],
    span,
  )
  builder.close()
}

///|
pub fn Environment::high_order_module(
  self : Environment,
  span? : @identity.SourceSpan? = None,
) -> @mlw.Pmodule raise {
  if self.high_order_module is Some(pmodule) {
    return pmodule
  }
  let key = @theory.TheoryKey::new([b"why3", b"HighOrd"], b"HighOrd")
  let pmodule = match self.modules.get(key) {
    Some(existing) => existing
    None => {
      guard self.modules.get(language_builtin_key(b"BuiltIn"))
        is Some(builtin_module) else {
        abort("language builtin module is not installed")
      }
      build_high_order_module(self.context, builtin_module, span)
    }
  }
  self.high_order_module = Some(pmodule)
  pmodule
}

///|
fn Environment::high_order_builtin_library(
  self : Environment,
  path : @env.LibraryPath,
) -> TypedLibrary? raise {
  guard path.without_builtin_prefix() is Some(relative) &&
    relative.view().segments is [name] &&
    name == b"HighOrd" else {
    return None
  }
  let pmodule = self.high_order_module()
  Some(TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]))
}

///|
fn build_well_founded_module(
  context : @identity.CompilationContext,
  builtin_module : @mlw.Pmodule,
  bool_module : @mlw.Pmodule,
  high_order_module : @mlw.Pmodule,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule raise {
  let name = b"WellFounded"
  let acc_origin = @identity.Origin::user(b"acc", None, [])
  let well_founded_origin = @identity.Origin::user(b"well_founded", None, [])
  let builtin_space = builtin_module.pure_theory().export_namespace()
  let bool_space = bool_module.pure_theory().export_namespace()
  let high_order_space = high_order_module.pure_theory().export_namespace()
  let equality = builtin_space.find_logic([b"infix ="], span)
  let bool_type = bool_space.find_type([b"bool"], span)
  let true_symbol = bool_space.find_logic([b"True"], span)
  let function_type = high_order_space.find_type([b"infix ->"], span)
  let application = high_order_space.find_logic([b"infix @"], span)
  let alpha = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let alpha_ty = @logic.Ty::variable(alpha)
  let bool_ty = @logic.Ty::app(bool_type, [], span)
  let relation_ty = @logic.Ty::app(
    function_type,
    [alpha_ty, @logic.Ty::app(function_type, [alpha_ty, bool_ty], span)],
    span,
  )
  let acc = @logic.LSymbol::new_predicate(
    context,
    b"acc",
    acc_origin,
    [relation_ty, alpha_ty],
    span,
  )
  let relation = @logic.VSymbol::new(
    context,
    b"r",
    @identity.Origin::user(b"r", None, []),
    relation_ty,
    span,
  )
  let value = @logic.VSymbol::new(
    context,
    b"x",
    @identity.Origin::user(b"x", None, []),
    alpha_ty,
    span,
  )
  let predecessor = @logic.VSymbol::new(
    context,
    b"y",
    @identity.Origin::user(b"y", None, []),
    alpha_ty,
    span,
  )
  let relation_term = @logic.Term::variable(relation)
  let value_term = @logic.Term::variable(value)
  let predecessor_term = @logic.Term::variable(predecessor)
  let relation_application = @logic.Term::apply_function(
    application,
    [
      @logic.Term::apply_function(
        application,
        [relation_term, predecessor_term],
        span,
      ),
      value_term,
    ],
    span,
  )
  let relation_formula = @logic.Term::apply_predicate(
    equality,
    [relation_application, @logic.Term::apply_function(true_symbol, [], span)],
    span,
  )
  let accessible_predecessor = @logic.Term::apply_predicate(
    acc,
    [relation_term, predecessor_term],
    span,
  )
  let all_predecessors = @logic.Term::quantify(
    ForallQuantifier,
    [predecessor],
    [],
    @logic.Term::binary(Implies, relation_formula, accessible_predecessor, span),
    span,
  )
  let accessible_value = @logic.Term::apply_predicate(
    acc,
    [relation_term, value_term],
    span,
  )
  let introduction = @logic.Term::quantify(
    ForallQuantifier,
    [relation, value],
    [],
    @logic.Term::binary(Implies, all_predecessors, accessible_value, span),
    span,
  )
  let acc_case = @logic.PrSymbol::new(
    context,
    b"acc_x",
    @identity.Origin::user(b"acc_x", None, []),
  )
  let inductive = @logic.Decl::inductive(
    context,
    acc_origin,
    Ind,
    [
      @logic.InductiveDeclaration::new(
        acc,
        [@logic.InductiveCase::new(context, acc_case, introduction, span)],
        span,
      ),
    ],
    span,
  )
  let well_founded_alpha = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let well_founded_alpha_ty = @logic.Ty::variable(well_founded_alpha)
  let well_founded_relation_ty = @logic.Ty::app(
    function_type,
    [
      well_founded_alpha_ty,
      @logic.Ty::app(function_type, [well_founded_alpha_ty, bool_ty], span),
    ],
    span,
  )
  let well_founded = @logic.LSymbol::new_predicate(
    context,
    b"well_founded",
    well_founded_origin,
    [well_founded_relation_ty],
    span,
  )
  let definition_relation = @logic.VSymbol::new(
    context,
    b"r",
    @identity.Origin::user(b"r", None, []),
    well_founded_relation_ty,
    span,
  )
  let definition_value = @logic.VSymbol::new(
    context,
    b"x",
    @identity.Origin::user(b"x", None, []),
    well_founded_alpha_ty,
    span,
  )
  let definition = @logic.Decl::logic(
    context,
    well_founded_origin,
    [
      @logic.LogicDefinition::new(
        context,
        well_founded,
        [definition_relation],
        @logic.Term::quantify(
          ForallQuantifier,
          [definition_value],
          [],
          @logic.Term::apply_predicate(
            acc,
            [
              @logic.Term::variable(definition_relation),
              @logic.Term::variable(definition_value),
            ],
            span,
          ),
          span,
        ),
        span,
      ),
    ],
    span,
  )
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"why3", name], name),
    @theory.SemanticName::new(name, [], span),
  )
  builder.add_use(builtin_module, true, span)
  builder.add_use(bool_module, true, span)
  builder.add_use(high_order_module, true, span)
  builder.add_pure_decl(inductive, span)
  builder.add_pure_decl(definition, span)
  builder.close()
}

///|
pub fn Environment::well_founded_module(
  self : Environment,
  span? : @identity.SourceSpan? = None,
) -> @mlw.Pmodule raise {
  if self.well_founded_module is Some(pmodule) {
    return pmodule
  }
  let key = @theory.TheoryKey::new([b"why3", b"WellFounded"], b"WellFounded")
  let pmodule = match self.modules.get(key) {
    Some(existing) => existing
    None => {
      let builtin = self.resolve_module(
        @theory.TheoryKey::new([], b"BuiltIn"),
        span,
      )
      let bool_module = self.resolve_module(
        @theory.TheoryKey::new([], b"Bool"),
        span,
      )
      build_well_founded_module(
        self.context,
        builtin,
        bool_module,
        self.high_order_module(span~),
        span,
      )
    }
  }
  self.well_founded_module = Some(pmodule)
  pmodule
}

///|
fn Environment::well_founded_builtin_library(
  self : Environment,
  path : @env.LibraryPath,
) -> TypedLibrary? raise {
  guard path.without_builtin_prefix() is Some(relative) &&
    relative.view().segments is [name] &&
    name == b"WellFounded" else {
    return None
  }
  let pmodule = self.well_founded_module()
  Some(TypedLibrary::new([(name, pmodule.pure_theory())], [(name, pmodule)]))
}

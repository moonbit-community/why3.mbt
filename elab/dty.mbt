// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// Delayed types are owned by the elaborator and expose no mutable view.
/// Semantic packages only receive fully finalized immutable `@logic.Ty`
/// values.
struct Dty {
  session : Ref[Unit]
  cell : Ref[DtyState]
}

///|
/// The mutable states mirror the elaboration boundary explicitly. `Link`
/// nodes are path-compressed and can never occur in semantic `@logic.Ty`.
priv enum DtyState {
  Fresh(Int64)
  Link(Dty)
  App(@logic.TypeSymbol, Array[Dty])
  Arrow(Dty, Dty)
  Known(@logic.Ty)
}

///|
/// One deterministic, single-threaded delayed-type arena associated with a
/// semantic compilation context.
struct DtyContext {
  semantic_context : @identity.CompilationContext
  session : Ref[Unit]
  mut next_fresh_id : Int64
}

///|
pub fn DtyContext::new(
  semantic_context : @identity.CompilationContext,
) -> DtyContext {
  { semantic_context, session: Ref(()), next_fresh_id: 0L }
}

///|
pub fn DtyContext::fresh(self : DtyContext) -> Dty {
  let id = self.next_fresh_id
  self.next_fresh_id = id + 1L
  { session: self.session, cell: Ref(Fresh(id)) }
}

///|
fn DtyContext::require_member(
  self : DtyContext,
  ty : Dty,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  if !physical_equal(self.session, ty.session) {
    @logic.fail_type(
      ContextMismatch,
      span,
      "delayed types belong to different elaboration sessions",
    )
  }
}

///|
pub fn DtyContext::known(
  self : DtyContext,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Dty raise @logic.TypeError {
  if !self.semantic_context.contains(ty.context_anchor()) {
    @logic.fail_type(
      ContextMismatch,
      span,
      "known type belongs to another compilation context",
    )
  }
  { session: self.session, cell: Ref(Known(ty)) }
}

///|
fn prune(ty : Dty) -> Dty {
  match ty.cell.val {
    Link(target) => {
      let root = prune(target)
      ty.cell.val = Link(root)
      root
    }
    Fresh(_) | App(_, _) | Arrow(_, _) | Known(_) => ty
  }
}

///|
fn DtyContext::head_symbol(
  self : DtyContext,
  delayed : Dty,
) -> @logic.TypeSymbol? raise @logic.TypeError {
  self.require_member(delayed, None)
  match prune(delayed).cell.val {
    Known(ty) =>
      match ty.view() {
        TyApp(symbol, _) => Some(symbol)
        TyVar(_) => None
      }
    App(symbol, _) => Some(symbol)
    Fresh(_) | Arrow(_, _) => None
    Link(_) => abort("prune returned a Link node")
  }
}

///|
fn write_semantic_ty_diagnostic_nested(
  output : @buffer.Buffer,
  ty : @logic.Ty,
  nested_arrow : Bool,
) -> Unit {
  match ty.view() {
    TyVar(variable) => {
      output.write_byte(b'\'')
      output.write_bytes(variable.name())
    }
    TyApp(symbol, [parameter, result]) if symbol.name() == b"infix ->" => {
      if nested_arrow {
        output.write_byte(b'(')
      }
      write_semantic_ty_diagnostic_nested(output, parameter, true)
      output.write_bytes(b" -> ")
      write_semantic_ty_diagnostic_nested(output, result, false)
      if nested_arrow {
        output.write_byte(b')')
      }
    }
    TyApp(symbol, arguments) => {
      output.write_bytes(symbol.name())
      if !arguments.is_empty() {
        output.write_byte(b'<')
        for index, argument in arguments {
          if index > 0 {
            output.write_bytes(b", ")
          }
          write_semantic_ty_diagnostic_nested(output, argument, true)
        }
        output.write_byte(b'>')
      }
    }
  }
}

///|
fn write_semantic_ty_diagnostic(
  output : @buffer.Buffer,
  ty : @logic.Ty,
) -> Unit {
  write_semantic_ty_diagnostic_nested(output, ty, false)
}

///|
fn write_dty_diagnostic_nested(
  output : @buffer.Buffer,
  ty : Dty,
  nested_arrow : Bool,
) -> Unit {
  let ty = prune(ty)
  match ty.cell.val {
    Fresh(id) => {
      output.write_byte(b'?')
      output.write_string_utf8(id.to_string())
    }
    Known(semantic) =>
      write_semantic_ty_diagnostic_nested(output, semantic, nested_arrow)
    App(symbol, [parameter, result]) if symbol.name() == b"infix ->" => {
      if nested_arrow {
        output.write_byte(b'(')
      }
      write_dty_diagnostic_nested(output, parameter, true)
      output.write_bytes(b" -> ")
      write_dty_diagnostic_nested(output, result, false)
      if nested_arrow {
        output.write_byte(b')')
      }
    }
    App(symbol, arguments) => {
      output.write_bytes(symbol.name())
      if !arguments.is_empty() {
        output.write_byte(b'<')
        for index, argument in arguments {
          if index > 0 {
            output.write_bytes(b", ")
          }
          write_dty_diagnostic_nested(output, argument, true)
        }
        output.write_byte(b'>')
      }
    }
    Arrow(parameter, result) => {
      if nested_arrow {
        output.write_byte(b'(')
      }
      write_dty_diagnostic_nested(output, parameter, true)
      output.write_bytes(b" -> ")
      write_dty_diagnostic_nested(output, result, false)
      if nested_arrow {
        output.write_byte(b')')
      }
    }
    Link(_) => abort("prune returned a Link node")
  }
}

///|
fn dty_diagnostic_bytes(ty : Dty) -> Bytes {
  let output = @buffer.Buffer()
  write_dty_diagnostic_nested(output, ty, false)
  output.to_bytes()
}

///|
fn semantic_ty_diagnostic_bytes(ty : @logic.Ty) -> Bytes {
  let output = @buffer.Buffer()
  write_semantic_ty_diagnostic(output, ty)
  output.to_bytes()
}

///|
fn reconcile_inferred_semantic_types(
  left : @logic.Ty,
  right : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  if left == right {
    return left
  }
  let substitution = @logic.TySubstitution::new().match_inference_types(
    left, right, span,
  )
  let resolved_left = substitution.apply(left, span)
  let resolved_right = substitution.apply(right, span)
  if resolved_left != resolved_right {
    @logic.fail_type(
      TypeMismatch,
      span,
      "inference substitution did not reconcile semantic types",
    )
  }
  resolved_left
}

///|
fn application_actual_type(
  symbol : @logic.LSymbol,
  supplied_arguments : Int,
) -> Bytes {
  let output = @buffer.Buffer()
  let view = symbol.view()
  for index = supplied_arguments
      index < view.argument_types.length()
      index = index + 1 {
    write_semantic_ty_diagnostic_nested(
      output,
      view.argument_types[index],
      true,
    )
    output.write_bytes(b" -> ")
  }
  match view.result_type {
    Some(result) => write_semantic_ty_diagnostic(output, result)
    None => output.write_bytes(b"formula")
  }
  output.to_bytes()
}

///|
fn application_expected_type(symbol : @logic.LSymbol) -> Bytes {
  match symbol.view().result_type {
    Some(result) => semantic_ty_diagnostic_bytes(result)
    None => b"formula"
  }
}

///|
fn DtyContext::unify_expected(
  self : DtyContext,
  actual : Dty,
  expected : Dty,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  let actual_type = dty_diagnostic_bytes(actual)
  let expected_type = dty_diagnostic_bytes(expected)
  self.unify(actual, expected, span) catch {
    @logic.TypeError(diagnostic) =>
      @logic.fail_type_with_types(
        diagnostic.kind,
        diagnostic.span,
        actual_type,
        expected_type,
        diagnostic.message,
      )
  }
}

///|
/// Internal higher-order shape used long enough to diagnose invalid source
/// applications (including occurs-check failures). It is never projected into
/// immutable Why3 semantic types.
pub fn DtyContext::arrow(
  self : DtyContext,
  parameter : Dty,
  result : Dty,
  span : @identity.SourceSpan?,
) -> Dty raise @logic.TypeError {
  self.require_member(parameter, span)
  self.require_member(result, span)
  { session: self.session, cell: Ref(Arrow(parameter, result)) }
}

///|
/// Instantiates every semantic type variable through a caller-owned map so a
/// polymorphic symbol application shares fresh delayed variables consistently.
pub fn DtyContext::specialize(
  self : DtyContext,
  ty : @logic.Ty,
  variables : Map[@logic.TyVarSymbol, Dty],
  span : @identity.SourceSpan?,
) -> Dty raise @logic.TypeError {
  match ty.view() {
    TyVar(variable) =>
      match variables.get(variable) {
        Some(delayed) => delayed
        None => {
          let delayed = self.fresh()
          variables[variable] = delayed
          delayed
        }
      }
    TyApp(symbol, arguments) => {
      let delayed_arguments = [
        for argument in arguments => self.specialize(argument, variables, span)
      ]
      self.app(symbol, delayed_arguments, span)
    }
  }
}

///|
fn instantiate_delayed_alias(
  context : DtyContext,
  ty : @logic.Ty,
  arguments : Map[@logic.TyVarSymbol, Dty],
  span : @identity.SourceSpan?,
) -> Dty raise @logic.TypeError {
  match ty.view() {
    TyVar(variable) =>
      match arguments.get(variable) {
        Some(value) => value
        None =>
          @logic.fail_type(
            UnboundTypeVariable,
            span,
            "validated alias is missing a delayed type argument",
          )
      }
    TyApp(symbol, type_arguments) => {
      let delayed_arguments = [
        for argument in type_arguments => {
          instantiate_delayed_alias(context, argument, arguments, span)
        }
      ]
      context.app(symbol, delayed_arguments, span)
    }
  }
}

///|
pub fn DtyContext::app(
  self : DtyContext,
  symbol : @logic.TypeSymbol,
  arguments : ArrayView[Dty],
  span : @identity.SourceSpan?,
) -> Dty raise @logic.TypeError {
  if !self.semantic_context.contains(symbol.semantic_id()) {
    @logic.fail_type(
      ContextMismatch,
      span,
      "delayed type constructor belongs to another compilation context",
    )
  }
  if arguments.length() != symbol.arity() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "delayed type constructor expected \{symbol.arity()} arguments but received \{arguments.length()}",
    )
  }
  let copied = arguments.to_owned()
  for argument in copied {
    self.require_member(argument, span)
  }
  let known_arguments : Array[@logic.Ty] = []
  let mut all_known = true
  for argument in copied {
    match prune(argument).cell.val {
      Known(ty) => known_arguments.push(ty)
      Fresh(_) | Link(_) | App(_, _) | Arrow(_, _) => all_known = false
    }
  }
  if all_known {
    return self.known(@logic.Ty::app(symbol, known_arguments, span), span)
  }
  match symbol.view().definition {
    Alias(target) => {
      let substitutions : Map[@logic.TyVarSymbol, Dty] = Map([])
      for index, parameter in symbol.view().parameters {
        substitutions[parameter] = copied[index]
      }
      instantiate_delayed_alias(self, target, substitutions, span)
    }
    NoDef | Range(_, _) | Float(_, _) =>
      { session: self.session, cell: Ref(App(symbol, copied)) }
  }
}

///|
fn DtyContext::occurs(
  self : DtyContext,
  variable : Dty,
  candidate : Dty,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  self.require_member(candidate, span)
  let candidate = prune(candidate)
  if physical_equal(variable.cell, candidate.cell) {
    @logic.fail_type(
      OccursCheck,
      span,
      "delayed type variable occurs in its own solution",
    )
  }
  match candidate.cell.val {
    App(_, arguments) =>
      for argument in arguments {
        self.occurs(variable, argument, span)
      }
    Arrow(parameter, result) => {
      self.occurs(variable, parameter, span)
      self.occurs(variable, result, span)
    }
    Fresh(_) | Known(_) => ()
    Link(_) => abort("prune returned a Link node")
  }
}

///|
fn DtyContext::match_known(
  self : DtyContext,
  delayed : Dty,
  known : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  let delayed = prune(delayed)
  match delayed.cell.val {
    Fresh(_) => delayed.cell.val = Known(known)
    Known(previous) => {
      let reconciled = reconcile_inferred_semantic_types(previous, known, span) catch {
        @logic.TypeError(diagnostic) =>
          if diagnostic.kind == TypeMismatch {
            let previous_shape = semantic_ty_diagnostic_bytes(previous).to_string()
            let known_shape = semantic_ty_diagnostic_bytes(known).to_string()
            @logic.fail_type(
              TypeMismatch,
              span,
              "semantic types do not match: \{previous_shape} vs \{known_shape}",
            )
          } else {
            raise @logic.TypeError(diagnostic)
          }
      }
      delayed.cell.val = Known(reconciled)
    }
    App(delayed_symbol, delayed_arguments) =>
      match known.view() {
        TyApp(known_symbol, known_arguments) => {
          if delayed_symbol != known_symbol ||
            delayed_arguments.length() != known_arguments.length() {
            @logic.fail_type(
              TypeMismatch,
              span,
              "delayed and semantic type constructors do not match: \{delayed_symbol.name()}#\{delayed_symbol.semantic_id().local_id()} vs \{known_symbol.name()}#\{known_symbol.semantic_id().local_id()}",
            )
          }
          for index, argument in delayed_arguments {
            self.match_known(argument, known_arguments[index], span)
          }
        }
        TyVar(_) =>
          @logic.fail_type(
            TypeMismatch,
            span,
            "delayed type application cannot match a semantic type variable",
          )
      }
    Arrow(parameter, result) =>
      match known.view() {
        TyApp(symbol, arguments) if symbol.view().name == b"infix ->" &&
          arguments.length() == 2 => {
          self.match_known(parameter, arguments[0], span)
          self.match_known(result, arguments[1], span)
        }
        _ =>
          @logic.fail_type(
            TypeMismatch,
            span,
            "higher-order delayed type cannot match a semantic type",
          )
      }
    Link(_) => abort("prune returned a Link node")
  }
}

///|
pub fn DtyContext::unify(
  self : DtyContext,
  left : Dty,
  right : Dty,
  span : @identity.SourceSpan?,
) -> Unit raise @logic.TypeError {
  self.require_member(left, span)
  self.require_member(right, span)
  let left = prune(left)
  let right = prune(right)
  if physical_equal(left.cell, right.cell) {
    return
  }
  match (left.cell.val, right.cell.val) {
    (Fresh(_), _) => {
      self.occurs(left, right, span)
      left.cell.val = Link(right)
    }
    (_, Fresh(_)) => {
      self.occurs(right, left, span)
      right.cell.val = Link(left)
    }
    (Known(left_type), Known(right_type)) => {
      let reconciled = reconcile_inferred_semantic_types(
        left_type, right_type, span,
      ) catch {
        @logic.TypeError(diagnostic) =>
          if diagnostic.kind == TypeMismatch {
            let left_shape = semantic_ty_diagnostic_bytes(left_type).to_string()
            let right_shape = semantic_ty_diagnostic_bytes(right_type).to_string()
            @logic.fail_type(
              TypeMismatch,
              span,
              "semantic types do not unify: \{left_shape} vs \{right_shape}",
            )
          } else {
            raise @logic.TypeError(diagnostic)
          }
      }
      left.cell.val = Known(reconciled)
      right.cell.val = Known(reconciled)
    }
    (Known(left_type), App(_, _)) => self.match_known(right, left_type, span)
    (App(_, _), Known(right_type)) => self.match_known(left, right_type, span)
    (Known(left_type), Arrow(_, _)) => self.match_known(right, left_type, span)
    (Arrow(_, _), Known(right_type)) => self.match_known(left, right_type, span)
    (App(left_symbol, left_arguments), App(right_symbol, right_arguments)) => {
      if left_symbol != right_symbol ||
        left_arguments.length() != right_arguments.length() {
        @logic.fail_type(
          TypeMismatch,
          span,
          "delayed type constructors do not unify: \{left_symbol.name()}#\{left_symbol.semantic_id().local_id()} vs \{right_symbol.name()}#\{right_symbol.semantic_id().local_id()}",
        )
      }
      for index, argument in left_arguments {
        self.unify(argument, right_arguments[index], span)
      }
    }
    (Arrow(left_parameter, left_result), Arrow(right_parameter, right_result)) => {
      self.unify(left_parameter, right_parameter, span)
      self.unify(left_result, right_result, span)
    }
    (App(left_symbol, left_arguments), Arrow(right_parameter, right_result)) =>
      if left_symbol.view().name == b"infix ->" && left_arguments.length() == 2 {
        self.unify(left_arguments[0], right_parameter, span)
        self.unify(left_arguments[1], right_result, span)
      } else {
        @logic.fail_type(
          TypeMismatch,
          span,
          "higher-order and first-order types do not unify",
        )
      }
    (Arrow(left_parameter, left_result), App(right_symbol, right_arguments)) =>
      if right_symbol.view().name == b"infix ->" &&
        right_arguments.length() == 2 {
        self.unify(left_parameter, right_arguments[0], span)
        self.unify(left_result, right_arguments[1], span)
      } else {
        @logic.fail_type(
          TypeMismatch,
          span,
          "higher-order and first-order types do not unify",
        )
      }
    (Link(_), _) | (_, Link(_)) => abort("prune returned a Link node")
  }
}

///|
pub fn DtyContext::finalize_strict(
  self : DtyContext,
  delayed : Dty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  self.require_member(delayed, span)
  let delayed = prune(delayed)
  match delayed.cell.val {
    Fresh(id) =>
      @logic.fail_type(
        UnresolvedTypeVariable,
        span,
        "program type contains unresolved type variable xi\{id}",
      )
    Known(ty) => {
      if !ty.is_closed() {
        @logic.fail_type(
          PolymorphicProgramRoutine,
          span,
          "program type contains a semantic type variable",
        )
      }
      ty
    }
    App(symbol, arguments) => {
      let finalized = [
        for argument in arguments => self.finalize_strict(argument, span)
      ]
      let ty = @logic.Ty::app(symbol, finalized, span)
      if !ty.is_closed() {
        @logic.fail_type(
          PolymorphicProgramRoutine,
          span,
          "program type contains a semantic type variable",
        )
      }
      delayed.cell.val = Known(ty)
      ty
    }
    Arrow(_, _) =>
      @logic.fail_type(
        PolymorphicProgramRoutine,
        span,
        "program type contains a higher-order arrow",
      )
    Link(_) => abort("prune returned a Link node")
  }
}

///|
/// Finalizes a first-order pure-logic type. Unlike program strictness, semantic
/// type variables are valid here; only unresolved delayed variables and arrows
/// are rejected.
pub fn DtyContext::finalize_pure(
  self : DtyContext,
  delayed : Dty,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  self.require_member(delayed, span)
  let delayed = prune(delayed)
  match delayed.cell.val {
    Fresh(id) =>
      @logic.fail_type(
        UnresolvedTypeVariable,
        span,
        "pure type contains unresolved type variable xi\{id}",
      )
    Known(ty) => ty
    App(symbol, arguments) => {
      let finalized = [
        for argument in arguments => self.finalize_pure(argument, span)
      ]
      let ty = @logic.Ty::app(symbol, finalized, span)
      delayed.cell.val = Known(ty)
      ty
    }
    Arrow(_, _) =>
      @logic.fail_type(
        TypeMismatch,
        span,
        "higher-order type cannot be finalized as first-order logic",
      )
    Link(_) => abort("prune returned a Link node")
  }
}

///|
fn DtyContext::contains_arrow(
  self : DtyContext,
  delayed : Dty,
) -> Bool raise @logic.TypeError {
  self.require_member(delayed, None)
  let delayed = prune(delayed)
  match delayed.cell.val {
    Fresh(_) | Known(_) => false
    App(_, arguments) =>
      arguments.any(argument => self.contains_arrow(argument))
    Arrow(_, _) => true
    Link(_) => abort("prune returned a Link node")
  }
}

///|
pub fn DtyContext::finalize_higher_order(
  self : DtyContext,
  delayed : Dty,
  function_type : @logic.TypeSymbol,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  self.require_member(delayed, span)
  if !self.semantic_context.contains(function_type.semantic_id()) {
    @logic.fail_type(
      ContextMismatch,
      span,
      "higher-order type symbol belongs to another compilation context",
    )
  }
  let function_view = function_type.view()
  if function_view.name != b"infix ->" || function_view.parameters.length() != 2 {
    @logic.fail_type(
      TypeMismatch,
      span,
      "higher-order finalization requires the builtin function type",
    )
  }
  let delayed = prune(delayed)
  let result = match delayed.cell.val {
    Fresh(id) =>
      @logic.fail_type(
        UnresolvedTypeVariable,
        span,
        "higher-order type contains unresolved type variable xi\{id}",
      )
    Known(ty) => ty
    App(symbol, arguments) =>
      @logic.Ty::app(
        symbol,
        arguments.map(argument => {
          self.finalize_higher_order(argument, function_type, span)
        }),
        span,
      )
    Arrow(parameter, result) =>
      @logic.Ty::app(
        function_type,
        [
          self.finalize_higher_order(parameter, function_type, span),
          self.finalize_higher_order(result, function_type, span),
        ],
        span,
      )
    Link(_) => abort("prune returned a Link node")
  }
  delayed.cell.val = Known(result)
  result
}

///|
fn DtyContext::generalize_inner(
  self : DtyContext,
  delayed : Dty,
  span : @identity.SourceSpan?,
  variables : Array[@logic.TyVarSymbol],
) -> @logic.Ty raise @logic.TypeError {
  self.require_member(delayed, span)
  let delayed = prune(delayed)
  match delayed.cell.val {
    Fresh(_) => {
      let origin = @identity.Origin::user(b"xi", span, [])
      let variable = @logic.TyVarSymbol::new(
        self.semantic_context,
        b"xi",
        origin,
      )
      variables.push(variable)
      let ty = @logic.Ty::variable(variable)
      delayed.cell.val = Known(ty)
      ty
    }
    Known(ty) => ty
    App(symbol, arguments) => {
      let finalized = [
        for argument in arguments => {
          self.generalize_inner(argument, span, variables)
        }
      ]
      let ty = @logic.Ty::app(symbol, finalized, span)
      delayed.cell.val = Known(ty)
      ty
    }
    Arrow(_, _) =>
      @logic.fail_type(
        TypeMismatch,
        span,
        "higher-order type cannot be generalized as first-order logic",
      )
    Link(_) => abort("prune returned a Link node")
  }
}

///|
/// Deterministically generalizes unresolved pure-logic variables in first
/// preorder encounter order.
pub fn DtyContext::generalize(
  self : DtyContext,
  delayed : Dty,
  span : @identity.SourceSpan?,
) -> (@logic.Ty, Array[@logic.TyVarSymbol]) raise @logic.TypeError {
  let variables : Array[@logic.TyVarSymbol] = []
  let ty = self.generalize_inner(delayed, span, variables)
  (ty, variables)
}

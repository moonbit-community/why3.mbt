// Projection used by pprint_whyml_sexp from the public MoonBit AST to Why3 1.7.2 Ptree sexps.

///|
fn sexp_of_span(span : @parser.Span) -> Sexp {
  sexp_list([
    sexp_atom(span.start.filename),
    sexp_int64(span.start.line),
    sexp_int64(span.start.column),
    sexp_int64(span.end.line),
    sexp_int64(span.end.column),
  ])
}

///|
fn sexp_of_attribute(attribute : @parser.Attribute) -> Sexp {
  match attribute {
    Text(value) => sexp_variant("ATstr", [sexp_atom(value)])
    Position(span) => sexp_variant("ATpos", [sexp_of_span(span)])
  }
}

///|
fn sexp_of_ident(ident : @parser.Ident) -> Sexp {
  sexp_record([
    ("id_str", sexp_atom(ident.name)),
    ("id_ats", sexp_array(ident.attributes, sexp_of_attribute)),
    ("id_loc", sexp_of_span(ident.span)),
  ])
}

///|
fn sexp_of_qualid(path : @parser.QualId) -> Sexp {
  match path {
    Qident(ident) => sexp_variant("Qident", [sexp_of_ident(ident)])
    Qdot(prefix, ident) =>
      sexp_variant("Qdot", [sexp_of_qualid(prefix), sexp_of_ident(ident)])
  }
}

///|
fn sexp_of_pty(ty : @parser.Pty) -> Sexp {
  match ty {
    PTtyvar(ident) => sexp_variant("PTtyvar", [sexp_of_ident(ident)])
    PTtyapp(path, arguments) =>
      sexp_variant("PTtyapp", [
        sexp_of_qualid(path),
        sexp_array(arguments, sexp_of_pty),
      ])
    PTtuple(elements) =>
      sexp_variant("PTtuple", [sexp_array(elements, sexp_of_pty)])
    PTref(elements) =>
      sexp_variant("PTref", [sexp_array(elements, sexp_of_pty)])
    PTarrow(left, right) =>
      sexp_variant("PTarrow", [sexp_of_pty(left), sexp_of_pty(right)])
    PTscope(path, inner) =>
      sexp_variant("PTscope", [sexp_of_qualid(path), sexp_of_pty(inner)])
    PTparen(inner) => sexp_variant("PTparen", [sexp_of_pty(inner)])
    PTpure(inner) => sexp_variant("PTpure", [sexp_of_pty(inner)])
  }
}

///|
fn sexp_of_pattern_desc(desc : @parser.PatternDesc) -> Sexp {
  match desc {
    Pwild => sexp_variant("Pwild", [])
    Pvar(ident) => sexp_variant("Pvar", [sexp_of_ident(ident)])
    Papp(path, arguments) =>
      sexp_variant("Papp", [
        sexp_of_qualid(path),
        sexp_array(arguments, sexp_of_pattern),
      ])
    Prec(fields) =>
      sexp_variant("Prec", [
        sexp_array(fields, field => {
          sexp_pair(field, sexp_of_qualid, sexp_of_pattern)
        }),
      ])
    Ptuple(elements) =>
      sexp_variant("Ptuple", [sexp_array(elements, sexp_of_pattern)])
    Pas(pattern, ident, ghost) =>
      sexp_variant("Pas", [
        sexp_of_pattern(pattern),
        sexp_of_ident(ident),
        sexp_bool(ghost),
      ])
    Por(left, right) =>
      sexp_variant("Por", [sexp_of_pattern(left), sexp_of_pattern(right)])
    Pcast(pattern, ty) =>
      sexp_variant("Pcast", [sexp_of_pattern(pattern), sexp_of_pty(ty)])
    Pscope(path, pattern) =>
      sexp_variant("Pscope", [sexp_of_qualid(path), sexp_of_pattern(pattern)])
    Pparen(pattern) => sexp_variant("Pparen", [sexp_of_pattern(pattern)])
    Pghost(pattern) => sexp_variant("Pghost", [sexp_of_pattern(pattern)])
  }
}

///|
fn sexp_of_pattern(pattern : @parser.Pattern) -> Sexp {
  sexp_record([
    ("pat_desc", sexp_of_pattern_desc(pattern.desc)),
    ("pat_loc", sexp_of_span(pattern.span)),
  ])
}

///|
fn sexp_of_binder(binder : @parser.Binder) -> Sexp {
  sexp_list([
    sexp_of_span(binder.span),
    sexp_option(binder.ident, sexp_of_ident),
    sexp_bool(binder.ghost),
    sexp_option(binder.binder_type, sexp_of_pty),
  ])
}

///|
fn sexp_of_param(param : @parser.Param) -> Sexp {
  sexp_list([
    sexp_of_span(param.span),
    sexp_option(param.ident, sexp_of_ident),
    sexp_bool(param.ghost),
    sexp_of_pty(param.param_type),
  ])
}

///|
fn sexp_of_int_literal_kind(kind : @parser.IntLiteralKind) -> Sexp {
  sexp_atom_string(
    match kind {
      ILitUnk => "ILitUnk"
      ILitDec => "ILitDec"
      ILitHex => "ILitHex"
      ILitOct => "ILitOct"
      ILitBin => "ILitBin"
    },
  )
}

///|
fn sexp_of_real_literal_kind(kind : @parser.RealLiteralKind) -> Sexp {
  match kind {
    RLitUnk => sexp_atom_string("RLitUnk")
    RLitDec(scale) => sexp_variant("RLitDec", [sexp_int64(scale)])
    RLitHex(scale) => sexp_variant("RLitHex", [sexp_int64(scale)])
  }
}

///|
fn sexp_of_constant(constant : @parser.Constant) -> Sexp {
  match constant {
    ConstInt(value) =>
      sexp_variant("ConstInt", [
        sexp_record([
          ("il_kind", sexp_of_int_literal_kind(value.kind)),
          ("il_int", sexp_bigint(value.value)),
        ]),
      ])
    ConstReal(value) =>
      sexp_variant("ConstReal", [
        sexp_record([
          ("rl_kind", sexp_of_real_literal_kind(value.kind)),
          (
            "rl_real",
            sexp_record([
              ("rv_sig", sexp_bigint(value.value.significand())),
              ("rv_pow2", sexp_bigint(value.value.pow2())),
              ("rv_pow5", sexp_bigint(value.value.pow5())),
            ]),
          ),
        ]),
      ])
    ConstStr(value) => sexp_variant("ConstStr", [sexp_atom(value)])
  }
}

///|
fn sexp_of_binary_logic_op(operator : @parser.BinaryLogicOp) -> Sexp {
  sexp_atom_string(
    match operator {
      DTand => "DTand"
      DTandAsym => "DTand_asym"
      DTor => "DTor"
      DTorAsym => "DTor_asym"
      DTimplies => "DTimplies"
      DTiff => "DTiff"
      DTby => "DTby"
      DTso => "DTso"
    },
  )
}

///|
fn sexp_of_quantifier(quantifier : @parser.Quantifier) -> Sexp {
  sexp_atom_string(
    match quantifier {
      DTforall => "DTforall"
      DTexists => "DTexists"
      DTlambda => "DTlambda"
    },
  )
}

///|
fn sexp_of_term_desc(desc : @parser.TermDesc) -> Sexp {
  match desc {
    Ttrue => sexp_variant("Ttrue", [])
    Tfalse => sexp_variant("Tfalse", [])
    Tconst(constant) => sexp_variant("Tconst", [sexp_of_constant(constant)])
    Tident(path) => sexp_variant("Tident", [sexp_of_qualid(path)])
    Tasref(path) => sexp_variant("Tasref", [sexp_of_qualid(path)])
    Tidapp(path, arguments) =>
      sexp_variant("Tidapp", [
        sexp_of_qualid(path),
        sexp_array(arguments, sexp_of_term),
      ])
    Tapply(function_, argument) =>
      sexp_variant("Tapply", [sexp_of_term(function_), sexp_of_term(argument)])
    Tinfix(left, operator, right) =>
      sexp_variant("Tinfix", [
        sexp_of_term(left),
        sexp_of_ident(operator),
        sexp_of_term(right),
      ])
    Tinnfix(left, operator, right) =>
      sexp_variant("Tinnfix", [
        sexp_of_term(left),
        sexp_of_ident(operator),
        sexp_of_term(right),
      ])
    Tbinop(left, operator, right) =>
      sexp_variant("Tbinop", [
        sexp_of_term(left),
        sexp_of_binary_logic_op(operator),
        sexp_of_term(right),
      ])
    Tbinnop(left, operator, right) =>
      sexp_variant("Tbinnop", [
        sexp_of_term(left),
        sexp_of_binary_logic_op(operator),
        sexp_of_term(right),
      ])
    Tnot(term) => sexp_variant("Tnot", [sexp_of_term(term)])
    Tif(condition, consequent, alternative) =>
      sexp_variant("Tif", [
        sexp_of_term(condition),
        sexp_of_term(consequent),
        sexp_of_term(alternative),
      ])
    Tquant(quantifier, binders, triggers, body) =>
      sexp_variant("Tquant", [
        sexp_of_quantifier(quantifier),
        sexp_array(binders, sexp_of_binder),
        sexp_array(triggers, trigger => sexp_array(trigger, sexp_of_term)),
        sexp_of_term(body),
      ])
    Teps(ident, ty, body) =>
      sexp_variant("Teps", [
        sexp_of_ident(ident),
        sexp_of_pty(ty),
        sexp_of_term(body),
      ])
    Tattr(attribute, term) =>
      sexp_variant("Tattr", [sexp_of_attribute(attribute), sexp_of_term(term)])
    Tlet(ident, value, body) =>
      sexp_variant("Tlet", [
        sexp_of_ident(ident),
        sexp_of_term(value),
        sexp_of_term(body),
      ])
    Tcase(scrutinee, branches) =>
      sexp_variant("Tcase", [
        sexp_of_term(scrutinee),
        sexp_array(branches, branch => {
          sexp_pair(branch, sexp_of_pattern, sexp_of_term)
        }),
      ])
    Tcast(term, ty) =>
      sexp_variant("Tcast", [sexp_of_term(term), sexp_of_pty(ty)])
    Ttuple(elements) =>
      sexp_variant("Ttuple", [sexp_array(elements, sexp_of_term)])
    Trecord(fields) =>
      sexp_variant("Trecord", [
        sexp_array(fields, field => {
          sexp_pair(field, sexp_of_qualid, sexp_of_term)
        }),
      ])
    Tupdate(base, fields) =>
      sexp_variant("Tupdate", [
        sexp_of_term(base),
        sexp_array(fields, field => {
          sexp_pair(field, sexp_of_qualid, sexp_of_term)
        }),
      ])
    Tscope(path, term) =>
      sexp_variant("Tscope", [sexp_of_qualid(path), sexp_of_term(term)])
    Tat(term, ident) =>
      sexp_variant("Tat", [sexp_of_term(term), sexp_of_ident(ident)])
  }
}

///|
fn sexp_of_term(term : @parser.Term) -> Sexp {
  sexp_record([
    ("term_desc", sexp_of_term_desc(term.desc)),
    ("term_loc", sexp_of_span(term.span)),
  ])
}

///|
fn sexp_of_invariant(invariant : @parser.Invariant) -> Sexp {
  sexp_array(invariant.terms, sexp_of_term)
}

///|
fn sexp_of_variant(variant : @parser.Variant) -> Sexp {
  sexp_array(variant.items, item => {
    sexp_pair(item, sexp_of_term, path => sexp_option(path, sexp_of_qualid))
  })
}

///|
fn sexp_of_postcondition(postcondition : @parser.PostCondition) -> Sexp {
  sexp_list([
    sexp_of_span(postcondition.span),
    sexp_array(postcondition.branches, branch => {
      sexp_pair(branch, sexp_of_pattern, sexp_of_term)
    }),
  ])
}

///|
fn sexp_of_exceptional_postcondition(
  postcondition : @parser.ExceptionalPostCondition,
) -> Sexp {
  sexp_list([
    sexp_of_span(postcondition.span),
    sexp_array(postcondition.branches, branch => {
      sexp_pair(branch, sexp_of_qualid, pair => {
        sexp_option(pair, pair => sexp_pair(pair, sexp_of_pattern, sexp_of_term))
      })
    }),
  ])
}

///|
fn sexp_of_spec(specification : @parser.Spec) -> Sexp {
  sexp_record([
    ("sp_pre", sexp_array(specification.preconditions, sexp_of_term)),
    ("sp_post", sexp_array(specification.postconditions, sexp_of_postcondition)),
    (
      "sp_xpost",
      sexp_array(
        specification.exceptional_postconditions,
        sexp_of_exceptional_postcondition,
      ),
    ),
    ("sp_reads", sexp_array(specification.reads, sexp_of_qualid)),
    ("sp_writes", sexp_array(specification.writes, sexp_of_term)),
    (
      "sp_alias",
      sexp_array(specification.aliases, item => {
        sexp_pair(item, sexp_of_term, sexp_of_term)
      }),
    ),
    ("sp_variant", sexp_of_variant(specification.variant)),
    ("sp_checkrw", sexp_bool(specification.check_reads_writes)),
    ("sp_diverge", sexp_bool(specification.diverges)),
    ("sp_partial", sexp_bool(specification.partial)),
  ])
}

///|
fn sexp_of_routine_kind(kind : @parser.RoutineKind) -> Sexp {
  sexp_atom_string(
    match kind {
      RKnone => "RKnone"
      RKlocal => "RKlocal"
      RKfunc => "RKfunc"
      RKpred => "RKpred"
      RKlemma => "RKlemma"
    },
  )
}

///|
fn sexp_of_mask(mask : @parser.Mask) -> Sexp {
  match mask {
    MaskVisible => sexp_atom_string("MaskVisible")
    MaskTuple(items) =>
      sexp_variant("MaskTuple", [sexp_array(items, sexp_of_mask)])
    MaskGhost => sexp_atom_string("MaskGhost")
  }
}

///|
fn sexp_of_for_direction(direction : @parser.ForDirection) -> Sexp {
  sexp_atom_string(
    match direction {
      To => "To"
      DownTo => "DownTo"
    },
  )
}

///|
fn sexp_of_assertion_kind(kind : @parser.AssertionKind) -> Sexp {
  sexp_atom_string(
    match kind {
      Assert => "Assert"
      Assume => "Assume"
      Check => "Check"
    },
  )
}

///|
fn sexp_of_regular_branch(branch : @parser.RegularBranch) -> Sexp {
  sexp_list([sexp_of_pattern(branch.pattern), sexp_of_expr(branch.body)])
}

///|
fn sexp_of_exception_branch(branch : @parser.ExceptionBranch) -> Sexp {
  sexp_list([
    sexp_of_qualid(branch.exception),
    sexp_option(branch.pattern, sexp_of_pattern),
    sexp_of_expr(branch.body),
  ])
}

///|
fn sexp_of_function_def(definition : @parser.FunctionDef) -> Sexp {
  sexp_list([
    sexp_of_ident(definition.name),
    sexp_bool(definition.ghost),
    sexp_of_routine_kind(definition.kind),
    sexp_array(definition.binders, sexp_of_binder),
    sexp_option(definition.return_type, sexp_of_pty),
    sexp_of_pattern(definition.return_pattern),
    sexp_of_mask(definition.mask),
    sexp_of_spec(definition.spec),
    sexp_of_expr(definition.body),
  ])
}

///|
fn sexp_of_assignment(assignment : @parser.Assignment) -> Sexp {
  sexp_list([
    sexp_of_expr(assignment.target),
    sexp_option(assignment.field, sexp_of_qualid),
    sexp_of_expr(assignment.value),
  ])
}

///|
fn sexp_of_expr_desc(desc : @parser.ExprDesc) -> Sexp {
  match desc {
    Eref => sexp_variant("Eref", [])
    Etrue => sexp_variant("Etrue", [])
    Efalse => sexp_variant("Efalse", [])
    Econst(constant) => sexp_variant("Econst", [sexp_of_constant(constant)])
    Eident(path) => sexp_variant("Eident", [sexp_of_qualid(path)])
    Easref(path) => sexp_variant("Easref", [sexp_of_qualid(path)])
    Eidapp(path, arguments) =>
      sexp_variant("Eidapp", [
        sexp_of_qualid(path),
        sexp_array(arguments, sexp_of_expr),
      ])
    Eapply(function_, argument) =>
      sexp_variant("Eapply", [sexp_of_expr(function_), sexp_of_expr(argument)])
    Einfix(left, operator, right) =>
      sexp_variant("Einfix", [
        sexp_of_expr(left),
        sexp_of_ident(operator),
        sexp_of_expr(right),
      ])
    Einnfix(left, operator, right) =>
      sexp_variant("Einnfix", [
        sexp_of_expr(left),
        sexp_of_ident(operator),
        sexp_of_expr(right),
      ])
    Elet(ident, ghost, kind, value, body) =>
      sexp_variant("Elet", [
        sexp_of_ident(ident),
        sexp_bool(ghost),
        sexp_of_routine_kind(kind),
        sexp_of_expr(value),
        sexp_of_expr(body),
      ])
    Erec(definitions, body) =>
      sexp_variant("Erec", [
        sexp_array(definitions, sexp_of_function_def),
        sexp_of_expr(body),
      ])
    Efun(binders, return_type, return_pattern, mask, spec, body) =>
      sexp_variant("Efun", [
        sexp_array(binders, sexp_of_binder),
        sexp_option(return_type, sexp_of_pty),
        sexp_of_pattern(return_pattern),
        sexp_of_mask(mask),
        sexp_of_spec(spec),
        sexp_of_expr(body),
      ])
    Eany(params, kind, return_type, return_pattern, mask, spec) =>
      sexp_variant("Eany", [
        sexp_array(params, sexp_of_param),
        sexp_of_routine_kind(kind),
        sexp_option(return_type, sexp_of_pty),
        sexp_of_pattern(return_pattern),
        sexp_of_mask(mask),
        sexp_of_spec(spec),
      ])
    Etuple(elements) =>
      sexp_variant("Etuple", [sexp_array(elements, sexp_of_expr)])
    Erecord(fields) =>
      sexp_variant("Erecord", [
        sexp_array(fields, field => {
          sexp_pair(field, sexp_of_qualid, sexp_of_expr)
        }),
      ])
    Eupdate(base, fields) =>
      sexp_variant("Eupdate", [
        sexp_of_expr(base),
        sexp_array(fields, field => {
          sexp_pair(field, sexp_of_qualid, sexp_of_expr)
        }),
      ])
    Eassign(assignments) =>
      sexp_variant("Eassign", [sexp_array(assignments, sexp_of_assignment)])
    Esequence(first, second) =>
      sexp_variant("Esequence", [sexp_of_expr(first), sexp_of_expr(second)])
    Eif(condition, consequent, alternative) =>
      sexp_variant("Eif", [
        sexp_of_expr(condition),
        sexp_of_expr(consequent),
        sexp_of_expr(alternative),
      ])
    Ewhile(condition, invariant, variant, body) =>
      sexp_variant("Ewhile", [
        sexp_of_expr(condition),
        sexp_of_invariant(invariant),
        sexp_of_variant(variant),
        sexp_of_expr(body),
      ])
    Eand(left, right) =>
      sexp_variant("Eand", [sexp_of_expr(left), sexp_of_expr(right)])
    Eor(left, right) =>
      sexp_variant("Eor", [sexp_of_expr(left), sexp_of_expr(right)])
    Enot(expression) => sexp_variant("Enot", [sexp_of_expr(expression)])
    Ematch(scrutinee, regular, exceptions) =>
      sexp_variant("Ematch", [
        sexp_of_expr(scrutinee),
        sexp_array(regular, sexp_of_regular_branch),
        sexp_array(exceptions, sexp_of_exception_branch),
      ])
    Eabsurd => sexp_variant("Eabsurd", [])
    Epure(term) => sexp_variant("Epure", [sexp_of_term(term)])
    Eidpur(path) => sexp_variant("Eidpur", [sexp_of_qualid(path)])
    Eraise(exception, argument) =>
      sexp_variant("Eraise", [
        sexp_of_qualid(exception),
        sexp_option(argument, sexp_of_expr),
      ])
    Eexn(ident, ty, mask, body) =>
      sexp_variant("Eexn", [
        sexp_of_ident(ident),
        sexp_of_pty(ty),
        sexp_of_mask(mask),
        sexp_of_expr(body),
      ])
    Eoptexn(ident, mask, body) =>
      sexp_variant("Eoptexn", [
        sexp_of_ident(ident),
        sexp_of_mask(mask),
        sexp_of_expr(body),
      ])
    Efor(ident, lower, direction, upper, invariant, body) =>
      sexp_variant("Efor", [
        sexp_of_ident(ident),
        sexp_of_expr(lower),
        sexp_of_for_direction(direction),
        sexp_of_expr(upper),
        sexp_of_invariant(invariant),
        sexp_of_expr(body),
      ])
    Eassert(kind, term) =>
      sexp_variant("Eassert", [sexp_of_assertion_kind(kind), sexp_of_term(term)])
    Escope(path, expression) =>
      sexp_variant("Escope", [sexp_of_qualid(path), sexp_of_expr(expression)])
    Elabel(ident, expression) =>
      sexp_variant("Elabel", [sexp_of_ident(ident), sexp_of_expr(expression)])
    Ecast(expression, ty) =>
      sexp_variant("Ecast", [sexp_of_expr(expression), sexp_of_pty(ty)])
    Eghost(expression) => sexp_variant("Eghost", [sexp_of_expr(expression)])
    Eattr(attribute, expression) =>
      sexp_variant("Eattr", [
        sexp_of_attribute(attribute),
        sexp_of_expr(expression),
      ])
  }
}

///|
fn sexp_of_expr(expression : @parser.Expr) -> Sexp {
  sexp_record([
    ("expr_desc", sexp_of_expr_desc(expression.desc)),
    ("expr_loc", sexp_of_span(expression.span)),
  ])
}

///|
fn sexp_of_field(field : @parser.Field) -> Sexp {
  sexp_record([
    ("f_loc", sexp_of_span(field.span)),
    ("f_ident", sexp_of_ident(field.ident)),
    ("f_pty", sexp_of_pty(field.field_type)),
    ("f_mutable", sexp_bool(field.mutable)),
    ("f_ghost", sexp_bool(field.ghost)),
  ])
}

///|
fn sexp_of_algebraic_case(case : @parser.AlgebraicCase) -> Sexp {
  sexp_list([
    sexp_of_span(case.span),
    sexp_of_ident(case.ident),
    sexp_array(case.params, sexp_of_param),
  ])
}

///|
fn sexp_of_type_def(definition : @parser.TypeDef) -> Sexp {
  match definition {
    TDalias(ty) => sexp_variant("TDalias", [sexp_of_pty(ty)])
    TDalgebraic(cases) =>
      sexp_variant("TDalgebraic", [sexp_array(cases, sexp_of_algebraic_case)])
    TDrecord(fields) =>
      sexp_variant("TDrecord", [sexp_array(fields, sexp_of_field)])
    TDrange(lower, upper) =>
      sexp_variant("TDrange", [sexp_bigint(lower), sexp_bigint(upper)])
    TDfloat(exponent, significand) =>
      sexp_variant("TDfloat", [sexp_int64(exponent), sexp_int64(significand)])
  }
}

///|
fn sexp_of_visibility(visibility : @parser.Visibility) -> Sexp {
  sexp_atom_string(
    match visibility {
      Public => "Public"
      Private => "Private"
      Abstract => "Abstract"
    },
  )
}

///|
fn sexp_of_type_decl(declaration : @parser.TypeDecl) -> Sexp {
  sexp_record([
    ("td_loc", sexp_of_span(declaration.span)),
    ("td_ident", sexp_of_ident(declaration.ident)),
    ("td_params", sexp_array(declaration.params, sexp_of_ident)),
    ("td_vis", sexp_of_visibility(declaration.visibility)),
    ("td_mut", sexp_bool(declaration.mutable)),
    ("td_inv", sexp_of_invariant(declaration.invariant)),
    ("td_wit", sexp_option(declaration.witness, sexp_of_expr)),
    ("td_def", sexp_of_type_def(declaration.definition)),
  ])
}

///|
fn sexp_of_logic_decl(declaration : @parser.LogicDecl) -> Sexp {
  sexp_record([
    ("ld_loc", sexp_of_span(declaration.span)),
    ("ld_ident", sexp_of_ident(declaration.ident)),
    ("ld_params", sexp_array(declaration.params, sexp_of_param)),
    ("ld_type", sexp_option(declaration.return_type, sexp_of_pty)),
    ("ld_def", sexp_option(declaration.definition, sexp_of_term)),
  ])
}

///|
fn sexp_of_inductive_case(case : @parser.InductiveCase) -> Sexp {
  sexp_list([
    sexp_of_span(case.span),
    sexp_of_ident(case.ident),
    sexp_of_term(case.body),
  ])
}

///|
fn sexp_of_inductive_decl(declaration : @parser.InductiveDecl) -> Sexp {
  sexp_record([
    ("in_loc", sexp_of_span(declaration.span)),
    ("in_ident", sexp_of_ident(declaration.ident)),
    ("in_params", sexp_array(declaration.params, sexp_of_param)),
    ("in_def", sexp_array(declaration.cases, sexp_of_inductive_case)),
  ])
}

///|
fn sexp_of_inductive_sign(sign : @parser.InductiveSign) -> Sexp {
  sexp_atom_string(
    match sign {
      Ind => "Ind"
      Coind => "Coind"
    },
  )
}

///|
fn sexp_of_proposition_kind(kind : @parser.PropositionKind) -> Sexp {
  sexp_atom_string(
    match kind {
      Plemma => "Plemma"
      Paxiom => "Paxiom"
      Pgoal => "Pgoal"
    },
  )
}

///|
fn sexp_of_meta_arg(argument : @parser.MetaArg) -> Sexp {
  match argument {
    Mty(ty) => sexp_variant("Mty", [sexp_of_pty(ty)])
    Mfs(path) => sexp_variant("Mfs", [sexp_of_qualid(path)])
    Mps(path) => sexp_variant("Mps", [sexp_of_qualid(path)])
    Max(path) => sexp_variant("Max", [sexp_of_qualid(path)])
    Mlm(path) => sexp_variant("Mlm", [sexp_of_qualid(path)])
    Mgl(path) => sexp_variant("Mgl", [sexp_of_qualid(path)])
    Mval(path) => sexp_variant("Mval", [sexp_of_qualid(path)])
    Mstr(value) => sexp_variant("Mstr", [sexp_atom(value)])
    Mint(value) => sexp_variant("Mint", [sexp_int64(value)])
  }
}

///|
fn sexp_of_clone_substitution(substitution : @parser.CloneSubstitution) -> Sexp {
  match substitution {
    CStsym(source, parameters, target) =>
      sexp_variant("CStsym", [
        sexp_of_qualid(source),
        sexp_array(parameters, sexp_of_ident),
        sexp_of_pty(target),
      ])
    CSfsym(source, target) =>
      sexp_variant("CSfsym", [sexp_of_qualid(source), sexp_of_qualid(target)])
    CSpsym(source, target) =>
      sexp_variant("CSpsym", [sexp_of_qualid(source), sexp_of_qualid(target)])
    CSvsym(source, target) =>
      sexp_variant("CSvsym", [sexp_of_qualid(source), sexp_of_qualid(target)])
    CSxsym(source, target) =>
      sexp_variant("CSxsym", [sexp_of_qualid(source), sexp_of_qualid(target)])
    CSprop(kind) => sexp_variant("CSprop", [sexp_of_proposition_kind(kind)])
    CSaxiom(path) => sexp_variant("CSaxiom", [sexp_of_qualid(path)])
    CSlemma(path) => sexp_variant("CSlemma", [sexp_of_qualid(path)])
    CSgoal(path) => sexp_variant("CSgoal", [sexp_of_qualid(path)])
  }
}

///|
fn sexp_of_decl(declaration : @parser.Decl) -> Sexp {
  match declaration {
    Dtype(declarations) =>
      sexp_variant("Dtype", [sexp_array(declarations, sexp_of_type_decl)])
    Dlogic(declarations) =>
      sexp_variant("Dlogic", [sexp_array(declarations, sexp_of_logic_decl)])
    Dind(sign, declarations) =>
      sexp_variant("Dind", [
        sexp_of_inductive_sign(sign),
        sexp_array(declarations, sexp_of_inductive_decl),
      ])
    Dprop(kind, ident, term) =>
      sexp_variant("Dprop", [
        sexp_of_proposition_kind(kind),
        sexp_of_ident(ident),
        sexp_of_term(term),
      ])
    Dlet(ident, ghost, kind, expression) =>
      sexp_variant("Dlet", [
        sexp_of_ident(ident),
        sexp_bool(ghost),
        sexp_of_routine_kind(kind),
        sexp_of_expr(expression),
      ])
    Drec(definitions) =>
      sexp_variant("Drec", [sexp_array(definitions, sexp_of_function_def)])
    Dexn(ident, ty, mask) =>
      sexp_variant("Dexn", [
        sexp_of_ident(ident),
        sexp_of_pty(ty),
        sexp_of_mask(mask),
      ])
    Dmeta(ident, arguments) =>
      sexp_variant("Dmeta", [
        sexp_of_ident(ident),
        sexp_array(arguments, sexp_of_meta_arg),
      ])
    Dcloneexport(span, source, substitutions) =>
      sexp_variant("Dcloneexport", [
        sexp_of_span(span),
        sexp_of_qualid(source),
        sexp_array(substitutions, sexp_of_clone_substitution),
      ])
    Duseexport(source) => sexp_variant("Duseexport", [sexp_of_qualid(source)])
    Dcloneimport(span, import_, source, alias_, substitutions) =>
      sexp_variant("Dcloneimport", [
        sexp_of_span(span),
        sexp_bool(import_),
        sexp_of_qualid(source),
        sexp_option(alias_, sexp_of_ident),
        sexp_array(substitutions, sexp_of_clone_substitution),
      ])
    Duseimport(span, import_, sources) =>
      sexp_variant("Duseimport", [
        sexp_of_span(span),
        sexp_bool(import_),
        sexp_array(sources, source => {
          sexp_pair(source, sexp_of_qualid, alias_ => {
            sexp_option(alias_, sexp_of_ident)
          })
        }),
      ])
    Dimport(source) => sexp_variant("Dimport", [sexp_of_qualid(source)])
    Dscope(span, import_, ident, declarations) =>
      sexp_variant("Dscope", [
        sexp_of_span(span),
        sexp_bool(import_),
        sexp_of_ident(ident),
        sexp_array(declarations, sexp_of_decl),
      ])
  }
}

///|
fn sexp_of_module(module_ : @parser.MlwModule) -> Sexp {
  // Why3 1.7.2 Ptree stores only the module identifier and declarations.
  sexp_list([
    sexp_of_ident(module_.name),
    sexp_array(module_.declarations, sexp_of_decl),
  ])
}

///|
fn sexp_of_mlw_file(file : @parser.MlwFile) -> Sexp {
  match file {
    Modules(modules) =>
      sexp_variant("Modules", [sexp_array(modules, sexp_of_module)])
    Decls(declarations) =>
      sexp_variant("Decls", [sexp_array(declarations, sexp_of_decl)])
  }
}

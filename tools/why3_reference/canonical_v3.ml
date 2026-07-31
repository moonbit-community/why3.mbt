(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit canonical v3 reference adapter, modified 2026-07-24.    *)
(*                                                                  *)
(********************************************************************)

open Why3
open Yojson.Safe

let fail message = invalid_arg ("canonical_v3: " ^ message)

let hex_digits = "0123456789abcdef"

let hex_string value =
  let result = Bytes.create (String.length value * 2) in
  String.iteri
    (fun index character ->
      let byte = Char.code character in
      Bytes.set result (index * 2) hex_digits.[byte lsr 4];
      Bytes.set result (index * 2 + 1) hex_digits.[byte land 0x0f])
    value;
  Bytes.unsafe_to_string result

let node name fields = `List (`String name :: fields)
let unit_node = node "Unit" []
let boolean value = node "Boolean" [`Bool value]
let bytes value = node "Bytes" [`String (hex_string value)]
let integer_string value = node "Integer" [`String value]
let integer value = integer_string (string_of_int value)
let bigint value = integer_string (BigInt.to_string value)
let sequence values = node "Sequence" [`List values]
let product values = node "Product" [`List values]
let none = node "Option.None" []
let some value = node "Option.Some" [value]
let option encode = function None -> none | Some value -> some (encode value)
let variant name payload = node name [payload]
let variant0 name = variant name unit_node
let variant1 name value = variant name value
let variantn name values = variant name (product values)
let list encode values = sequence (List.map encode values)
let pair left right = product [left; right]

let compact value = Yojson.Safe.to_string ~std:true value
let canonical_bytes value = compact value ^ "\n"
let sha256_string value = Digestif.SHA256.(to_hex (digest_string value))

type source = {
  label : string;
  absolute : string;
  bytes : string;
  line_starts : int array;
}

let read_source label path =
  let channel = open_in_bin path in
  let length = in_channel_length channel in
  let source_bytes = really_input_string channel length in
  close_in channel;
  let starts = ref [0] in
  String.iteri
    (fun index character ->
      if character = '\n' then starts := (index + 1) :: !starts)
    source_bytes;
  { label;
    absolute = Unix.realpath path;
    bytes = source_bytes;
    line_starts = Array.of_list (List.rev !starts) }

let source_offset source file line column =
  let absolute = Unix.realpath file in
  if absolute <> source.absolute then
    fail ("source location escapes selected fixture: " ^ file);
  if line < 1 || line > Array.length source.line_starts then
    fail "source line is out of bounds";
  let offset = source.line_starts.(line - 1) + column in
  if offset < 0 || offset > String.length source.bytes then
    fail "source column is out of bounds";
  offset

let source_span source position =
  let file, start_line, start_column, end_line, end_column =
    Loc.get position
  in
  node "SourceSpan"
    [ `String (hex_string source.label);
      `Int (source_offset source file start_line start_column);
      `Int (source_offset source file end_line end_column);
      `Int start_line;
      `Int start_column;
      `Int end_line;
      `Int end_column ]

let canonical_int_literal_kind = function
  | Number.ILitUnk -> variant0 "Number.int_literal_kind.ILitUnk"
  | Number.ILitDec -> variant0 "Number.int_literal_kind.ILitDec"
  | Number.ILitHex -> variant0 "Number.int_literal_kind.ILitHex"
  | Number.ILitOct -> variant0 "Number.int_literal_kind.ILitOct"
  | Number.ILitBin -> variant0 "Number.int_literal_kind.ILitBin"

let canonical_int_constant literal =
  node "Number.int_constant"
    [ canonical_int_literal_kind literal.Number.il_kind;
      bigint literal.Number.il_int ]

let canonical_real_literal_kind = function
  | Number.RLitUnk -> variant0 "Number.real_literal_kind.RLitUnk"
  | Number.RLitDec exponent ->
      variant1 "Number.real_literal_kind.RLitDec" (integer exponent)
  | Number.RLitHex exponent ->
      variant1 "Number.real_literal_kind.RLitHex" (integer exponent)

let canonical_real_value value =
  node "Number.real_value"
    [ bigint value.Number.rv_sig;
      bigint value.Number.rv_pow2;
      bigint value.Number.rv_pow5 ]

let canonical_real_constant literal =
  node "Number.real_constant"
    [ canonical_real_literal_kind literal.Number.rl_kind;
      canonical_real_value literal.Number.rl_real ]

let canonical_constant = function
  | Constant.ConstInt literal ->
      variant1 "Constant.constant.ConstInt"
        (canonical_int_constant literal)
  | Constant.ConstReal literal ->
      variant1 "Constant.constant.ConstReal"
        (canonical_real_constant literal)
  | Constant.ConstStr value ->
      variant1 "Constant.constant.ConstStr" (bytes value)

let canonical_dbinop = function
  | Dterm.DTand -> variant0 "Dterm.dbinop.DTand"
  | Dterm.DTand_asym -> variant0 "Dterm.dbinop.DTand_asym"
  | Dterm.DTor -> variant0 "Dterm.dbinop.DTor"
  | Dterm.DTor_asym -> variant0 "Dterm.dbinop.DTor_asym"
  | Dterm.DTimplies -> variant0 "Dterm.dbinop.DTimplies"
  | Dterm.DTiff -> variant0 "Dterm.dbinop.DTiff"
  | Dterm.DTby -> variant0 "Dterm.dbinop.DTby"
  | Dterm.DTso -> variant0 "Dterm.dbinop.DTso"

let canonical_dquant = function
  | Dterm.DTforall -> variant0 "Dterm.dquant.DTforall"
  | Dterm.DTexists -> variant0 "Dterm.dquant.DTexists"
  | Dterm.DTlambda -> variant0 "Dterm.dquant.DTlambda"

let canonical_rs_kind = function
  | Expr.RKnone -> variant0 "Expr.rs_kind.RKnone"
  | Expr.RKlocal -> variant0 "Expr.rs_kind.RKlocal"
  | Expr.RKfunc -> variant0 "Expr.rs_kind.RKfunc"
  | Expr.RKpred -> variant0 "Expr.rs_kind.RKpred"
  | Expr.RKlemma -> variant0 "Expr.rs_kind.RKlemma"

let canonical_assertion_kind = function
  | Expr.Assert -> variant0 "Expr.assertion_kind.Assert"
  | Expr.Assume -> variant0 "Expr.assertion_kind.Assume"
  | Expr.Check -> variant0 "Expr.assertion_kind.Check"

let canonical_for_direction = function
  | Expr.To -> variant0 "Expr.for_direction.To"
  | Expr.DownTo -> variant0 "Expr.for_direction.DownTo"

let rec canonical_mask = function
  | Ity.MaskVisible -> variant0 "Ity.mask.MaskVisible"
  | Ity.MaskTuple masks ->
      variant1 "Ity.mask.MaskTuple" (list canonical_mask masks)
  | Ity.MaskGhost -> variant0 "Ity.mask.MaskGhost"

let canonical_ind_sign = function
  | Decl.Ind -> variant0 "Decl.ind_sign.Ind"
  | Decl.Coind -> variant0 "Decl.ind_sign.Coind"

let canonical_prop_kind = function
  | Decl.Plemma -> variant0 "Decl.prop_kind.Plemma"
  | Decl.Paxiom -> variant0 "Decl.prop_kind.Paxiom"
  | Decl.Pgoal -> variant0 "Decl.prop_kind.Pgoal"

let canonical_attr source = function
  | Ptree.ATstr attribute ->
      variant1 "Ptree.attr.ATstr" (bytes attribute.Ident.attr_string)
  | Ptree.ATpos position ->
      variant1 "Ptree.attr.ATpos" (source_span source position)

let canonical_ident source ident =
  node "Ptree.ident"
    [ bytes ident.Ptree.id_str;
      list (canonical_attr source) ident.Ptree.id_ats;
      source_span source ident.Ptree.id_loc ]

let rec canonical_qualid source = function
  | Ptree.Qident ident ->
      variant1 "Ptree.qualid.Qident" (canonical_ident source ident)
  | Ptree.Qdot (prefix, ident) ->
      variantn "Ptree.qualid.Qdot"
        [canonical_qualid source prefix; canonical_ident source ident]

let rec canonical_pty source = function
  | Ptree.PTtyvar ident ->
      variant1 "Ptree.pty.PTtyvar" (canonical_ident source ident)
  | Ptree.PTtyapp (qualid, arguments) ->
      variantn "Ptree.pty.PTtyapp"
        [ canonical_qualid source qualid;
          list (canonical_pty source) arguments ]
  | Ptree.PTtuple arguments ->
      variant1 "Ptree.pty.PTtuple" (list (canonical_pty source) arguments)
  | Ptree.PTref arguments ->
      variant1 "Ptree.pty.PTref" (list (canonical_pty source) arguments)
  | Ptree.PTarrow (argument, result) ->
      variantn "Ptree.pty.PTarrow"
        [canonical_pty source argument; canonical_pty source result]
  | Ptree.PTscope (scope, ty) ->
      variantn "Ptree.pty.PTscope"
        [canonical_qualid source scope; canonical_pty source ty]
  | Ptree.PTparen ty ->
      variant1 "Ptree.pty.PTparen" (canonical_pty source ty)
  | Ptree.PTpure ty ->
      variant1 "Ptree.pty.PTpure" (canonical_pty source ty)

let rec canonical_pattern source pattern =
  node "Ptree.pattern"
    [ canonical_pat_desc source pattern.Ptree.pat_desc;
      source_span source pattern.Ptree.pat_loc ]

and canonical_pat_desc source = function
  | Ptree.Pwild -> variant0 "Ptree.pat_desc.Pwild"
  | Ptree.Pvar ident ->
      variant1 "Ptree.pat_desc.Pvar" (canonical_ident source ident)
  | Ptree.Papp (qualid, arguments) ->
      variantn "Ptree.pat_desc.Papp"
        [ canonical_qualid source qualid;
          list (canonical_pattern source) arguments ]
  | Ptree.Prec fields ->
      variant1 "Ptree.pat_desc.Prec"
        (list
           (fun (qualid, pattern) ->
             pair
               (canonical_qualid source qualid)
               (canonical_pattern source pattern))
           fields)
  | Ptree.Ptuple patterns ->
      variant1 "Ptree.pat_desc.Ptuple"
        (list (canonical_pattern source) patterns)
  | Ptree.Pas (pattern, ident, ghost) ->
      variantn "Ptree.pat_desc.Pas"
        [ canonical_pattern source pattern;
          canonical_ident source ident;
          boolean ghost ]
  | Ptree.Por (left, right) ->
      variantn "Ptree.pat_desc.Por"
        [canonical_pattern source left; canonical_pattern source right]
  | Ptree.Pcast (pattern, ty) ->
      variantn "Ptree.pat_desc.Pcast"
        [canonical_pattern source pattern; canonical_pty source ty]
  | Ptree.Pscope (scope, pattern) ->
      variantn "Ptree.pat_desc.Pscope"
        [canonical_qualid source scope; canonical_pattern source pattern]
  | Ptree.Pparen pattern ->
      variant1 "Ptree.pat_desc.Pparen" (canonical_pattern source pattern)
  | Ptree.Pghost pattern ->
      variant1 "Ptree.pat_desc.Pghost" (canonical_pattern source pattern)

let canonical_binder source (location, ident, ghost, ty) =
  product
    [ source_span source location;
      option (canonical_ident source) ident;
      boolean ghost;
      option (canonical_pty source) ty ]

let canonical_param source (location, ident, ghost, ty) =
  product
    [ source_span source location;
      option (canonical_ident source) ident;
      boolean ghost;
      canonical_pty source ty ]

let rec canonical_term source term =
  node "Ptree.term"
    [ canonical_term_desc source term.Ptree.term_desc;
      source_span source term.Ptree.term_loc ]

and canonical_term_desc source = function
  | Ptree.Ttrue -> variant0 "Ptree.term_desc.Ttrue"
  | Ptree.Tfalse -> variant0 "Ptree.term_desc.Tfalse"
  | Ptree.Tconst constant ->
      variant1 "Ptree.term_desc.Tconst" (canonical_constant constant)
  | Ptree.Tident qualid ->
      variant1 "Ptree.term_desc.Tident" (canonical_qualid source qualid)
  | Ptree.Tasref qualid ->
      variant1 "Ptree.term_desc.Tasref" (canonical_qualid source qualid)
  | Ptree.Tidapp (qualid, arguments) ->
      variantn "Ptree.term_desc.Tidapp"
        [ canonical_qualid source qualid;
          list (canonical_term source) arguments ]
  | Ptree.Tapply (function_, argument) ->
      variantn "Ptree.term_desc.Tapply"
        [canonical_term source function_; canonical_term source argument]
  | Ptree.Tinfix (left, operator, right) ->
      variantn "Ptree.term_desc.Tinfix"
        [ canonical_term source left;
          canonical_ident source operator;
          canonical_term source right ]
  | Ptree.Tinnfix (left, operator, right) ->
      variantn "Ptree.term_desc.Tinnfix"
        [ canonical_term source left;
          canonical_ident source operator;
          canonical_term source right ]
  | Ptree.Tbinop (left, operator, right) ->
      variantn "Ptree.term_desc.Tbinop"
        [ canonical_term source left;
          canonical_dbinop operator;
          canonical_term source right ]
  | Ptree.Tbinnop (left, operator, right) ->
      variantn "Ptree.term_desc.Tbinnop"
        [ canonical_term source left;
          canonical_dbinop operator;
          canonical_term source right ]
  | Ptree.Tnot inner ->
      variant1 "Ptree.term_desc.Tnot" (canonical_term source inner)
  | Ptree.Tif (condition, consequent, alternative) ->
      variantn "Ptree.term_desc.Tif"
        [ canonical_term source condition;
          canonical_term source consequent;
          canonical_term source alternative ]
  | Ptree.Tquant (quantifier, binders, triggers, body) ->
      variantn "Ptree.term_desc.Tquant"
        [ canonical_dquant quantifier;
          list (canonical_binder source) binders;
          list (list (canonical_term source)) triggers;
          canonical_term source body ]
  | Ptree.Teps (ident, ty, body) ->
      variantn "Ptree.term_desc.Teps"
        [ canonical_ident source ident;
          canonical_pty source ty;
          canonical_term source body ]
  | Ptree.Tattr (attribute, term) ->
      variantn "Ptree.term_desc.Tattr"
        [canonical_attr source attribute; canonical_term source term]
  | Ptree.Tlet (ident, value, body) ->
      variantn "Ptree.term_desc.Tlet"
        [ canonical_ident source ident;
          canonical_term source value;
          canonical_term source body ]
  | Ptree.Tcase (scrutinee, branches) ->
      variantn "Ptree.term_desc.Tcase"
        [ canonical_term source scrutinee;
          list
            (fun (pattern, body) ->
              pair
                (canonical_pattern source pattern)
                (canonical_term source body))
            branches ]
  | Ptree.Tcast (term, ty) ->
      variantn "Ptree.term_desc.Tcast"
        [canonical_term source term; canonical_pty source ty]
  | Ptree.Ttuple terms ->
      variant1 "Ptree.term_desc.Ttuple" (list (canonical_term source) terms)
  | Ptree.Trecord fields ->
      variant1 "Ptree.term_desc.Trecord"
        (list
           (fun (qualid, term) ->
             pair
               (canonical_qualid source qualid)
               (canonical_term source term))
           fields)
  | Ptree.Tupdate (base, fields) ->
      variantn "Ptree.term_desc.Tupdate"
        [ canonical_term source base;
          list
            (fun (qualid, term) ->
              pair
                (canonical_qualid source qualid)
                (canonical_term source term))
            fields ]
  | Ptree.Tscope (scope, term) ->
      variantn "Ptree.term_desc.Tscope"
        [canonical_qualid source scope; canonical_term source term]
  | Ptree.Tat (term, label) ->
      variantn "Ptree.term_desc.Tat"
        [canonical_term source term; canonical_ident source label]

let canonical_post source (location, cases) =
  pair
    (source_span source location)
    (list
       (fun (pattern, term) ->
         pair
           (canonical_pattern source pattern)
           (canonical_term source term))
       cases)

let canonical_xpost source (location, cases) =
  pair
    (source_span source location)
    (list
       (fun (exception_, result) ->
         pair
           (canonical_qualid source exception_)
           (option
              (fun (pattern, term) ->
                pair
                  (canonical_pattern source pattern)
                  (canonical_term source term))
              result))
       cases)

let canonical_variant source values =
  list
    (fun (term, relation) ->
      pair
        (canonical_term source term)
        (option (canonical_qualid source) relation))
    values

let canonical_spec source spec =
  node "Ptree.spec"
    [ list (canonical_term source) spec.Ptree.sp_pre;
      list (canonical_post source) spec.Ptree.sp_post;
      list (canonical_xpost source) spec.Ptree.sp_xpost;
      list (canonical_qualid source) spec.Ptree.sp_reads;
      list (canonical_term source) spec.Ptree.sp_writes;
      list
        (fun (left, right) ->
          pair (canonical_term source left) (canonical_term source right))
        spec.Ptree.sp_alias;
      canonical_variant source spec.Ptree.sp_variant;
      boolean spec.Ptree.sp_checkrw;
      boolean spec.Ptree.sp_diverge;
      boolean spec.Ptree.sp_partial ]

let rec canonical_expr source expression =
  node "Ptree.expr"
    [ canonical_expr_desc source expression.Ptree.expr_desc;
      source_span source expression.Ptree.expr_loc ]

and canonical_expr_desc source = function
  | Ptree.Eref -> variant0 "Ptree.expr_desc.Eref"
  | Ptree.Etrue -> variant0 "Ptree.expr_desc.Etrue"
  | Ptree.Efalse -> variant0 "Ptree.expr_desc.Efalse"
  | Ptree.Econst constant ->
      variant1 "Ptree.expr_desc.Econst" (canonical_constant constant)
  | Ptree.Eident qualid ->
      variant1 "Ptree.expr_desc.Eident" (canonical_qualid source qualid)
  | Ptree.Easref qualid ->
      variant1 "Ptree.expr_desc.Easref" (canonical_qualid source qualid)
  | Ptree.Eidapp (qualid, arguments) ->
      variantn "Ptree.expr_desc.Eidapp"
        [ canonical_qualid source qualid;
          list (canonical_expr source) arguments ]
  | Ptree.Eapply (function_, argument) ->
      variantn "Ptree.expr_desc.Eapply"
        [canonical_expr source function_; canonical_expr source argument]
  | Ptree.Einfix (left, operator, right) ->
      variantn "Ptree.expr_desc.Einfix"
        [ canonical_expr source left;
          canonical_ident source operator;
          canonical_expr source right ]
  | Ptree.Einnfix (left, operator, right) ->
      variantn "Ptree.expr_desc.Einnfix"
        [ canonical_expr source left;
          canonical_ident source operator;
          canonical_expr source right ]
  | Ptree.Elet (ident, ghost, kind, value, body) ->
      variantn "Ptree.expr_desc.Elet"
        [ canonical_ident source ident;
          boolean ghost;
          canonical_rs_kind kind;
          canonical_expr source value;
          canonical_expr source body ]
  | Ptree.Erec (definitions, body) ->
      variantn "Ptree.expr_desc.Erec"
        [ list (canonical_fundef source) definitions;
          canonical_expr source body ]
  | Ptree.Efun (binders, result, pattern, mask, spec, body) ->
      variantn "Ptree.expr_desc.Efun"
        [ list (canonical_binder source) binders;
          option (canonical_pty source) result;
          canonical_pattern source pattern;
          canonical_mask mask;
          canonical_spec source spec;
          canonical_expr source body ]
  | Ptree.Eany (parameters, kind, result, pattern, mask, spec) ->
      variantn "Ptree.expr_desc.Eany"
        [ list (canonical_param source) parameters;
          canonical_rs_kind kind;
          option (canonical_pty source) result;
          canonical_pattern source pattern;
          canonical_mask mask;
          canonical_spec source spec ]
  | Ptree.Etuple expressions ->
      variant1 "Ptree.expr_desc.Etuple"
        (list (canonical_expr source) expressions)
  | Ptree.Erecord fields ->
      variant1 "Ptree.expr_desc.Erecord"
        (list
           (fun (qualid, expression) ->
             pair
               (canonical_qualid source qualid)
               (canonical_expr source expression))
           fields)
  | Ptree.Eupdate (base, fields) ->
      variantn "Ptree.expr_desc.Eupdate"
        [ canonical_expr source base;
          list
            (fun (qualid, expression) ->
              pair
                (canonical_qualid source qualid)
                (canonical_expr source expression))
            fields ]
  | Ptree.Eassign assignments ->
      variant1 "Ptree.expr_desc.Eassign"
        (list
           (fun (target, field, value) ->
             product
               [ canonical_expr source target;
                 option (canonical_qualid source) field;
                 canonical_expr source value ])
           assignments)
  | Ptree.Esequence (first, second) ->
      variantn "Ptree.expr_desc.Esequence"
        [canonical_expr source first; canonical_expr source second]
  | Ptree.Eif (condition, consequent, alternative) ->
      variantn "Ptree.expr_desc.Eif"
        [ canonical_expr source condition;
          canonical_expr source consequent;
          canonical_expr source alternative ]
  | Ptree.Ewhile (condition, invariants, variants, body) ->
      variantn "Ptree.expr_desc.Ewhile"
        [ canonical_expr source condition;
          list (canonical_term source) invariants;
          canonical_variant source variants;
          canonical_expr source body ]
  | Ptree.Eand (left, right) ->
      variantn "Ptree.expr_desc.Eand"
        [canonical_expr source left; canonical_expr source right]
  | Ptree.Eor (left, right) ->
      variantn "Ptree.expr_desc.Eor"
        [canonical_expr source left; canonical_expr source right]
  | Ptree.Enot expression ->
      variant1 "Ptree.expr_desc.Enot" (canonical_expr source expression)
  | Ptree.Ematch (scrutinee, regular, exceptional) ->
      variantn "Ptree.expr_desc.Ematch"
        [ canonical_expr source scrutinee;
          list
            (fun (pattern, body) ->
              pair
                (canonical_pattern source pattern)
                (canonical_expr source body))
            regular;
          list
            (fun (exception_, pattern, body) ->
              product
                [ canonical_qualid source exception_;
                  option (canonical_pattern source) pattern;
                  canonical_expr source body ])
            exceptional ]
  | Ptree.Eabsurd -> variant0 "Ptree.expr_desc.Eabsurd"
  | Ptree.Epure term ->
      variant1 "Ptree.expr_desc.Epure" (canonical_term source term)
  | Ptree.Eidpur qualid ->
      variant1 "Ptree.expr_desc.Eidpur" (canonical_qualid source qualid)
  | Ptree.Eraise (exception_, argument) ->
      variantn "Ptree.expr_desc.Eraise"
        [ canonical_qualid source exception_;
          option (canonical_expr source) argument ]
  | Ptree.Eexn (ident, ty, mask, body) ->
      variantn "Ptree.expr_desc.Eexn"
        [ canonical_ident source ident;
          canonical_pty source ty;
          canonical_mask mask;
          canonical_expr source body ]
  | Ptree.Eoptexn (ident, mask, body) ->
      variantn "Ptree.expr_desc.Eoptexn"
        [ canonical_ident source ident;
          canonical_mask mask;
          canonical_expr source body ]
  | Ptree.Efor (index, lower, direction, upper, invariants, body) ->
      variantn "Ptree.expr_desc.Efor"
        [ canonical_ident source index;
          canonical_expr source lower;
          canonical_for_direction direction;
          canonical_expr source upper;
          list (canonical_term source) invariants;
          canonical_expr source body ]
  | Ptree.Eassert (kind, term) ->
      variantn "Ptree.expr_desc.Eassert"
        [canonical_assertion_kind kind; canonical_term source term]
  | Ptree.Escope (scope, expression) ->
      variantn "Ptree.expr_desc.Escope"
        [canonical_qualid source scope; canonical_expr source expression]
  | Ptree.Elabel (label, expression) ->
      variantn "Ptree.expr_desc.Elabel"
        [canonical_ident source label; canonical_expr source expression]
  | Ptree.Ecast (expression, ty) ->
      variantn "Ptree.expr_desc.Ecast"
        [canonical_expr source expression; canonical_pty source ty]
  | Ptree.Eghost expression ->
      variant1 "Ptree.expr_desc.Eghost" (canonical_expr source expression)
  | Ptree.Eattr (attribute, expression) ->
      variantn "Ptree.expr_desc.Eattr"
        [canonical_attr source attribute; canonical_expr source expression]

and canonical_fundef source
    (ident, ghost, kind, binders, result, pattern, mask, spec, body) =
  product
    [ canonical_ident source ident;
      boolean ghost;
      canonical_rs_kind kind;
      list (canonical_binder source) binders;
      option (canonical_pty source) result;
      canonical_pattern source pattern;
      canonical_mask mask;
      canonical_spec source spec;
      canonical_expr source body ]

let canonical_field source field =
  node "Ptree.field"
    [ source_span source field.Ptree.f_loc;
      canonical_ident source field.Ptree.f_ident;
      canonical_pty source field.Ptree.f_pty;
      boolean field.Ptree.f_mutable;
      boolean field.Ptree.f_ghost ]

let canonical_type_def source = function
  | Ptree.TDalias ty ->
      variant1 "Ptree.type_def.TDalias" (canonical_pty source ty)
  | Ptree.TDalgebraic constructors ->
      variant1 "Ptree.type_def.TDalgebraic"
        (list
           (fun (location, ident, parameters) ->
             product
               [ source_span source location;
                 canonical_ident source ident;
                 list (canonical_param source) parameters ])
           constructors)
  | Ptree.TDrecord fields ->
      variant1 "Ptree.type_def.TDrecord"
        (list (canonical_field source) fields)
  | Ptree.TDrange (lower, upper) ->
      variantn "Ptree.type_def.TDrange" [bigint lower; bigint upper]
  | Ptree.TDfloat (exponent, significand) ->
      variantn "Ptree.type_def.TDfloat"
        [integer exponent; integer significand]

let canonical_visibility = function
  | Ptree.Public -> variant0 "Ptree.visibility.Public"
  | Ptree.Private -> variant0 "Ptree.visibility.Private"
  | Ptree.Abstract -> variant0 "Ptree.visibility.Abstract"

let canonical_type_decl source declaration =
  node "Ptree.type_decl"
    [ source_span source declaration.Ptree.td_loc;
      canonical_ident source declaration.Ptree.td_ident;
      list (canonical_ident source) declaration.Ptree.td_params;
      canonical_visibility declaration.Ptree.td_vis;
      boolean declaration.Ptree.td_mut;
      list (canonical_term source) declaration.Ptree.td_inv;
      option (canonical_expr source) declaration.Ptree.td_wit;
      canonical_type_def source declaration.Ptree.td_def ]

let canonical_logic_decl source declaration =
  node "Ptree.logic_decl"
    [ source_span source declaration.Ptree.ld_loc;
      canonical_ident source declaration.Ptree.ld_ident;
      list (canonical_param source) declaration.Ptree.ld_params;
      option (canonical_pty source) declaration.Ptree.ld_type;
      option (canonical_term source) declaration.Ptree.ld_def ]

let canonical_ind_decl source declaration =
  node "Ptree.ind_decl"
    [ source_span source declaration.Ptree.in_loc;
      canonical_ident source declaration.Ptree.in_ident;
      list (canonical_param source) declaration.Ptree.in_params;
      list
        (fun (location, ident, term) ->
          product
            [ source_span source location;
              canonical_ident source ident;
              canonical_term source term ])
        declaration.Ptree.in_def ]

let canonical_metarg source = function
  | Ptree.Mty ty ->
      variant1 "Ptree.metarg.Mty" (canonical_pty source ty)
  | Ptree.Mfs qualid ->
      variant1 "Ptree.metarg.Mfs" (canonical_qualid source qualid)
  | Ptree.Mps qualid ->
      variant1 "Ptree.metarg.Mps" (canonical_qualid source qualid)
  | Ptree.Max qualid ->
      variant1 "Ptree.metarg.Max" (canonical_qualid source qualid)
  | Ptree.Mlm qualid ->
      variant1 "Ptree.metarg.Mlm" (canonical_qualid source qualid)
  | Ptree.Mgl qualid ->
      variant1 "Ptree.metarg.Mgl" (canonical_qualid source qualid)
  | Ptree.Mval qualid ->
      variant1 "Ptree.metarg.Mval" (canonical_qualid source qualid)
  | Ptree.Mstr value ->
      variant1 "Ptree.metarg.Mstr" (bytes value)
  | Ptree.Mint value ->
      variant1 "Ptree.metarg.Mint" (integer value)

let canonical_clone_subst source = function
  | Ptree.CStsym (symbol, parameters, ty) ->
      variantn "Ptree.clone_subst.CStsym"
        [ canonical_qualid source symbol;
          list (canonical_ident source) parameters;
          canonical_pty source ty ]
  | Ptree.CSfsym (source_symbol, target) ->
      variantn "Ptree.clone_subst.CSfsym"
        [ canonical_qualid source source_symbol;
          canonical_qualid source target ]
  | Ptree.CSpsym (source_symbol, target) ->
      variantn "Ptree.clone_subst.CSpsym"
        [ canonical_qualid source source_symbol;
          canonical_qualid source target ]
  | Ptree.CSvsym (source_symbol, target) ->
      variantn "Ptree.clone_subst.CSvsym"
        [ canonical_qualid source source_symbol;
          canonical_qualid source target ]
  | Ptree.CSxsym (source_symbol, target) ->
      variantn "Ptree.clone_subst.CSxsym"
        [ canonical_qualid source source_symbol;
          canonical_qualid source target ]
  | Ptree.CSprop kind ->
      variant1 "Ptree.clone_subst.CSprop" (canonical_prop_kind kind)
  | Ptree.CSaxiom qualid ->
      variant1 "Ptree.clone_subst.CSaxiom" (canonical_qualid source qualid)
  | Ptree.CSlemma qualid ->
      variant1 "Ptree.clone_subst.CSlemma" (canonical_qualid source qualid)
  | Ptree.CSgoal qualid ->
      variant1 "Ptree.clone_subst.CSgoal" (canonical_qualid source qualid)

let rec canonical_decl source = function
  | Ptree.Dtype declarations ->
      variant1 "Ptree.decl.Dtype"
        (list (canonical_type_decl source) declarations)
  | Ptree.Dlogic declarations ->
      variant1 "Ptree.decl.Dlogic"
        (list (canonical_logic_decl source) declarations)
  | Ptree.Dind (sign, declarations) ->
      variantn "Ptree.decl.Dind"
        [canonical_ind_sign sign; list (canonical_ind_decl source) declarations]
  | Ptree.Dprop (kind, ident, term) ->
      variantn "Ptree.decl.Dprop"
        [ canonical_prop_kind kind;
          canonical_ident source ident;
          canonical_term source term ]
  | Ptree.Dlet (ident, ghost, kind, expression) ->
      variantn "Ptree.decl.Dlet"
        [ canonical_ident source ident;
          boolean ghost;
          canonical_rs_kind kind;
          canonical_expr source expression ]
  | Ptree.Drec definitions ->
      variant1 "Ptree.decl.Drec"
        (list (canonical_fundef source) definitions)
  | Ptree.Dexn (ident, ty, mask) ->
      variantn "Ptree.decl.Dexn"
        [ canonical_ident source ident;
          canonical_pty source ty;
          canonical_mask mask ]
  | Ptree.Dmeta (ident, arguments) ->
      variantn "Ptree.decl.Dmeta"
        [ canonical_ident source ident;
          list (canonical_metarg source) arguments ]
  | Ptree.Dcloneexport (location, module_, substitutions) ->
      variantn "Ptree.decl.Dcloneexport"
        [ source_span source location;
          canonical_qualid source module_;
          list (canonical_clone_subst source) substitutions ]
  | Ptree.Duseexport module_ ->
      variant1 "Ptree.decl.Duseexport"
        (canonical_qualid source module_)
  | Ptree.Dcloneimport
      (location, import, module_, alias, substitutions) ->
      variantn "Ptree.decl.Dcloneimport"
        [ source_span source location;
          boolean import;
          canonical_qualid source module_;
          option (canonical_ident source) alias;
          list (canonical_clone_subst source) substitutions ]
  | Ptree.Duseimport (location, import, modules) ->
      variantn "Ptree.decl.Duseimport"
        [ source_span source location;
          boolean import;
          list
            (fun (module_, alias) ->
              pair
                (canonical_qualid source module_)
                (option (canonical_ident source) alias))
            modules ]
  | Ptree.Dimport module_ ->
      variant1 "Ptree.decl.Dimport" (canonical_qualid source module_)
  | Ptree.Dscope (location, import, ident, declarations) ->
      variantn "Ptree.decl.Dscope"
        [ source_span source location;
          boolean import;
          canonical_ident source ident;
          list (canonical_decl source) declarations ]

let canonical_mlw_file source = function
  | Ptree.Modules modules ->
      variant1 "Ptree.mlw_file.Modules"
        (list
           (fun (ident, declarations) ->
             pair
               (canonical_ident source ident)
               (list (canonical_decl source) declarations))
           modules)
  | Ptree.Decls declarations ->
      variant1 "Ptree.mlw_file.Decls"
        (list (canonical_decl source) declarations)

let canonical_full_unit_kind source = function
  | Ptree.FullTheory ->
      variant0 "PtreeFull.full_unit_kind.FullTheory"
  | Ptree.FullModule interface ->
      variant1 "PtreeFull.full_unit_kind.FullModule"
        (option (canonical_qualid source) interface)

let canonical_full_unit source unit_ =
  node "PtreeFull.full_unit"
    [ canonical_full_unit_kind source unit_.Ptree.full_kind;
      canonical_ident source unit_.Ptree.full_name;
      list (canonical_decl source) unit_.Ptree.full_decls;
      source_span source unit_.Ptree.full_loc ]

let canonical_full_mlw_file source = function
  | Ptree.FullModules units ->
      variant1 "PtreeFull.full_mlw_file.FullModules"
        (list (canonical_full_unit source) units)
  | Ptree.FullDecls declarations ->
      variant1 "PtreeFull.full_mlw_file.FullDecls"
        (list (canonical_decl source) declarations)

let source_sha256 source = sha256_string source.bytes

let surface_file_record source parsed =
  let canonical = canonical_full_mlw_file source parsed in
  let canonical_text = canonical_bytes canonical in
  `Assoc
    [ ("schema", `Int 3);
      ( "semantic_profile_sha256",
        `String Canonical_v3_profile.semantic_profile_sha256 );
      ( "diagnostic_contract_sha256",
        `String Canonical_v3_profile.diagnostic_contract_sha256 );
      ("fixture", `String source.label);
      ("source_sha256", `String (source_sha256 source));
      ("scope", `String "file");
      ("stage", `String "parsed-surface");
      ("canonical_sha256", `String (sha256_string canonical_text));
      ("canonical", canonical) ]

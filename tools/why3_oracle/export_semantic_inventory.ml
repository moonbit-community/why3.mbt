(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit inventory adapter, translated/modified 2026-07-21.      *)
(*                                                                  *)
(********************************************************************)

open Why3

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let observed_variants = ref StringSet.empty

let observe category variant =
  observed_variants :=
    StringSet.add (category ^ "\t" ^ variant) !observed_variants

let fail message =
  prerr_endline ("export_semantic_inventory: " ^ message);
  exit 1

let split_qualified name =
  match List.rev (String.split_on_char '.' name) with
  | [] -> assert false
  | theory :: rev_path -> (List.rev rev_path, theory)

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

let module_key pmodule = theory_key pmodule.Pmodule.mod_theory

let rec observe_ty ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar _ -> observe "type-node" "Tyvar"
  | Ty.Tyapp (symbol, arguments) ->
      observe "type-node" "Tyapp";
      observe_tysymbol symbol;
      List.iter observe_ty arguments

and observe_tysymbol symbol =
  observe "type-symbol-definition"
    (match symbol.Ty.ts_def with
     | Ty.NoDef -> "NoDef"
     | Ty.Alias _ -> "Alias"
     | Ty.Range _ -> "Range"
     | Ty.Float _ -> "Float");
  match symbol.Ty.ts_def with
  | Ty.Alias ty -> observe_ty ty
  | Ty.NoDef | Ty.Range _ | Ty.Float _ -> ()

let observe_constant constant =
  let variant =
    match constant with
    | Constant.ConstInt value ->
        "Int:" ^
        (match value.Number.il_kind with
         | Number.ILitUnk -> "Unknown"
         | Number.ILitDec -> "Decimal"
         | Number.ILitHex -> "Hexadecimal"
         | Number.ILitOct -> "Octal"
         | Number.ILitBin -> "Binary")
    | Constant.ConstReal value ->
        "Real:" ^
        (match value.Number.rl_kind with
         | Number.RLitUnk -> "Unknown"
         | Number.RLitDec _ -> "Decimal"
         | Number.RLitHex _ -> "Hexadecimal")
    | Constant.ConstStr _ -> "String"
  in
  observe "constant" variant

let observe_lsymbol symbol =
  List.iter observe_ty symbol.Term.ls_args;
  Option.iter observe_ty symbol.Term.ls_value

let rec observe_pattern pattern =
  observe_ty pattern.Term.pat_ty;
  match pattern.Term.pat_node with
  | Term.Pwild -> observe "pattern-node" "Pwild"
  | Term.Pvar variable ->
      observe "pattern-node" "Pvar";
      observe_ty variable.Term.vs_ty
  | Term.Papp (symbol, arguments) ->
      observe "pattern-node" "Papp";
      observe_lsymbol symbol;
      List.iter observe_pattern arguments
  | Term.Por (left, right) ->
      observe "pattern-node" "Por";
      observe_pattern left;
      observe_pattern right
  | Term.Pas (nested, variable) ->
      observe "pattern-node" "Pas";
      observe_pattern nested;
      observe_ty variable.Term.vs_ty

let rec observe_term term =
  Option.iter observe_ty term.Term.t_ty;
  match term.Term.t_node with
  | Term.Tvar variable ->
      observe "term-node" "Tvar";
      observe_ty variable.Term.vs_ty
  | Term.Tconst constant ->
      observe "term-node" "Tconst";
      observe_constant constant
  | Term.Tapp (symbol, arguments) ->
      observe "term-node" "Tapp";
      observe_lsymbol symbol;
      List.iter observe_term arguments
  | Term.Tif (condition, then_, else_) ->
      observe "term-node" "Tif";
      List.iter observe_term [condition; then_; else_]
  | Term.Tlet (value, bound) ->
      observe "term-node" "Tlet";
      observe_term value;
      let variable, body = Term.t_open_bound bound in
      observe_ty variable.Term.vs_ty;
      observe_term body
  | Term.Tcase (scrutinee, branches) ->
      observe "term-node" "Tcase";
      observe_term scrutinee;
      List.iter
        (fun branch ->
          let pattern, body = Term.t_open_branch branch in
          observe_pattern pattern;
          observe_term body)
        branches
  | Term.Teps bound ->
      observe "term-node" "Teps";
      let variable, body = Term.t_open_bound bound in
      observe_ty variable.Term.vs_ty;
      observe_term body
  | Term.Tquant (quantifier, quantified) ->
      observe "term-node"
        (match quantifier with
         | Term.Tforall -> "Tquant:Forall"
         | Term.Texists -> "Tquant:Exists");
      let variables, triggers, body = Term.t_open_quant quantified in
      List.iter (fun variable -> observe_ty variable.Term.vs_ty) variables;
      List.iter (List.iter observe_term) triggers;
      observe_term body
  | Term.Tbinop (operator, left, right) ->
      observe "term-node"
        (match operator with
         | Term.Tand -> "Tbinop:And"
         | Term.Tor -> "Tbinop:Or"
         | Term.Timplies -> "Tbinop:Implies"
         | Term.Tiff -> "Tbinop:Iff");
      observe_term left;
      observe_term right
  | Term.Tnot nested ->
      observe "term-node" "Tnot";
      observe_term nested
  | Term.Ttrue -> observe "term-node" "Ttrue"
  | Term.Tfalse -> observe "term-node" "Tfalse"

let observe_decl decl =
  match decl.Decl.d_node with
  | Decl.Dtype symbol -> observe_tysymbol symbol
  | Decl.Ddata declarations ->
      List.iter
        (fun (symbol, constructors) ->
          observe_tysymbol symbol;
          List.iter
            (fun (constructor, projections) ->
              observe_lsymbol constructor;
              List.iter (Option.iter observe_lsymbol) projections)
            constructors)
        declarations
  | Decl.Dparam symbol -> observe_lsymbol symbol
  | Decl.Dlogic declarations ->
      List.iter
        (fun (symbol, definition) ->
          observe_lsymbol symbol;
          let variables, body = Decl.open_ls_defn definition in
          List.iter (fun variable -> observe_ty variable.Term.vs_ty) variables;
          observe_term body)
        declarations
  | Decl.Dind (_, declarations) ->
      List.iter
        (fun (symbol, cases) ->
          observe_lsymbol symbol;
          List.iter (fun (_, body) -> observe_term body) cases)
        declarations
  | Decl.Dprop (_, _, body) -> observe_term body

let rec observe_ity ity =
  match ity.Ity.ity_node with
  | Ity.Ityvar _ -> observe "program-type-node" "Ityvar"
  | Ity.Ityreg region ->
      observe "program-type-node" "Ityreg";
      List.iter observe_ity region.Ity.reg_args;
      List.iter observe_ity region.Ity.reg_regs
  | Ity.Ityapp (symbol, arguments, regions) ->
      observe "program-type-node" "Ityapp";
      observe_tysymbol symbol.Ity.its_ts;
      List.iter observe_ity arguments;
      List.iter observe_ity regions

let rec observe_mask = function
  | Ity.MaskVisible -> observe "program-mask" "Visible"
  | Ity.MaskGhost -> observe "program-mask" "Ghost"
  | Ity.MaskTuple masks ->
      observe "program-mask" "Tuple";
      List.iter observe_mask masks

let observe_effect effect =
  observe "program-effect" (if Ity.eff_pure effect then "Pure" else "Impure");
  observe "program-termination"
    (match effect.Ity.eff_oneway with
     | Ity.Total -> "Total"
     | Ity.Partial -> "Partial"
     | Ity.Diverges -> "Diverges")

let observe_cty cty =
  List.iter (fun variable -> observe_ity variable.Ity.pv_ity) cty.Ity.cty_args;
  List.iter observe_term cty.Ity.cty_pre;
  List.iter
    (fun post ->
      let variable, body = Ity.open_post post in
      observe_ty variable.Term.vs_ty;
      observe_term body)
    cty.Ity.cty_post;
  Ity.Mxs.iter
    (fun exception_ posts ->
      observe_ity exception_.Ity.xs_ity;
      observe_mask exception_.Ity.xs_mask;
      List.iter
        (fun post ->
          let variable, body = Ity.open_post post in
          observe_ty variable.Term.vs_ty;
          observe_term body)
        posts)
    cty.Ity.cty_xpost;
  observe_effect cty.Ity.cty_effect;
  observe_ity cty.Ity.cty_result;
  observe_mask cty.Ity.cty_mask

let observe_rsymbol symbol =
  observe "routine-logic"
    (match symbol.Expr.rs_logic with
     | Expr.RLnone -> "RLnone"
     | Expr.RLpv _ -> "RLpv"
     | Expr.RLls logic ->
         observe_lsymbol logic;
         "RLls"
     | Expr.RLlemma -> "RLlemma");
  observe_cty symbol.Expr.rs_cty

let observe_cexp computation =
  observe "program-computation"
    (match computation.Expr.c_node with
     | Expr.Capp (symbol, _) ->
         observe_rsymbol symbol;
         "Capp"
     | Expr.Cpur (symbol, _) ->
         observe_lsymbol symbol;
         "Cpur"
     | Expr.Cfun _ -> "Cfun"
     | Expr.Cany -> "Cany");
  observe_cty computation.Expr.c_cty

let decl_kind decl =
  match decl.Decl.d_node with
  | Decl.Dtype symbol ->
      let definition =
        match symbol.Ty.ts_def with
        | Ty.NoDef -> "NoDef"
        | Ty.Alias _ -> "Alias"
        | Ty.Range _ -> "Range"
        | Ty.Float _ -> "Float"
      in
      "Dtype:" ^ definition
  | Decl.Ddata _ -> "Ddata"
  | Decl.Dparam _ -> "Dparam"
  | Decl.Dlogic _ -> "Dlogic"
  | Decl.Dind (Decl.Ind, _) -> "Dind:Ind"
  | Decl.Dind (Decl.Coind, _) -> "Dind:Coind"
  | Decl.Dprop (Decl.Plemma, _, _) -> "Dprop:Plemma"
  | Decl.Dprop (Decl.Paxiom, _, _) -> "Dprop:Paxiom"
  | Decl.Dprop (Decl.Pgoal, _, _) -> "Dprop:Pgoal"

let pdecl_kind pdecl =
  match pdecl.Pdecl.pd_node with
  | Pdecl.PDtype _ -> "PDtype"
  | Pdecl.PDlet (Expr.LDvar _) -> "PDlet:LDvar"
  | Pdecl.PDlet (Expr.LDsym _) -> "PDlet:LDsym"
  | Pdecl.PDlet (Expr.LDrec _) -> "PDlet:LDrec"
  | Pdecl.PDexn _ -> "PDexn"
  | Pdecl.PDpure -> "PDpure"

let observe_pdecl pdecl =
  observe "program-declaration" (pdecl_kind pdecl);
  List.iter observe_decl pdecl.Pdecl.pd_pure;
  match pdecl.Pdecl.pd_node with
  | Pdecl.PDtype definitions ->
      List.iter
        (fun definition ->
          observe_tysymbol definition.Pdecl.itd_its.Ity.its_ts;
          List.iter observe_rsymbol definition.Pdecl.itd_fields;
          List.iter observe_rsymbol definition.Pdecl.itd_constructors;
          List.iter observe_term definition.Pdecl.itd_invariant;
          if Option.is_some definition.Pdecl.itd_witness then
            observe "program-type-witness" "Present"
          else
            observe "program-type-witness" "Absent")
        definitions
  | Pdecl.PDlet (Expr.LDvar (variable, _)) ->
      observe_ity variable.Ity.pv_ity
  | Pdecl.PDlet (Expr.LDsym (symbol, computation)) ->
      observe_rsymbol symbol;
      observe_cexp computation
  | Pdecl.PDlet (Expr.LDrec definitions) ->
      List.iter
        (fun definition ->
          observe_rsymbol definition.Expr.rec_sym;
          observe_rsymbol definition.Expr.rec_rsym;
          observe_cexp definition.Expr.rec_fun)
        definitions
  | Pdecl.PDexn exception_ ->
      observe_ity exception_.Ity.xs_ity;
      observe_mask exception_.Ity.xs_mask
  | Pdecl.PDpure -> ()

let add_record records fields =
  records := String.concat "\t" fields :: !records

let collect_theories roots =
  let seen = ref StringMap.empty in
  let records = ref [] in
  let rec visit theory =
    let key = theory_key theory in
    if not (StringMap.mem key !seen) then begin
      seen := StringMap.add key theory !seen;
      add_record records ["theory"; key];
      List.iteri
        (fun ordinal declaration ->
          match declaration.Theory.td_node with
          | Theory.Decl decl ->
              observe_decl decl;
              add_record records
                ["theory-item"; key; string_of_int ordinal; decl_kind decl]
          | Theory.Use used ->
              let target = theory_key used in
              add_record records
                ["theory-item"; key; string_of_int ordinal; "Use"; target];
              visit used
          | Theory.Clone (source, _) ->
              let target = theory_key source in
              add_record records
                ["theory-item"; key; string_of_int ordinal; "Clone"; target];
              visit source
          | Theory.Meta (meta, args) ->
              add_record records
                [ "theory-item";
                  key;
                  string_of_int ordinal;
                  "Meta";
                  meta.Theory.meta_name;
                  string_of_int (List.length args) ])
        theory.Theory.th_decls
    end
  in
  List.iter visit roots;
  (!seen, !records)

let collect_modules roots =
  let seen = ref StringMap.empty in
  let records = ref [] in
  let rec visit pmodule =
    let key = module_key pmodule in
    if not (StringMap.mem key !seen) then begin
      seen := StringMap.add key pmodule !seen;
      add_record records ["module"; key; theory_key pmodule.Pmodule.mod_theory];
      List.iteri (visit_unit key []) pmodule.Pmodule.mod_units
    end
  and visit_unit owner path ordinal unit_ =
    let path = path @ [ordinal] in
    let ordinal_path =
      String.concat "." (List.map string_of_int path)
    in
    match unit_ with
    | Pmodule.Udecl pdecl ->
        observe_pdecl pdecl;
        add_record records
          ["module-item"; owner; ordinal_path; pdecl_kind pdecl]
    | Pmodule.Uuse used ->
        let target = module_key used in
        add_record records ["module-item"; owner; ordinal_path; "Uuse"; target];
        visit used
    | Pmodule.Uclone instance ->
        let target = module_key instance.Pmodule.mi_mod in
        add_record records
          ["module-item"; owner; ordinal_path; "Uclone"; target];
        visit instance.Pmodule.mi_mod
    | Pmodule.Umeta (meta, args) ->
        add_record records
          [ "module-item";
            owner;
            ordinal_path;
            "Umeta";
            meta.Theory.meta_name;
            string_of_int (List.length args) ]
    | Pmodule.Uscope (name, units) ->
        add_record records
          [ "module-item";
            owner;
            ordinal_path;
            "Uscope";
            name;
            string_of_int (List.length units) ];
        List.iteri (visit_unit owner path) units
  in
  List.iter visit roots;
  (!seen, !records)

let read_theory environment name =
  let path, theory = split_qualified name in
  Env.read_theory environment path theory

let read_module environment name =
  let path, pmodule = split_qualified name in
  Pmodule.read_module environment path pmodule

let () =
  let stdlib = ref None in
  let theory_roots = ref [] in
  let module_roots = ref [] in
  let specification =
    [ ( "--stdlib",
        Arg.String (fun path -> stdlib := Some path),
        "PATH pinned Why3 stdlib directory" );
      ( "--theory",
        Arg.String (fun name -> theory_roots := name :: !theory_roots),
        "NAME root pure theory (repeatable)" );
      ( "--module",
        Arg.String (fun name -> module_roots := name :: !module_roots),
        "NAME root program module (repeatable)" ) ]
  in
  Arg.parse specification (fun value -> fail ("unexpected argument: " ^ value))
    "export_semantic_inventory --stdlib PATH --theory NAME --module NAME";
  let stdlib =
    match !stdlib with
    | Some path -> path
    | None -> fail "--stdlib is required"
  in
  let environment = Env.create_env [stdlib] in
  let theory_roots =
    List.rev_map (read_theory environment) !theory_roots
  in
  let module_roots =
    List.rev_map (read_module environment) !module_roots
  in
  let _, theory_records = collect_theories theory_roots in
  let modules, module_records = collect_modules module_roots in
  let projected_theories =
    StringMap.bindings modules
    |> List.map (fun (_, pmodule) -> pmodule.Pmodule.mod_theory)
  in
  let _, projected_records = collect_theories projected_theories in
  let variant_records =
    StringSet.elements !observed_variants
    |> List.map (fun value -> "variant\t" ^ value)
  in
  List.sort_uniq String.compare
    (theory_records @ module_records @ projected_records @ variant_records)
  |> List.iter print_endline

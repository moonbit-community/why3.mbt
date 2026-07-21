(* SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception *)
(* Original adapter over the pinned Why3 1.7.2 semantic APIs. *)

open Why3
open Yojson.Safe

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let fail message =
  prerr_endline ("export_snapshot: " ^ message);
  exit 1

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

let tag name fields = `List (`String name :: fields)
let option_json encode = function None -> `Null | Some value -> encode value
let bigint value = `String (BigInt.to_string value)

let observed = ref StringMap.empty

let observe category variant =
  let variants =
    Option.value ~default:StringSet.empty
      (StringMap.find_opt category !observed)
  in
  observed :=
    StringMap.add category (StringSet.add variant variants) !observed

let split_qualified name =
  match List.rev (String.split_on_char '.' name) with
  | [] -> assert false
  | leaf :: reversed_path -> (List.rev reversed_path, leaf)

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

let module_key pmodule = theory_key pmodule.Pmodule.mod_theory

let stdlib_root = ref ""
let source_cache : (string, string * int array) Hashtbl.t = Hashtbl.create 37

let strip_prefix prefix value =
  let prefix_length = String.length prefix in
  if String.length value >= prefix_length
     && String.sub value 0 prefix_length = prefix
  then Some (String.sub value prefix_length (String.length value - prefix_length))
  else None

let load_source path =
  match Hashtbl.find_opt source_cache path with
  | Some cached -> cached
  | None ->
      let channel = open_in_bin path in
      let length = in_channel_length channel in
      let source = really_input_string channel length in
      close_in channel;
      let starts = ref [0] in
      String.iteri
        (fun index character ->
          if character = '\n' then starts := (index + 1) :: !starts)
        source;
      let starts = Array.of_list (List.rev !starts) in
      let cached = (source, starts) in
      Hashtbl.add source_cache path cached;
      cached

let source_path file =
  let root = Unix.realpath !stdlib_root in
  let absolute =
    if Filename.is_relative file then Filename.concat root file else file
  in
  let absolute =
    if Sys.file_exists absolute then Unix.realpath absolute
    else fail ("source location does not exist: " ^ file)
  in
  let prefix = root ^ Filename.dir_sep in
  match strip_prefix prefix absolute with
  | Some relative -> (relative, absolute)
  | None -> fail ("source location escapes the pinned stdlib: " ^ absolute)

let source_offset path line column =
  let source, starts = load_source path in
  if line < 1 || line > Array.length starts then
    fail (Printf.sprintf "invalid source line %d in %s" line path);
  let offset = starts.(line - 1) + column in
  if offset < 0 || offset > String.length source then
    fail (Printf.sprintf "invalid source column %d:%d in %s" line column path);
  offset

let location_json = function
  | None -> `Null
  | Some position ->
      let file, start_line, start_column, end_line, end_column =
        Loc.get position
      in
      let relative, absolute = source_path file in
      `Assoc
        [ ("relativePathHex", `String (hex_string relative));
          ("startByte", `Int (source_offset absolute start_line start_column));
          ("endByte", `Int (source_offset absolute end_line end_column));
          ("startLine", `Int start_line);
          ("startColumn", `Int start_column);
          ("endLine", `Int end_line);
          ("endColumn", `Int end_column) ]

let attributes_json attributes =
  attributes
  |> Ident.Sattr.elements
  |> List.map (fun attribute -> hex_string attribute.Ident.attr_string)
  |> List.sort String.compare
  |> List.map (fun value -> `String value)
  |> fun values -> `List values

let ident_json ident =
  `Assoc
    [ ("nameHex", `String (hex_string ident.Ident.id_string));
      ("attributes", attributes_json ident.Ident.id_attrs);
      ("sourceSpan", location_json ident.Ident.id_loc) ]

type locator = {
  owner : string;
  item : int;
  inner : int;
  kind : string;
  shape : string;
}

let locator_string locator =
  Printf.sprintf "%s#%d#%d#%s" locator.owner locator.item locator.inner
    locator.kind

let locator_json locator =
  `Assoc
    [ ("id", `String (locator_string locator));
      ("theoryKey", `String locator.owner);
      ("itemOrdinal", `Int locator.item);
      ("innerOrdinal", `Int locator.inner);
      ("kind", `String locator.kind);
      ("shape", `String locator.shape) ]

type catalog_entry =
  | Type_entry of locator * Ty.tysymbol
  | Logic_entry of locator * Term.lsymbol
  | Proposition_entry of locator * Decl.prsymbol
  | Program_type_entry of locator * Ity.itysymbol
  | Routine_entry of locator * Expr.rsymbol

let type_locations = ref Ty.Mts.empty
let logic_locations = ref Term.Mls.empty
let proposition_locations = ref Decl.Mpr.empty
let program_type_locations = ref Ity.Mits.empty
let routine_locations = ref Expr.Mrs.empty
let catalog_entries = ref []

let add_type locator symbol =
  if not (Ty.Mts.mem symbol !type_locations) then begin
    type_locations := Ty.Mts.add symbol locator !type_locations;
    catalog_entries := Type_entry (locator, symbol) :: !catalog_entries
  end

let add_logic locator symbol =
  if not (Term.Mls.mem symbol !logic_locations) then begin
    logic_locations := Term.Mls.add symbol locator !logic_locations;
    catalog_entries := Logic_entry (locator, symbol) :: !catalog_entries
  end

let add_proposition locator symbol =
  if not (Decl.Mpr.mem symbol !proposition_locations) then begin
    proposition_locations := Decl.Mpr.add symbol locator !proposition_locations;
    catalog_entries := Proposition_entry (locator, symbol) :: !catalog_entries
  end

let add_program_type locator symbol =
  if not (Ity.Mits.mem symbol !program_type_locations) then begin
    program_type_locations :=
      Ity.Mits.add symbol locator !program_type_locations;
    catalog_entries := Program_type_entry (locator, symbol) :: !catalog_entries
  end

let add_routine locator symbol =
  if not (Expr.Mrs.mem symbol !routine_locations) then begin
    routine_locations := Expr.Mrs.add symbol locator !routine_locations;
    catalog_entries := Routine_entry (locator, symbol) :: !catalog_entries
  end

let find_location kind name find symbol =
  match find symbol with
  | Some locator -> locator
  | None -> fail (Printf.sprintf "unindexed %s symbol %s" kind name)

let type_ref symbol =
  let locator =
    find_location "type" symbol.Ty.ts_name.Ident.id_string
      (fun value -> Ty.Mts.find_opt value !type_locations) symbol
  in
  `String (locator_string locator)

let logic_ref symbol =
  let locator =
    find_location "logic" symbol.Term.ls_name.Ident.id_string
      (fun value -> Term.Mls.find_opt value !logic_locations) symbol
  in
  `String (locator_string locator)

let proposition_ref symbol =
  let locator =
    find_location "proposition" symbol.Decl.pr_name.Ident.id_string
      (fun value -> Decl.Mpr.find_opt value !proposition_locations) symbol
  in
  `String (locator_string locator)

let program_type_ref symbol =
  let locator =
    find_location "program type" symbol.Ity.its_ts.Ty.ts_name.Ident.id_string
      (fun value -> Ity.Mits.find_opt value !program_type_locations) symbol
  in
  `String (locator_string locator)

let routine_ref symbol =
  let locator =
    find_location "routine" symbol.Expr.rs_name.Ident.id_string
      (fun value -> Expr.Mrs.find_opt value !routine_locations) symbol
  in
  `String (locator_string locator)

let next_type_variable = ref 0
let type_variable_ids = ref Ty.Mtv.empty
let type_variables = ref []

let type_variable_id variable =
  match Ty.Mtv.find_opt variable !type_variable_ids with
  | Some id -> id
  | None ->
      let id = !next_type_variable in
      incr next_type_variable;
      type_variable_ids := Ty.Mtv.add variable id !type_variable_ids;
      type_variables := (id, variable) :: !type_variables;
      id

let rec type_json ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar variable ->
      observe "typeNode" "Tyvar";
      tag "TyVar" [`Int (type_variable_id variable)]
  | Ty.Tyapp (symbol, arguments) ->
      observe "typeNode" "Tyapp";
      tag "TyApp" [type_ref symbol; `List (List.map type_json arguments)]

let type_definition_json definition =
  match definition with
  | Ty.NoDef ->
      observe "typeSymbolDefinition" "NoDef";
      tag "NoDef" []
  | Ty.Alias ty ->
      observe "typeSymbolDefinition" "Alias";
      tag "Alias" [type_json ty]
  | Ty.Range range ->
      observe "typeSymbolDefinition" "Range";
      tag "Range" [bigint range.Number.ir_lower; bigint range.Number.ir_upper]
  | Ty.Float format ->
      observe "typeSymbolDefinition" "Float";
      tag "Float"
        [ `Int format.Number.fp_exponent_digits;
          `Int format.Number.fp_significand_digits ]

let ordered_type_variables_of_types types result =
  let seen = ref Ty.Stv.empty in
  let ordered = ref [] in
  let rec visit ty =
    match ty.Ty.ty_node with
    | Ty.Tyvar variable ->
        if not (Ty.Stv.mem variable !seen) then begin
          seen := Ty.Stv.add variable !seen;
          ordered := variable :: !ordered
        end
    | Ty.Tyapp (_, arguments) -> List.iter visit arguments
  in
  List.iter visit types;
  Option.iter visit result;
  List.rev !ordered

let builtin_type_kind symbol =
  if Ty.ts_equal symbol Ty.ts_int then Some "integer"
  else if Ty.ts_equal symbol Ty.ts_real then Some "real"
  else if Ty.ts_equal symbol Ty.ts_bool then Some "boolean"
  else if Ty.ts_equal symbol Ty.ts_str then Some "string"
  else None

let type_symbol_json symbol =
  `Assoc
    [ ("tag", `String "TypeSymbol");
      ("name", ident_json symbol.Ty.ts_name);
      ( "typeParameters",
        `List
          (List.map
             (fun variable -> `Int (type_variable_id variable))
             symbol.Ty.ts_args) );
      ("definition", type_definition_json symbol.Ty.ts_def);
      ("builtinKind", option_json (fun value -> `String value)
          (builtin_type_kind symbol)) ]

let logic_symbol_json symbol =
  let type_parameters =
    ordered_type_variables_of_types symbol.Term.ls_args symbol.Term.ls_value
  in
  let role =
    if symbol.Term.ls_proj then tag "Projection" []
    else if symbol.Term.ls_constr > 0 then
      tag "Constructor" [`Int symbol.Term.ls_constr]
    else tag "Ordinary" []
  in
  `Assoc
    [ ("tag", `String "LogicSymbol");
      ("name", ident_json symbol.Term.ls_name);
      ( "typeParameters",
        `List
          (List.map
             (fun variable -> `Int (type_variable_id variable))
             type_parameters) );
      ("argumentTypes", `List (List.map type_json symbol.Term.ls_args));
      ("resultType", option_json type_json symbol.Term.ls_value);
      ("role", role) ]

let proposition_symbol_json symbol =
  `Assoc
    [ ("tag", `String "PropositionSymbol");
      ("name", ident_json symbol.Decl.pr_name) ]

let make_locator owner item inner kind shape =
  { owner; item; inner; kind; shape }

let preindex_decl owner item declaration =
  let inner = ref 0 in
  let fresh kind shape =
    let locator = make_locator owner item !inner kind shape in
    incr inner;
    locator
  in
  match declaration.Decl.d_node with
  | Decl.Dtype symbol -> add_type (fresh "type" "typeSymbol") symbol
  | Decl.Ddata declarations ->
      List.iter
        (fun (symbol, constructors) ->
          add_type (fresh "type" "typeSymbol") symbol;
          List.iter
            (fun (constructor, projections) ->
              add_logic (fresh "logic" "logicSymbol") constructor;
              List.iter
                (Option.iter (fun projection ->
                     add_logic (fresh "logic" "logicSymbol") projection))
                projections)
            constructors)
        declarations
  | Decl.Dparam symbol -> add_logic (fresh "logic" "logicSymbol") symbol
  | Decl.Dlogic definitions ->
      List.iter
        (fun (symbol, _) -> add_logic (fresh "logic" "logicSymbol") symbol)
        definitions
  | Decl.Dind (_, declarations) ->
      List.iter
        (fun (predicate, cases) ->
          add_logic (fresh "logic" "logicSymbol") predicate;
          List.iter
            (fun (proposition, _) ->
              add_proposition (fresh "proposition" "propositionSymbol")
                proposition)
            cases)
        declarations
  | Decl.Dprop (_, proposition, _) ->
      add_proposition (fresh "proposition" "propositionSymbol") proposition

let preindex_theory theory =
  let owner = theory_key theory in
  List.iteri
    (fun item declaration ->
      match declaration.Theory.td_node with
      | Theory.Decl decl -> preindex_decl owner item decl
      | Theory.Use _ | Theory.Clone _ | Theory.Meta _ -> ())
    theory.Theory.th_decls

let preindex_pdecl owner item pdecl =
  let inner = ref 0 in
  let fresh shape =
    let locator = make_locator owner item !inner "program" shape in
    incr inner;
    locator
  in
  match pdecl.Pdecl.pd_node with
  | Pdecl.PDtype definitions ->
      List.iter
        (fun definition ->
          add_program_type (fresh "programTypeSymbol")
            definition.Pdecl.itd_its;
          List.iter (fun symbol -> add_routine (fresh "routineSymbol") symbol)
            definition.Pdecl.itd_fields;
          List.iter (fun symbol -> add_routine (fresh "routineSymbol") symbol)
            definition.Pdecl.itd_constructors)
        definitions
  | Pdecl.PDlet (Expr.LDsym (symbol, _)) ->
      add_routine (fresh "routineSymbol") symbol
  | Pdecl.PDpure -> ()
  | Pdecl.PDlet (Expr.LDvar _) ->
      fail "trusted snapshot contains PDlet:LDvar"
  | Pdecl.PDlet (Expr.LDrec _) ->
      fail "trusted snapshot contains PDlet:LDrec"
  | Pdecl.PDexn _ -> fail "trusted snapshot contains PDexn"

let preindex_module pmodule =
  let owner = module_key pmodule in
  let ordinal = ref 0 in
  let rec visit units =
    List.iter
      (fun unit_ ->
        let item = !ordinal in
        incr ordinal;
        match unit_ with
        | Pmodule.Udecl pdecl -> preindex_pdecl owner item pdecl
        | Pmodule.Uscope (_, nested) -> visit nested
        | Pmodule.Uuse _ | Pmodule.Uclone _ | Pmodule.Umeta _ -> ())
      units
  in
  visit pmodule.Pmodule.mod_units

let collect_theories roots =
  let theories = ref StringMap.empty in
  let rec visit theory =
    let key = theory_key theory in
    if not (StringMap.mem key !theories) then begin
      theories := StringMap.add key theory !theories;
      List.iter
        (fun declaration ->
          match declaration.Theory.td_node with
          | Theory.Use used | Theory.Clone (used, _) -> visit used
          | Theory.Decl _ | Theory.Meta _ -> ())
        theory.Theory.th_decls
    end
  in
  List.iter visit roots;
  (!theories, visit)

let collect_modules roots =
  let modules = ref StringMap.empty in
  let rec visit pmodule =
    let key = module_key pmodule in
    if not (StringMap.mem key !modules) then begin
      modules := StringMap.add key pmodule !modules;
      let rec visit_units units =
        List.iter
          (function
            | Pmodule.Uuse used -> visit used
            | Pmodule.Uclone instance -> visit instance.Pmodule.mi_mod
            | Pmodule.Uscope (_, nested) -> visit_units nested
            | Pmodule.Udecl _ | Pmodule.Umeta _ -> ())
          units
      in
      visit_units pmodule.Pmodule.mod_units
    end
  in
  List.iter visit roots;
  !modules

let integer_kind_json = function
  | Number.ILitUnk ->
      observe "constant" "Int:Unknown";
      `String "ILitUnk"
  | Number.ILitDec ->
      observe "constant" "Int:Decimal";
      `String "ILitDec"
  | Number.ILitHex ->
      observe "constant" "Int:Hexadecimal";
      `String "ILitHex"
  | Number.ILitOct -> fail "trusted snapshot contains an octal integer"
  | Number.ILitBin -> fail "trusted snapshot contains a binary integer"

let real_kind_json = function
  | Number.RLitUnk -> fail "trusted snapshot contains an unknown real literal"
  | Number.RLitDec exponent ->
      observe "constant" "Real:Decimal";
      tag "RLitDec" [`Int exponent]
  | Number.RLitHex exponent ->
      observe "constant" "Real:Hexadecimal";
      tag "RLitHex" [`Int exponent]

let constant_json = function
  | Constant.ConstInt value ->
      tag "ConstantInt"
        [integer_kind_json value.Number.il_kind; bigint value.Number.il_int]
  | Constant.ConstReal value ->
      let real = value.Number.rl_real in
      tag "ConstantReal"
        [ real_kind_json value.Number.rl_kind;
          bigint real.Number.rv_sig;
          bigint real.Number.rv_pow2;
          bigint real.Number.rv_pow5 ]
  | Constant.ConstStr value ->
      observe "constant" "String";
      tag "ConstantString" [`String (hex_string value)]

type term_environment = {
  local_variables : int Term.Mvs.t;
  program_variables : int Term.Mvs.t;
  next_local : int ref;
}

let empty_term_environment () =
  { local_variables = Term.Mvs.empty;
    program_variables = Term.Mvs.empty;
    next_local = ref 0 }

let variable_json id variable =
  `Assoc
    [ ("id", `Int id);
      ("name", ident_json variable.Term.vs_name);
      ("type", type_json variable.Term.vs_ty) ]

let bind_variable environment variable =
  let id = !(environment.next_local) in
  incr environment.next_local;
  ( { environment with
      local_variables =
        Term.Mvs.add variable id environment.local_variables },
    variable_json id variable )

let bind_variables environment variables =
  List.fold_left
    (fun (environment, encoded) variable ->
      let environment, descriptor = bind_variable environment variable in
      (environment, descriptor :: encoded))
    (environment, []) variables
  |> fun (environment, reversed) -> (environment, List.rev reversed)

let variable_reference environment variable =
  match Term.Mvs.find_opt variable environment.local_variables with
  | Some id -> tag "LocalVariable" [`Int id]
  | None ->
      begin match Term.Mvs.find_opt variable environment.program_variables with
      | Some id -> tag "ProgramVariable" [`Int id]
      | None ->
          fail
            ("unbound term variable " ^ variable.Term.vs_name.Ident.id_string)
      end

let rec pattern_json environment pattern =
  let node =
    match pattern.Term.pat_node with
    | Term.Pwild ->
        observe "patternNode" "Pwild";
        tag "Pwild" [type_json pattern.Term.pat_ty]
    | Term.Papp (symbol, arguments) ->
        observe "patternNode" "Papp";
        tag "Papp"
          [ logic_ref symbol;
            `List (List.map (pattern_json environment) arguments);
            type_json pattern.Term.pat_ty ]
    | Term.Por (left, right) ->
        observe "patternNode" "Por";
        tag "Por"
          [ pattern_json environment left;
            pattern_json environment right;
            type_json pattern.Term.pat_ty ]
    | Term.Pvar _ -> fail "trusted snapshot contains Pvar"
    | Term.Pas _ -> fail "trusted snapshot contains Pas"
  in
  node

let rec term_json environment term =
  let node =
    match term.Term.t_node with
    | Term.Tvar variable ->
        observe "termNode" "Tvar";
        tag "Tvar" [variable_reference environment variable]
    | Term.Tconst constant ->
        observe "termNode" "Tconst";
        tag "Tconst"
          [ constant_json constant;
            option_json type_json term.Term.t_ty ]
    | Term.Tapp (symbol, arguments) ->
        observe "termNode" "Tapp";
        tag "Tapp"
          [ logic_ref symbol;
            `List (List.map (term_json environment) arguments);
            option_json type_json term.Term.t_ty ]
    | Term.Tif (condition, then_branch, else_branch) ->
        observe "termNode" "Tif";
        tag "Tif"
          [ term_json environment condition;
            term_json environment then_branch;
            term_json environment else_branch;
            option_json type_json term.Term.t_ty ]
    | Term.Tlet (value, bound) ->
        observe "termNode" "Tlet";
        let variable, body = Term.t_open_bound bound in
        let body_environment, binder = bind_variable environment variable in
        tag "Tlet"
          [ term_json environment value;
            binder;
            term_json body_environment body;
            option_json type_json term.Term.t_ty ]
    | Term.Tcase (scrutinee, branches) ->
        observe "termNode" "Tcase";
        let branches =
          List.map
            (fun branch ->
              let pattern, body = Term.t_open_branch branch in
              if not (Term.Svs.is_empty pattern.Term.pat_vars) then
                fail "trusted snapshot case pattern binds a variable";
              `List
                [ pattern_json environment pattern;
                  term_json environment body ])
            branches
        in
        tag "Tcase"
          [ term_json environment scrutinee;
            `List branches;
            option_json type_json term.Term.t_ty ]
    | Term.Teps bound ->
        observe "termNode" "Teps";
        let variable, body = Term.t_open_bound bound in
        let body_environment, binder = bind_variable environment variable in
        tag "Teps"
          [ binder;
            term_json body_environment body;
            option_json type_json term.Term.t_ty ]
    | Term.Tquant (Term.Tforall, quantified) ->
        observe "termNode" "Tquant:Forall";
        let variables, triggers, body = Term.t_open_quant quantified in
        let body_environment, binders =
          bind_variables environment variables
        in
        tag "Tquant.Forall"
          [ `List binders;
            `List
              (List.map
                 (fun group ->
                   `List (List.map (term_json body_environment) group))
                 triggers);
            term_json body_environment body ]
    | Term.Tquant (Term.Texists, _) ->
        fail "trusted snapshot contains an existential quantifier"
    | Term.Tbinop (operator, left, right) ->
        let name, variant =
          match operator with
          | Term.Tand -> ("Tbinop.And", "Tbinop:And")
          | Term.Tor -> ("Tbinop.Or", "Tbinop:Or")
          | Term.Timplies -> ("Tbinop.Implies", "Tbinop:Implies")
          | Term.Tiff -> ("Tbinop.Iff", "Tbinop:Iff")
        in
        observe "termNode" variant;
        tag name [term_json environment left; term_json environment right]
    | Term.Tnot nested ->
        observe "termNode" "Tnot";
        tag "Tnot" [term_json environment nested]
    | Term.Ttrue -> fail "trusted snapshot contains Ttrue"
    | Term.Tfalse -> fail "trusted snapshot contains Tfalse"
  in
  `Assoc
    [ ("node", node);
      ("sourceSpan", location_json term.Term.t_loc);
      ("attributes", attributes_json term.Term.t_attrs) ]

let proposition_kind_json = function
  | Decl.Paxiom ->
      observe "propositionKind" "Paxiom";
      `String "Paxiom"
  | Decl.Plemma ->
      observe "propositionKind" "Plemma";
      `String "Plemma"
  | Decl.Pgoal ->
      observe "propositionKind" "Pgoal";
      `String "Pgoal"

let decl_json declaration =
  let environment = empty_term_environment () in
  match declaration.Decl.d_node with
  | Decl.Dtype symbol ->
      observe "declaration" "Dtype";
      tag "Dtype" [type_ref symbol]
  | Decl.Ddata declarations ->
      observe "declaration" "Ddata";
      tag "Ddata"
        [ `List
            (List.map
               (fun (symbol, constructors) ->
                 `List
                   [ type_ref symbol;
                     `List
                       (List.map
                          (fun (constructor, projections) ->
                            `List
                              [ logic_ref constructor;
                                `List
                                  (List.map
                                     (option_json logic_ref)
                                     projections) ])
                          constructors) ])
               declarations) ]
  | Decl.Dparam symbol ->
      observe "declaration" "Dparam";
      tag "Dparam" [logic_ref symbol]
  | Decl.Dlogic definitions ->
      observe "declaration" "Dlogic";
      tag "Dlogic"
        [ `List
            (List.map
               (fun (symbol, definition) ->
                 let environment = empty_term_environment () in
                 let variables, body = Decl.open_ls_defn definition in
                 let body_environment, parameters =
                   bind_variables environment variables
                 in
                 `List
                   [ logic_ref symbol;
                     `List parameters;
                     term_json body_environment body ])
               definitions) ]
  | Decl.Dind (Decl.Ind, declarations) ->
      observe "declaration" "Dind:Ind";
      tag "Dind.Ind"
        [ `List
            (List.map
               (fun (predicate, cases) ->
                 `List
                   [ logic_ref predicate;
                     `List
                       (List.map
                          (fun (proposition, formula) ->
                            `List
                              [ proposition_ref proposition;
                                term_json environment formula ])
                          cases) ])
               declarations) ]
  | Decl.Dind (Decl.Coind, _) ->
      fail "trusted snapshot contains Dind:Coind"
  | Decl.Dprop (kind, proposition, formula) ->
      observe "declaration" "Dprop";
      tag "Dprop"
        [ proposition_kind_json kind;
          proposition_ref proposition;
          term_json environment formula ]

let sorted_entries key encode entries =
  entries
  |> List.map (fun (source, target) -> (key source, encode source target))
  |> List.sort (fun (left, _) (right, _) -> String.compare left right)
  |> List.map snd

let clone_map_json map =
  `Assoc
    [ ( "typeInstantiations",
        `List
          (sorted_entries
             (fun symbol ->
               match type_ref symbol with `String value -> value | _ -> assert false)
             (fun source target -> `List [type_ref source; type_json target])
             (Ty.Mts.bindings map.Theory.sm_ty)) );
      ( "typeSymbolInstantiations",
        `List
          (sorted_entries
             (fun symbol ->
               match type_ref symbol with `String value -> value | _ -> assert false)
             (fun source target -> `List [type_ref source; type_ref target])
             (Ty.Mts.bindings map.Theory.sm_ts)) );
      ( "logicInstantiations",
        `List
          (sorted_entries
             (fun symbol ->
               match logic_ref symbol with `String value -> value | _ -> assert false)
             (fun source target -> `List [logic_ref source; logic_ref target])
             (Term.Mls.bindings map.Theory.sm_ls)) );
      ( "propositionInstantiations",
        `List
          (sorted_entries
             (fun symbol ->
               match proposition_ref symbol with
               | `String value -> value
               | _ -> assert false)
             (fun source target ->
               `List [proposition_ref source; proposition_ref target])
             (Decl.Mpr.bindings map.Theory.sm_pr)) ) ]

let meta_arg_json = function
  | Theory.MAty ty -> tag "Type" [type_json ty]
  | Theory.MAts symbol -> tag "TypeSymbol" [type_ref symbol]
  | Theory.MAls symbol -> tag "LogicSymbol" [logic_ref symbol]
  | Theory.MApr symbol -> tag "PropositionSymbol" [proposition_ref symbol]
  | Theory.MAstr value -> tag "String" [`String (hex_string value)]
  | Theory.MAint value -> tag "Integer" [`Int value]
  | Theory.MAid ident -> tag "Identifier" [ident_json ident]

let meta_json meta arguments =
  `Assoc
    [ ("nameHex", `String (hex_string meta.Theory.meta_name));
      ("arguments", `List (List.map meta_arg_json arguments)) ]

let rec namespace_json namespace =
  let entries encode values =
    values
    |> Wstdlib.Mstr.bindings
    |> List.map (fun (name, value) ->
           `List [`String (hex_string name); encode value])
    |> fun values -> `List values
  in
  `Assoc
    [ ("types", entries type_ref namespace.Theory.ns_ts);
      ("logic", entries logic_ref namespace.Theory.ns_ls);
      ("propositions", entries proposition_ref namespace.Theory.ns_pr);
      ("subspaces", entries namespace_json namespace.Theory.ns_ns) ]

let theory_json theory =
  let key = theory_key theory in
  let items =
    List.mapi
      (fun ordinal declaration ->
        let node =
          match declaration.Theory.td_node with
          | Theory.Decl decl ->
              observe "theoryItem" "Decl";
              tag "Decl" [decl_json decl]
          | Theory.Use used ->
              observe "theoryItem" "Use";
              tag "Use" [`String (theory_key used)]
          | Theory.Clone (source, map) ->
              observe "theoryItem" "Clone";
              tag "Clone"
                [ `String (theory_key source);
                  `Int ordinal;
                  clone_map_json map ]
          | Theory.Meta (meta, arguments) ->
              observe "theoryItem" "Meta";
              tag "Meta" [meta_json meta arguments]
        in
        `Assoc [("ordinal", `Int ordinal); ("node", node)])
      theory.Theory.th_decls
  in
  `Assoc
    [ ("key", `String key);
      ( "pathHex",
        `List
      (List.map
             (fun segment -> `String (hex_string segment))
             theory.Theory.th_path) );
      ("name", ident_json theory.Theory.th_name);
      ("items", `List items);
      ("exportNamespace", namespace_json theory.Theory.th_export) ]

let ity_flag_json flag =
  `Assoc
    [ ("frozen", `Bool flag.Ity.its_frozen);
      ("exposed", `Bool flag.Ity.its_exposed);
      ("liable", `Bool flag.Ity.its_liable);
      ("fixed", `Bool flag.Ity.its_fixed);
      ("visible", `Bool flag.Ity.its_visible) ]

let rec ity_json ity =
  match ity.Ity.ity_node with
  | Ity.Ityapp (symbol, arguments, regions) ->
      observe "programTypeNode" "Ityapp";
      tag "ItyApp"
        [ program_type_ref symbol;
          `List (List.map ity_json arguments);
          `List (List.map ity_json regions);
          `Bool ity.Ity.ity_pure ]
  | Ity.Ityvar _ -> fail "trusted snapshot contains Ityvar"
  | Ity.Ityreg _ -> fail "trusted snapshot contains Ityreg"

let program_type_definition_json definition =
  match definition with
  | Ty.NoDef -> tag "NoDef" []
  | Ty.Alias ity -> tag "Alias" [ity_json ity]
  | Ty.Range range ->
      tag "Range" [bigint range.Number.ir_lower; bigint range.Number.ir_upper]
  | Ty.Float format ->
      tag "Float"
        [ `Int format.Number.fp_exponent_digits;
          `Int format.Number.fp_significand_digits ]

let pvsymbol_json variable =
  `Assoc
    [ ("name", ident_json variable.Ity.pv_vs.Term.vs_name);
      ("ity", ity_json variable.Ity.pv_ity);
      ("ghost", `Bool variable.Ity.pv_ghost) ]

let program_type_symbol_json symbol =
  if symbol.Ity.its_regions <> [] then
    fail
      ("trusted program type contains regions: "
       ^ symbol.Ity.its_ts.Ty.ts_name.Ident.id_string);
  `Assoc
    [ ("tag", `String "ProgramTypeSymbol");
      ("logicTypeSymbol", type_ref symbol.Ity.its_ts);
      ("nonfree", `Bool symbol.Ity.its_nonfree);
      ("private", `Bool symbol.Ity.its_private);
      ("mutable", `Bool symbol.Ity.its_mutable);
      ("fragile", `Bool symbol.Ity.its_fragile);
      ("mutableFields", `List (List.map pvsymbol_json symbol.Ity.its_mfields));
      ("immutableFields", `List (List.map pvsymbol_json symbol.Ity.its_ofields));
      ("argumentFlags", `List (List.map ity_flag_json symbol.Ity.its_arg_flg));
      ("regionFlags", `List (List.map ity_flag_json symbol.Ity.its_reg_flg));
      ("definition", program_type_definition_json symbol.Ity.its_def) ]

let mask_json = function
  | Ity.MaskVisible ->
      observe "programMask" "Visible";
      `String "Visible"
  | Ity.MaskGhost ->
      observe "programMask" "Ghost";
      `String "Ghost"
  | Ity.MaskTuple _ -> fail "trusted snapshot contains a tuple mask"

let termination_json = function
  | Ity.Total ->
      observe "programTermination" "Total";
      `String "Total"
  | Ity.Partial -> fail "trusted snapshot contains a partial effect"
  | Ity.Diverges -> fail "trusted snapshot contains a diverging effect"

type program_environment = {
  variables_by_term_symbol : int Term.Mvs.t;
  variables_by_program_symbol : int Ity.Mpv.t;
  variables_in_order : Ity.pvsymbol list;
}

let empty_program_environment =
  { variables_by_term_symbol = Term.Mvs.empty;
    variables_by_program_symbol = Ity.Mpv.empty;
    variables_in_order = [] }

let add_program_variable environment variable =
  match Ity.Mpv.find_opt variable environment.variables_by_program_symbol with
  | Some _ -> environment
  | None ->
      let id = List.length environment.variables_in_order in
      { variables_by_term_symbol =
          Term.Mvs.add variable.Ity.pv_vs id
            environment.variables_by_term_symbol;
        variables_by_program_symbol =
          Ity.Mpv.add variable id environment.variables_by_program_symbol;
        variables_in_order = environment.variables_in_order @ [variable] }

let add_program_variables environment variables =
  List.fold_left add_program_variable environment variables

let program_variable_id environment variable =
  match Ity.Mpv.find_opt variable environment.variables_by_program_symbol with
  | Some id -> id
  | None ->
      fail
        ("unbound program variable "
         ^ variable.Ity.pv_vs.Term.vs_name.Ident.id_string)

let term_environment_of_program environment =
  { local_variables = Term.Mvs.empty;
    program_variables = environment.variables_by_term_symbol;
    next_local = ref 0 }

let cty_program_environment cty =
  let environment =
    add_program_variables empty_program_environment cty.Ity.cty_args
  in
  let environment =
    add_program_variables environment
      (Ity.Spv.elements cty.Ity.cty_effect.Ity.eff_reads)
  in
  Ity.Mpv.bindings cty.Ity.cty_oldies
  |> List.fold_left
       (fun environment (snapshot, original) ->
         add_program_variables
           (add_program_variable environment snapshot)
           [original])
       environment

let program_variable_descriptor environment variable =
  `Assoc
    [ ("id", `Int (program_variable_id environment variable));
      ("name", ident_json variable.Ity.pv_vs.Term.vs_name);
      ("ity", ity_json variable.Ity.pv_ity);
      ("ghost", `Bool variable.Ity.pv_ghost) ]

let term_with_program_environment environment term =
  term_json (term_environment_of_program environment) term

let post_json environment post =
  let result, body = Ity.open_post post in
  let term_environment = term_environment_of_program environment in
  let body_environment, binder = bind_variable term_environment result in
  `Assoc
    [ ("result", binder);
      ("formula", term_json body_environment body) ]

let effect_json environment effect =
  if not (Ity.eff_pure effect) then
    fail "trusted snapshot contains an impure effect";
  observe "programEffect" "Pure";
  if not (Ity.Mreg.is_empty effect.Ity.eff_writes) then
    fail "trusted pure effect contains writes";
  if not (Ity.Sreg.is_empty effect.Ity.eff_taints) then
    fail "trusted pure effect contains taints";
  if not (Ity.Sreg.is_empty effect.Ity.eff_covers) then
    fail "trusted pure effect contains covers";
  if not (Ity.Sreg.is_empty effect.Ity.eff_resets) then
    fail "trusted pure effect contains resets";
  if not (Ity.Sxs.is_empty effect.Ity.eff_raises) then
    fail "trusted pure effect contains raised exceptions";
  `Assoc
    [ ( "reads",
        `List
          (List.map
             (fun variable ->
               `Int (program_variable_id environment variable))
             (Ity.Spv.elements effect.Ity.eff_reads)) );
      ("writes", `List []);
      ("taints", `List []);
      ("covers", `List []);
      ("resets", `List []);
      ("raises", `List []);
      ( "spoils",
        `List
          (List.map
             (fun variable -> `Int (type_variable_id variable))
             (Ty.Stv.elements effect.Ity.eff_spoils)) );
      ("termination", termination_json effect.Ity.eff_oneway);
      ("ghost", `Bool effect.Ity.eff_ghost) ]

let freeze_json freeze =
  if not (Ity.Mreg.is_empty freeze.Ity.isb_reg) then
    fail "trusted computation type freezes a region";
  `Assoc
    [ ( "typeVariables",
        `List
          (List.map
             (fun (variable, ity) ->
               `List [`Int (type_variable_id variable); ity_json ity])
             (Ty.Mtv.bindings freeze.Ity.isb_var)) );
      ("regions", `List []) ]

let cty_json cty =
  let environment = cty_program_environment cty in
  let exceptional_posts =
    Ity.Mxs.bindings cty.Ity.cty_xpost
  in
  if exceptional_posts <> [] then
    fail "trusted computation type contains exceptional postconditions";
  `Assoc
    [ ( "programVariables",
        `List
          (List.map
             (program_variable_descriptor environment)
             environment.variables_in_order) );
      ( "arguments",
        `List
          (List.map
             (fun variable ->
               `Int (program_variable_id environment variable))
             cty.Ity.cty_args) );
      ( "preconditions",
        `List
          (List.map
             (term_with_program_environment environment)
             cty.Ity.cty_pre) );
      ( "postconditions",
        `List (List.map (post_json environment) cty.Ity.cty_post) );
      ("exceptionalPostconditions", `List []);
      ( "oldies",
        `List
          (List.map
             (fun (snapshot, original) ->
               `List
                 [ `Int (program_variable_id environment snapshot);
                   `Int (program_variable_id environment original) ])
             (Ity.Mpv.bindings cty.Ity.cty_oldies)) );
      ("effect", effect_json environment cty.Ity.cty_effect);
      ("result", ity_json cty.Ity.cty_result);
      ("mask", mask_json cty.Ity.cty_mask);
      ("freeze", freeze_json cty.Ity.cty_freeze) ]

let routine_logic_json = function
  | Expr.RLnone ->
      observe "routineLogic" "RLnone";
      tag "RLnone" []
  | Expr.RLls symbol ->
      observe "routineLogic" "RLls";
      tag "RLls" [logic_ref symbol]
  | Expr.RLpv _ -> fail "trusted snapshot contains RLpv"
  | Expr.RLlemma -> fail "trusted snapshot contains RLlemma"

let routine_symbol_json symbol =
  `Assoc
    [ ("tag", `String "RoutineSymbol");
      ("name", ident_json symbol.Expr.rs_name);
      ("cty", cty_json symbol.Expr.rs_cty);
      ("logic", routine_logic_json symbol.Expr.rs_logic);
      ("field", option_json pvsymbol_json symbol.Expr.rs_field) ]

let cexp_json computation =
  let node =
    match computation.Expr.c_node with
    | Expr.Cany ->
        observe "programComputation" "Cany";
        tag "Cany" []
    | Expr.Cfun _ ->
        observe "programComputation" "Cfun";
        tag "Cfun" []
    | Expr.Capp _ -> fail "trusted snapshot contains Capp"
    | Expr.Cpur _ -> fail "trusted snapshot contains Cpur"
  in
  `Assoc [("node", node); ("cty", cty_json computation.Expr.c_cty)]

let invariant_environment definitions =
  let fields =
    List.concat_map
      (fun definition ->
        definition.Pdecl.itd_fields
        |> List.filter_map (fun routine -> routine.Expr.rs_field))
      definitions
  in
  add_program_variables empty_program_environment fields

let pdecl_json pdecl =
  let pure = `List (List.map decl_json pdecl.Pdecl.pd_pure) in
  let node =
    match pdecl.Pdecl.pd_node with
    | Pdecl.PDtype definitions ->
        observe "programDeclaration" "PDtype";
        let environment = invariant_environment definitions in
        tag "PDtype"
          [ `List
              (List.map
                 (fun definition ->
                   let witness =
                     match definition.Pdecl.itd_witness with
                     | None ->
                         observe "programTypeWitness" "Absent";
                         `Null
                     | Some _ ->
                         fail "trusted program type contains a witness"
                   in
                   `Assoc
                     [ ("symbol", program_type_ref definition.Pdecl.itd_its);
                       ( "fields",
                         `List
                           (List.map routine_ref definition.Pdecl.itd_fields) );
                       ( "constructors",
                         `List
                           (List.map routine_ref
                              definition.Pdecl.itd_constructors) );
                       ( "invariants",
                         `List
                           (List.map
                              (term_with_program_environment environment)
                              definition.Pdecl.itd_invariant) );
                       ("witness", witness) ])
                 definitions) ]
    | Pdecl.PDpure ->
        observe "programDeclaration" "PDpure";
        tag "PDpure" []
    | Pdecl.PDlet (Expr.LDsym (symbol, computation)) ->
        observe "programDeclaration" "PDlet:LDsym";
        tag "PDlet.LDsym" [routine_ref symbol; cexp_json computation]
    | Pdecl.PDlet (Expr.LDvar _) ->
        fail "trusted snapshot contains PDlet:LDvar"
    | Pdecl.PDlet (Expr.LDrec _) ->
        fail "trusted snapshot contains PDlet:LDrec"
    | Pdecl.PDexn _ -> fail "trusted snapshot contains PDexn"
  in
  `Assoc [("node", node); ("pureDeclarations", pure)]

let clone_prop_kind_json = function
  | Decl.Paxiom -> `String "Paxiom"
  | Decl.Plemma -> `String "Plemma"
  | Decl.Pgoal -> `String "Pgoal"

let module_clone_json instance =
  if not (Ity.Mxs.is_empty instance.Pmodule.mi_xs) then
    fail "trusted module clone contains an exception instantiation";
  let pairs key encode bindings =
    sorted_entries key encode bindings |> fun values -> `List values
  in
  let ref_string encode value =
    match encode value with `String string -> string | _ -> assert false
  in
  `Assoc
    [ ("sourceModule", `String (module_key instance.Pmodule.mi_mod));
      ( "typeInstantiations",
        pairs
          (ref_string type_ref)
          (fun source target -> `List [type_ref source; ity_json target])
          (Ty.Mts.bindings instance.Pmodule.mi_ty) );
      ( "programTypeInstantiations",
        pairs
          (ref_string type_ref)
          (fun source target ->
            `List [type_ref source; program_type_ref target])
          (Ty.Mts.bindings instance.Pmodule.mi_ts) );
      ( "logicInstantiations",
        pairs
          (ref_string logic_ref)
          (fun source target -> `List [logic_ref source; logic_ref target])
          (Term.Mls.bindings instance.Pmodule.mi_ls) );
      ( "propositionInstantiations",
        pairs
          (ref_string proposition_ref)
          (fun source target ->
            `List [proposition_ref source; proposition_ref target])
          (Decl.Mpr.bindings instance.Pmodule.mi_pr) );
      ( "propositionKinds",
        pairs
          (ref_string proposition_ref)
          (fun source kind ->
            `List [proposition_ref source; clone_prop_kind_json kind])
          (Decl.Mpr.bindings instance.Pmodule.mi_pk) );
      ( "programVariableInstantiations",
        `List
          (List.map
             (fun (source, target) ->
               `List
                 [ `Assoc
                     [ ("name", ident_json source.Term.vs_name);
                       ("type", type_json source.Term.vs_ty) ];
                   pvsymbol_json target ])
             (Term.Mvs.bindings instance.Pmodule.mi_pv)) );
      ( "routineInstantiations",
        pairs
          (ref_string routine_ref)
          (fun source target ->
            `List [routine_ref source; routine_ref target])
          (Expr.Mrs.bindings instance.Pmodule.mi_rs) );
      ("exceptionInstantiations", `List []);
      ("defaultPropositionKind", clone_prop_kind_json instance.Pmodule.mi_df) ]

let rec program_namespace_json namespace =
  if not (Wstdlib.Mstr.is_empty namespace.Pmodule.ns_xs) then
    fail "trusted export namespace contains an exception symbol";
  let entries encode values =
    values
    |> Wstdlib.Mstr.bindings
    |> List.map (fun (name, value) ->
           `List [`String (hex_string name); encode value])
    |> fun values -> `List values
  in
  let program_symbol_json = function
    | Pmodule.RS symbol -> routine_ref symbol
    | Pmodule.PV _ ->
        fail "trusted export namespace contains a program variable"
    | Pmodule.OO _ ->
        fail "trusted export namespace contains an overload set"
  in
  `Assoc
    [ ("types", entries program_type_ref namespace.Pmodule.ns_ts);
      ("program", entries program_symbol_json namespace.Pmodule.ns_ps);
      ("exceptions", `List []);
      ("subspaces", entries program_namespace_json namespace.Pmodule.ns_ns) ]

let module_json pmodule =
  let owner = module_key pmodule in
  let next_ordinal = ref 0 in
  let rec units_json path units =
    units
    |> List.mapi (fun path_ordinal unit_ ->
           let ordinal = !next_ordinal in
           incr next_ordinal;
           let ordinal_path = path @ [path_ordinal] in
           let node =
             match unit_ with
             | Pmodule.Udecl pdecl ->
                 observe "moduleItem" "Udecl";
                 tag "Udecl" [pdecl_json pdecl]
             | Pmodule.Uuse used ->
                 observe "moduleItem" "Uuse";
                 tag "Uuse" [`String (module_key used)]
             | Pmodule.Uclone instance ->
                 observe "moduleItem" "Uclone";
                 tag "Uclone" [module_clone_json instance]
             | Pmodule.Umeta (meta, arguments) ->
                 observe "moduleItem" "Umeta";
                 tag "Umeta" [meta_json meta arguments]
             | Pmodule.Uscope (name, nested) ->
                 observe "moduleItem" "Uscope";
                 tag "Uscope"
                   [ `String (hex_string name);
                     `List (units_json ordinal_path nested) ]
           in
           `Assoc
             [ ("ordinal", `Int ordinal);
               ("ordinalPath", `List (List.map (fun value -> `Int value) ordinal_path));
               ("node", node) ])
  in
  `Assoc
    [ ("key", `String owner);
      ("pureTheory", `String (theory_key pmodule.Pmodule.mod_theory));
      ("items", `List (units_json [] pmodule.Pmodule.mod_units));
      ("exportNamespace", program_namespace_json pmodule.Pmodule.mod_export) ]

let catalog_entry_json = function
  | Type_entry (locator, symbol) ->
      `Assoc
        [("locator", locator_json locator); ("symbol", type_symbol_json symbol)]
  | Logic_entry (locator, symbol) ->
      `Assoc
        [("locator", locator_json locator); ("symbol", logic_symbol_json symbol)]
  | Proposition_entry (locator, symbol) ->
      `Assoc
        [ ("locator", locator_json locator);
          ("symbol", proposition_symbol_json symbol) ]
  | Program_type_entry (locator, symbol) ->
      `Assoc
        [ ("locator", locator_json locator);
          ("symbol", program_type_symbol_json symbol) ]
  | Routine_entry (locator, symbol) ->
      `Assoc
        [ ("locator", locator_json locator);
          ("symbol", routine_symbol_json symbol) ]

let catalog_locator = function
  | Type_entry (locator, _)
  | Logic_entry (locator, _)
  | Proposition_entry (locator, _)
  | Program_type_entry (locator, _)
  | Routine_entry (locator, _) -> locator_string locator

let observed_json () =
  !observed
  |> StringMap.bindings
  |> List.map (fun (category, variants) ->
         ( category,
           `List
             (List.map (fun variant -> `String variant)
                (StringSet.elements variants)) ))
  |> fun fields -> `Assoc fields

let type_variables_json () =
  !type_variables
  |> List.sort (fun (left, _) (right, _) -> Int.compare left right)
  |> List.map (fun (id, variable) ->
         `Assoc
           [ ("id", `Int id);
             ("name", ident_json variable.Ty.tv_name) ])
  |> fun variables -> `List variables

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
  Arg.parse specification
    (fun value -> fail ("unexpected argument: " ^ value))
    "export_snapshot --stdlib PATH --theory NAME --module NAME";
  let stdlib =
    match !stdlib with
    | Some path -> Unix.realpath path
    | None -> fail "--stdlib is required"
  in
  stdlib_root := stdlib;
  let environment = Env.create_env [stdlib] in
  let theory_root_names = List.rev !theory_roots in
  let module_root_names = List.rev !module_roots in
  let root_theories =
    List.map (read_theory environment) theory_root_names
  in
  let root_modules =
    List.map (read_module environment) module_root_names
  in
  let modules = collect_modules root_modules in
  let projected_theories =
    StringMap.bindings modules
    |> List.map (fun (_, pmodule) -> pmodule.Pmodule.mod_theory)
  in
  let theories, _ = collect_theories (root_theories @ projected_theories) in
  StringMap.iter (fun _ theory -> preindex_theory theory) theories;
  StringMap.iter (fun _ pmodule -> preindex_module pmodule) modules;
  let encoded_theories =
    StringMap.bindings theories
    |> List.map (fun (_, theory) -> theory_json theory)
  in
  let encoded_modules =
    StringMap.bindings modules
    |> List.map (fun (_, pmodule) -> module_json pmodule)
  in
  let encoded_catalog =
    !catalog_entries
    |> List.sort (fun left right ->
           String.compare (catalog_locator left) (catalog_locator right))
    |> List.map catalog_entry_json
  in
  let result =
    `Assoc
      [ ("schemaVersion", `Int 1);
        ( "roots",
          `Assoc
            [ ( "theories",
                `List
                  (List.map2
                     (fun requested theory ->
                       `Assoc
                         [ ("requested", `String requested);
                           ("resolvedKey", `String (theory_key theory)) ])
                     theory_root_names root_theories) );
              ( "modules",
                `List
                  (List.map2
                     (fun requested pmodule ->
                       `Assoc
                         [ ("requested", `String requested);
                           ("resolvedKey", `String (module_key pmodule)) ])
                     module_root_names root_modules) ) ] );
        ("theories", `List encoded_theories);
        ("modules", `List encoded_modules);
        ("catalog", `List encoded_catalog);
        ("typeVariables", type_variables_json ());
        ("observedVariants", observed_json ()) ]
  in
  Yojson.Safe.to_channel ~std:true stdout result;
  output_char stdout '\n'

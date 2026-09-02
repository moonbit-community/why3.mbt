(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   Why3 Development Team      *)
(*  Copyright 2010-2023 -- Inria - CNRS - Paris-Saclay University   *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  Snapshot-free source-symbol catalog adapter, modified 2026.     *)
(*                                                                  *)
(********************************************************************)

open Why3

module StringMap = Map.Make (String)

type locator = {
  owner : string;
  item : int;
  inner : int;
  kind : string;
  digest : string;
}

type catalog = {
  theories : Theory.theory list;
  type_locations : locator Ty.Mts.t;
  logic_locations : locator Term.Mls.t;
  proposition_locations : locator Decl.Mpr.t;
}

type raw_locator = {
  raw_owner : string;
  raw_item : int;
  raw_inner : int;
  raw_kind : string;
}

type raw_entry =
  | Type_entry of raw_locator * Ty.tysymbol
  | Logic_entry of raw_locator * Term.lsymbol
  | Proposition_entry of raw_locator * Decl.prsymbol

let fail message = invalid_arg ("source_catalog: " ^ message)

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

let option_json encode = function
  | None -> `Null
  | Some value -> encode value

let bigint value = `String (BigInt.to_string value)

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

let locator_string locator =
  Printf.sprintf "%s#%d#%d#%s" locator.raw_owner locator.raw_item
    locator.raw_inner locator.raw_kind

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
  StringMap.bindings !theories |> List.map snd

let make_raw_locator owner item inner kind =
  { raw_owner = owner; raw_item = item; raw_inner = inner; raw_kind = kind }

let source_path stdlib file =
  let absolute =
    if Filename.is_relative file then Filename.concat stdlib file else file
  in
  let absolute =
    if Sys.file_exists absolute then Unix.realpath absolute
    else fail ("source location does not exist: " ^ file)
  in
  let prefix = stdlib ^ Filename.dir_sep in
  let prefix_length = String.length prefix in
  if String.length absolute < prefix_length
     || String.sub absolute 0 prefix_length <> prefix
  then fail ("source location escapes the pinned stdlib: " ^ absolute);
  ( String.sub absolute prefix_length
      (String.length absolute - prefix_length),
    absolute )

let source_cache : (string, string * int array) Hashtbl.t =
  Hashtbl.create 37

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
      let cached = (source, Array.of_list (List.rev !starts)) in
      Hashtbl.add source_cache path cached;
      cached

let source_offset path line column =
  let source, starts = load_source path in
  if line < 1 || line > Array.length starts then
    fail (Printf.sprintf "invalid source line %d in %s" line path);
  let offset = starts.(line - 1) + column in
  if offset < 0 || offset > String.length source then
    fail (Printf.sprintf "invalid source column %d:%d in %s" line column path);
  offset

let location_json stdlib = function
  | None -> `Null
  | Some position ->
      let file, start_line, start_column, end_line, end_column =
        Loc.get position
      in
      let relative, absolute = source_path stdlib file in
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

let ident_json stdlib ident =
  `Assoc
    [ ("nameHex", `String (hex_string ident.Ident.id_string));
      ("attributes", attributes_json ident.Ident.id_attrs);
      ("sourceSpan", location_json stdlib ident.Ident.id_loc) ]

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

let sha256_json value =
  Digestif.SHA256.(
    to_hex (digest_string (Yojson.Safe.to_string ~std:true value ^ "\n")))

let build ~stdlib roots =
  let stdlib = Unix.realpath stdlib in
  Hashtbl.clear source_cache;
  let theories = collect_theories roots in
  let raw_type_locations = ref Ty.Mts.empty in
  let raw_logic_locations = ref Term.Mls.empty in
  let raw_proposition_locations = ref Decl.Mpr.empty in
  let entries = ref [] in
  let add_type locator symbol =
    if not (Ty.Mts.mem symbol !raw_type_locations) then begin
      raw_type_locations := Ty.Mts.add symbol locator !raw_type_locations;
      entries := Type_entry (locator, symbol) :: !entries
    end
  in
  let add_logic locator symbol =
    if not (Term.Mls.mem symbol !raw_logic_locations) then begin
      raw_logic_locations := Term.Mls.add symbol locator !raw_logic_locations;
      entries := Logic_entry (locator, symbol) :: !entries
    end
  in
  let add_proposition locator symbol =
    if not (Decl.Mpr.mem symbol !raw_proposition_locations) then begin
      raw_proposition_locations :=
        Decl.Mpr.add symbol locator !raw_proposition_locations;
      entries := Proposition_entry (locator, symbol) :: !entries
    end
  in
  let preindex_decl owner item declaration =
    let inner = ref 0 in
    let fresh kind =
      let locator = make_raw_locator owner item !inner kind in
      incr inner;
      locator
    in
    match declaration.Decl.d_node with
    | Decl.Dtype symbol -> add_type (fresh "type") symbol
    | Decl.Ddata declarations ->
        List.iter
          (fun (symbol, constructors) ->
            add_type (fresh "type") symbol;
            List.iter
              (fun (constructor, projections) ->
                add_logic (fresh "logic") constructor;
                List.iter
                  (Option.iter
                     (fun projection -> add_logic (fresh "logic") projection))
                  projections)
              constructors)
          declarations
    | Decl.Dparam symbol -> add_logic (fresh "logic") symbol
    | Decl.Dlogic definitions ->
        List.iter
          (fun (symbol, _) -> add_logic (fresh "logic") symbol)
          definitions
    | Decl.Dind (_, declarations) ->
        List.iter
          (fun (predicate, cases) ->
            add_logic (fresh "logic") predicate;
            List.iter
              (fun (proposition, _) ->
                add_proposition (fresh "proposition") proposition)
              cases)
          declarations
    | Decl.Dprop (_, proposition, _) ->
        add_proposition (fresh "proposition") proposition
  in
  List.iter
    (fun theory ->
      let owner = theory_key theory in
      List.iteri
        (fun item declaration ->
          match declaration.Theory.td_node with
          | Theory.Decl decl -> preindex_decl owner item decl
          | Theory.Use _ | Theory.Clone _ | Theory.Meta _ -> ())
        theory.Theory.th_decls)
    theories;
  let raw_location find symbol kind name =
    match find symbol with
    | Some locator -> locator
    | None -> fail ("uncatalogued " ^ kind ^ " symbol " ^ name)
  in
  let raw_type symbol =
    raw_location
      (fun value -> Ty.Mts.find_opt value !raw_type_locations)
      symbol "type" symbol.Ty.ts_name.Ident.id_string
  in
  let type_variables = ref Ty.Mtv.empty in
  let next_type_variable = ref 0 in
  let type_variable_id variable =
    match Ty.Mtv.find_opt variable !type_variables with
    | Some id -> id
    | None ->
        let id = !next_type_variable in
        incr next_type_variable;
        type_variables := Ty.Mtv.add variable id !type_variables;
        id
  in
  let rec type_json ty =
    match ty.Ty.ty_node with
    | Ty.Tyvar variable -> tag "TyVar" [`Int (type_variable_id variable)]
    | Ty.Tyapp (symbol, arguments) ->
        tag "TyApp"
          [ `String (locator_string (raw_type symbol));
            `List (List.map type_json arguments) ]
  in
  let type_definition_json = function
    | Ty.NoDef -> tag "NoDef" []
    | Ty.Alias ty -> tag "Alias" [type_json ty]
    | Ty.Range range ->
        tag "Range" [bigint range.Number.ir_lower; bigint range.Number.ir_upper]
    | Ty.Float format ->
        tag "Float"
          [ `Int format.Number.fp_exponent_digits;
            `Int format.Number.fp_significand_digits ]
  in
  let type_symbol_json symbol =
    `Assoc
      [ ("tag", `String "TypeSymbol");
        ("name", ident_json stdlib symbol.Ty.ts_name);
        ( "typeParameters",
          `List
            (List.map
               (fun variable -> `Int (type_variable_id variable))
               symbol.Ty.ts_args) );
        ("definition", type_definition_json symbol.Ty.ts_def);
        ( "builtinKind",
          option_json (fun value -> `String value)
            (builtin_type_kind symbol) ) ]
  in
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
        ("name", ident_json stdlib symbol.Term.ls_name);
        ( "typeParameters",
          `List
            (List.map
               (fun variable -> `Int (type_variable_id variable))
               type_parameters) );
        ("argumentTypes", `List (List.map type_json symbol.Term.ls_args));
        ("resultType", option_json type_json symbol.Term.ls_value);
        ("role", role) ]
  in
  let proposition_symbol_json symbol =
    `Assoc
      [ ("tag", `String "PropositionSymbol");
        ("name", ident_json stdlib symbol.Decl.pr_name) ]
  in
  let entry_locator = function
    | Type_entry (locator, _)
    | Logic_entry (locator, _)
    | Proposition_entry (locator, _) -> locator
  in
  let sorted_entries =
    List.sort
      (fun left right ->
        String.compare
          (locator_string (entry_locator left))
          (locator_string (entry_locator right)))
      !entries
  in
  let type_locations = ref Ty.Mts.empty in
  let logic_locations = ref Term.Mls.empty in
  let proposition_locations = ref Decl.Mpr.empty in
  let located raw digest =
    { owner = raw.raw_owner;
      item = raw.raw_item;
      inner = raw.raw_inner;
      kind = raw.raw_kind;
      digest }
  in
  List.iter
    (function
      | Type_entry (raw, symbol) ->
          type_locations :=
            Ty.Mts.add symbol (located raw (sha256_json (type_symbol_json symbol)))
              !type_locations
      | Logic_entry (raw, symbol) ->
          logic_locations :=
            Term.Mls.add symbol
              (located raw (sha256_json (logic_symbol_json symbol)))
              !logic_locations
      | Proposition_entry (raw, symbol) ->
          proposition_locations :=
            Decl.Mpr.add symbol
              (located raw (sha256_json (proposition_symbol_json symbol)))
              !proposition_locations)
    sorted_entries;
  { theories;
    type_locations = !type_locations;
    logic_locations = !logic_locations;
    proposition_locations = !proposition_locations }

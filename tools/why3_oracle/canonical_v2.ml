(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit canonical oracle adapter, modified 2026-07-22.          *)
(*                                                                  *)
(********************************************************************)

open Why3
open Yojson.Safe

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let fail message = invalid_arg ("canonical_v2: " ^ message)

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

(* OCaml does not specify constructor-argument evaluation order.  Canonical
   symbol identities are assigned on first encounter, while the MoonBit
   encoder evaluates array elements from left to right.  Keep every
   identity-bearing traversal explicit instead of relying on list literals. *)
let ordered thunks =
  List.rev
    (List.fold_left (fun values thunk -> thunk () :: values) [] thunks)

let ordered_map encode values =
  List.rev
    (List.fold_left
       (fun encoded value -> encode value :: encoded)
       [] values)

let ordered_mapi encode values =
  let _, reversed =
    List.fold_left
      (fun (index, encoded) value ->
        (index + 1, encode index value :: encoded))
      (0, []) values
  in
  List.rev reversed

let otag name fields = tag name (ordered fields)
let olist fields = `List (ordered fields)

let none = tag "none" []
let some value = tag "some" [value]
let option_json encode = function None -> none | Some value -> some (encode value)
let bigint value = `Intlit (BigInt.to_string value)

let compact value = Yojson.Safe.to_string ~std:true value

let semantic_map entries =
  entries
  |> List.map (fun (key, value) -> (compact key, compact value, key, value))
  |> List.sort (fun (left_key, left_value, _, _) (right_key, right_value, _, _) ->
         let order = String.compare left_key right_key in
         if order <> 0 then order else String.compare left_value right_value)
  |> List.map (fun (_, _, key, value) -> `List [key; value])
  |> fun values -> `List values

let split_qualified name =
  match List.rev (String.split_on_char '.' name) with
  | [] -> assert false
  | leaf :: reversed_path -> (List.rev reversed_path, leaf)

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

type locator = {
  owner : string;
  item : int;
  inner : int;
  kind : string;
  digest : string;
}

let locator_id owner item inner kind =
  Printf.sprintf "%s#%d#%d#%s" owner item inner kind

type catalog = {
  snapshot_digests : string StringMap.t;
  type_locations : locator Ty.Mts.t;
  logic_locations : locator Term.Mls.t;
  proposition_locations : locator Decl.Mpr.t;
  tdecl_occurrences : (string * int) list Theory.Mtdecl.t;
}

let empty_catalog =
  { snapshot_digests = StringMap.empty;
    type_locations = Ty.Mts.empty;
    logic_locations = Term.Mls.empty;
    proposition_locations = Decl.Mpr.empty;
    tdecl_occurrences = Theory.Mtdecl.empty }

let json_member name = function
  | `Assoc fields ->
      begin match List.assoc_opt name fields with
      | Some value -> value
      | None -> fail ("missing JSON field " ^ name)
      end
  | _ -> fail ("expected object while reading " ^ name)

let json_string = function
  | `String value -> value
  | _ -> fail "expected JSON string"

let json_int = function
  | `Int value -> value
  | _ -> fail "expected JSON integer"

let json_list = function
  | `List values -> values
  | _ -> fail "expected JSON array"

let sha256_string value =
  Digestif.SHA256.(to_hex (digest_string value))

let snapshot_digests snapshot =
  json_member "catalog" snapshot
  |> json_list
  |> List.fold_left
       (fun digests entry ->
         let locator = json_member "locator" entry in
         let id = json_string (json_member "id" locator) in
         let symbol = json_member "symbol" entry in
         let digest = sha256_string (compact symbol ^ "\n") in
         StringMap.add id digest digests)
       StringMap.empty

let catalog_locator digests owner item inner kind =
  let id = locator_id owner item inner kind in
  match StringMap.find_opt id digests with
  | Some digest -> { owner; item; inner; kind; digest }
  | None -> fail ("snapshot catalog has no locator " ^ id)

let preindex_decl digests catalog owner item declaration =
  let inner = ref 0 in
  let fresh kind =
    let result = catalog_locator digests owner item !inner kind in
    incr inner;
    result
  in
  match declaration.Decl.d_node with
  | Decl.Dtype symbol ->
      { catalog with
        type_locations = Ty.Mts.add symbol (fresh "type") catalog.type_locations }
  | Decl.Ddata declarations ->
      List.fold_left
        (fun catalog (symbol, constructors) ->
          let catalog =
            { catalog with
              type_locations =
                Ty.Mts.add symbol (fresh "type") catalog.type_locations }
          in
          List.fold_left
            (fun catalog (constructor, projections) ->
              let catalog =
                { catalog with
                  logic_locations =
                    Term.Mls.add constructor (fresh "logic")
                      catalog.logic_locations }
              in
              List.fold_left
                (fun catalog projection ->
                  match projection with
                  | None -> catalog
                  | Some projection ->
                      { catalog with
                        logic_locations =
                          Term.Mls.add projection (fresh "logic")
                            catalog.logic_locations })
                catalog projections)
            catalog constructors)
        catalog declarations
  | Decl.Dparam symbol ->
      { catalog with
        logic_locations =
          Term.Mls.add symbol (fresh "logic") catalog.logic_locations }
  | Decl.Dlogic definitions ->
      List.fold_left
        (fun catalog (symbol, _) ->
          { catalog with
            logic_locations =
              Term.Mls.add symbol (fresh "logic") catalog.logic_locations })
        catalog definitions
  | Decl.Dind (_, declarations) ->
      List.fold_left
        (fun catalog (predicate, cases) ->
          let catalog =
            { catalog with
              logic_locations =
                Term.Mls.add predicate (fresh "logic") catalog.logic_locations }
          in
          List.fold_left
            (fun catalog (proposition, _) ->
              { catalog with
                proposition_locations =
                  Decl.Mpr.add proposition (fresh "proposition")
                    catalog.proposition_locations })
            catalog cases)
        catalog declarations
  | Decl.Dprop (_, proposition, _) ->
      { catalog with
        proposition_locations =
          Decl.Mpr.add proposition (fresh "proposition")
            catalog.proposition_locations }

let preindex_theory digests catalog theory =
  let owner = theory_key theory in
  List.fold_left
    (fun catalog (item, tdecl) ->
      let occurrences =
        Option.value ~default:[]
          (Theory.Mtdecl.find_opt tdecl catalog.tdecl_occurrences)
      in
      let catalog =
        { catalog with
          tdecl_occurrences =
            Theory.Mtdecl.add tdecl ((owner, item) :: occurrences)
              catalog.tdecl_occurrences }
      in
      match tdecl.Theory.td_node with
      | Theory.Decl declaration ->
          preindex_decl digests catalog owner item declaration
      | Theory.Use _ | Theory.Clone _ | Theory.Meta _ -> catalog)
    catalog (List.mapi (fun index value -> (index, value)) theory.Theory.th_decls)

let load_catalog environment snapshot_path =
  let snapshot = Yojson.Safe.from_file snapshot_path in
  let digests = snapshot_digests snapshot in
  let theory_keys =
    json_member "theories" snapshot
    |> json_list
    |> List.map (fun value -> json_string (json_member "key" value))
  in
  List.fold_left
    (fun catalog key ->
      let path, name = split_qualified key in
      preindex_theory digests catalog (Env.read_theory environment path name))
    { empty_catalog with snapshot_digests = digests } theory_keys

type source = {
  label : string;
  absolute : string;
  bytes : string;
  line_starts : int array;
}

let read_source label path =
  let channel = open_in_bin path in
  let length = in_channel_length channel in
  let bytes = really_input_string channel length in
  close_in channel;
  let starts = ref [0] in
  String.iteri
    (fun index character ->
      if character = '\n' then starts := (index + 1) :: !starts)
    bytes;
  { label;
    absolute = Unix.realpath path;
    bytes;
    line_starts = Array.of_list (List.rev !starts) }

let source_offset source file line column =
  let absolute =
    if Filename.is_relative file then Unix.realpath file else Unix.realpath file
  in
  if absolute <> source.absolute then
    fail ("user location escapes selected fixture: " ^ file);
  if line < 1 || line > Array.length source.line_starts then
    fail "source line is out of bounds";
  let offset = source.line_starts.(line - 1) + column in
  if offset < 0 || offset > String.length source.bytes then
    fail "source column is out of bounds";
  offset

let source_span source position =
  let file, start_line, start_column, end_line, end_column = Loc.get position in
  tag "SourceSpan"
    [ `String (hex_string source.label);
      `Int (source_offset source file start_line start_column);
      `Int (source_offset source file end_line end_column);
      `Int start_line;
      `Int start_column;
      `Int end_line;
      `Int end_column ]

let source_span_option source = function
  | None -> none
  | Some position -> some (source_span source position)

let attributes attributes =
  attributes
  |> Ident.Sattr.elements
  |> List.map (fun attribute -> hex_string attribute.Ident.attr_string)
  |> List.sort String.compare
  |> List.map (fun value -> `String value)
  |> fun values -> `List values

let user_origin source ident =
  tag "Origin.User"
    [ `String (hex_string ident.Ident.id_string);
      source_span_option source ident.Ident.id_loc;
      attributes ident.Ident.id_attrs ]

let snapshot_origin ident locator =
  tag "Origin.Snapshot"
    [ `String (hex_string ident.Ident.id_string);
      tag "SnapshotSymbolKey"
        [ `String (hex_string locator.owner);
          `Int locator.item;
          `Int locator.inner;
          `String locator.kind;
          `String locator.digest ];
      attributes ident.Ident.id_attrs ]

let generated_source_span_option source = function
  | None -> none
  | Some position ->
      let file, _, _, _, _ = Loc.get position in
      let absolute =
        try
          Some
            (if Filename.is_relative file then Unix.realpath file
             else Unix.realpath file)
        with Unix.Unix_error _ -> None
      in
      begin match absolute with
      | Some absolute when absolute = source.absolute ->
          some (source_span source position)
      | Some _ | None -> none
      end

let generated_origin source stage ident =
  tag "Origin.Generated"
    [ `String stage;
      `String (hex_string ident.Ident.id_string);
      generated_source_span_option source ident.Ident.id_loc;
      attributes ident.Ident.id_attrs ]

type numbering = {
  mutable type_ids : int Ident.Mid.t;
  mutable logic_ids : int Term.Mls.t;
  mutable proposition_ids : int Decl.Mpr.t;
  mutable program_ids : int Ident.Mid.t;
  mutable next_type : int;
  mutable next_logic : int;
  mutable next_proposition : int;
  mutable next_program : int;
}

let new_numbering () =
  { type_ids = Ident.Mid.empty;
    logic_ids = Term.Mls.empty;
    proposition_ids = Decl.Mpr.empty;
    program_ids = Ident.Mid.empty;
    next_type = 0;
    next_logic = 0;
    next_proposition = 0;
    next_program = 0 }

let encounter_type numbering ident =
  match Ident.Mid.find_opt ident numbering.type_ids with
  | Some value -> value
  | None ->
      let value = numbering.next_type in
      numbering.next_type <- value + 1;
      numbering.type_ids <- Ident.Mid.add ident value numbering.type_ids;
      value

let encounter_logic numbering symbol =
  match Term.Mls.find_opt symbol numbering.logic_ids with
  | Some value -> value
  | None ->
      let value = numbering.next_logic in
      numbering.next_logic <- value + 1;
      numbering.logic_ids <- Term.Mls.add symbol value numbering.logic_ids;
      value

let encounter_proposition numbering symbol =
  match Decl.Mpr.find_opt symbol numbering.proposition_ids with
  | Some value -> value
  | None ->
      let value = numbering.next_proposition in
      numbering.next_proposition <- value + 1;
      numbering.proposition_ids <-
        Decl.Mpr.add symbol value numbering.proposition_ids;
      value

let encounter_program numbering ident =
  match Ident.Mid.find_opt ident numbering.program_ids with
  | Some value -> value
  | None ->
      let value = numbering.next_program in
      numbering.next_program <- value + 1;
      numbering.program_ids <- Ident.Mid.add ident value numbering.program_ids;
      value

let type_identity numbering ident =
  `List [`String "type"; `Int (encounter_type numbering ident)]

let logic_identity numbering symbol =
  `List [`String "logic"; `Int (encounter_logic numbering symbol)]

let proposition_identity numbering symbol =
  `List [`String "proposition"; `Int (encounter_proposition numbering symbol)]

let program_identifier_identity numbering ident =
  `List [`String "program"; `Int (encounter_program numbering ident)]

let program_identity numbering symbol =
  program_identifier_identity numbering symbol.Term.vs_name

type state = {
  catalog : catalog;
  source : source;
  numbering : numbering;
  provenance : task_provenance option;
  generated_stage : string option;
  mutable clone_offsets : int StringMap.t Theory.Mtdecl.t;
}

and task_provenance = {
  mutable raw_types : Ident.Sid.t;
  mutable raw_logic : Term.Sls.t;
  mutable raw_propositions : Decl.Spr.t;
  mutable raw_programs : Term.Svs.t;
  mutable generated_types : string Ident.Mid.t;
  mutable generated_logic : string Term.Mls.t;
  mutable generated_propositions : string Decl.Mpr.t;
  mutable generated_programs : string Term.Mvs.t;
  mutable seen_identifiers : Ident.Sid.t;
  mutable identifier_types : Ty.ty Ident.Mid.t;
  mutable raw_identifiers : Ident.Sid.t;
  mutable generated_identifiers : string Ident.Mid.t;
  mutable clone_origins : Ident.ident Ident.Mid.t;
}

let new_task_provenance () =
  { raw_types = Ident.Sid.empty;
    raw_logic = Term.Sls.empty;
    raw_propositions = Decl.Spr.empty;
    raw_programs = Term.Svs.empty;
    generated_types = Ident.Mid.empty;
    generated_logic = Term.Mls.empty;
    generated_propositions = Decl.Mpr.empty;
    generated_programs = Term.Mvs.empty;
    seen_identifiers = Ident.Sid.empty;
    identifier_types = Ident.Mid.empty;
    raw_identifiers = Ident.Sid.empty;
    generated_identifiers = Ident.Mid.empty;
    clone_origins = Ident.Mid.empty }

let new_state ?provenance ?generated_stage catalog source =
  { catalog;
    source;
    numbering = new_numbering ();
    provenance;
    generated_stage;
    clone_offsets = Theory.Mtdecl.empty }

let origin_from_provenance state ident is_raw find_generated add_raw
    add_generated =
  match state.provenance with
  | None -> user_origin state.source ident
  | Some provenance ->
      if is_raw provenance then user_origin state.source ident
      else
        begin match find_generated provenance with
        | Some stage -> generated_origin state.source stage ident
        | None ->
            begin match state.generated_stage with
            | None ->
                add_raw provenance;
                user_origin state.source ident
            | Some stage ->
                add_generated provenance stage;
                generated_origin state.source stage ident
            end
        end

let type_origin state symbol =
  match Ty.Mts.find_opt symbol state.catalog.type_locations with
  | Some locator -> snapshot_origin symbol.Ty.ts_name locator
  | None ->
      origin_from_provenance state symbol.Ty.ts_name
        (fun provenance -> Ident.Sid.mem symbol.Ty.ts_name provenance.raw_types)
        (fun provenance ->
          Ident.Mid.find_opt symbol.Ty.ts_name provenance.generated_types)
        (fun provenance ->
          provenance.raw_types <-
            Ident.Sid.add symbol.Ty.ts_name provenance.raw_types)
        (fun provenance stage ->
          provenance.generated_types <-
            Ident.Mid.add symbol.Ty.ts_name stage provenance.generated_types;
          provenance.generated_identifiers <-
            Ident.Mid.add symbol.Ty.ts_name stage
              provenance.generated_identifiers)

let logic_origin state symbol =
  match Term.Mls.find_opt symbol state.catalog.logic_locations with
  | Some locator -> snapshot_origin symbol.Term.ls_name locator
  | None ->
      origin_from_provenance state symbol.Term.ls_name
        (fun provenance -> Term.Sls.mem symbol provenance.raw_logic)
        (fun provenance -> Term.Mls.find_opt symbol provenance.generated_logic)
        (fun provenance ->
          provenance.raw_logic <- Term.Sls.add symbol provenance.raw_logic)
        (fun provenance stage ->
          provenance.generated_logic <-
            Term.Mls.add symbol stage provenance.generated_logic;
          provenance.generated_identifiers <-
            Ident.Mid.add symbol.Term.ls_name stage
              provenance.generated_identifiers)

let proposition_origin state symbol =
  match Decl.Mpr.find_opt symbol state.catalog.proposition_locations with
  | Some locator -> snapshot_origin symbol.Decl.pr_name locator
  | None ->
      origin_from_provenance state symbol.Decl.pr_name
        (fun provenance ->
          Decl.Spr.mem symbol provenance.raw_propositions)
        (fun provenance ->
          Decl.Mpr.find_opt symbol provenance.generated_propositions)
        (fun provenance ->
          provenance.raw_propositions <-
            Decl.Spr.add symbol provenance.raw_propositions)
        (fun provenance stage ->
          provenance.generated_propositions <-
            Decl.Mpr.add symbol stage provenance.generated_propositions;
          provenance.generated_identifiers <-
            Ident.Mid.add symbol.Decl.pr_name stage
              provenance.generated_identifiers)

let program_origin state symbol =
  origin_from_provenance state symbol.Term.vs_name
    (fun provenance -> Term.Svs.mem symbol provenance.raw_programs)
    (fun provenance ->
      Term.Mvs.find_opt symbol provenance.generated_programs)
    (fun provenance ->
      provenance.raw_programs <- Term.Svs.add symbol provenance.raw_programs;
      provenance.raw_identifiers <-
        Ident.Sid.add symbol.Term.vs_name provenance.raw_identifiers)
    (fun provenance stage ->
      provenance.generated_programs <-
        Term.Mvs.add symbol stage provenance.generated_programs;
      provenance.generated_identifiers <-
        Ident.Mid.add symbol.Term.vs_name stage
          provenance.generated_identifiers)

let sibling_program_locator state locator =
  let id = locator_id locator.owner locator.item locator.inner "program" in
  match StringMap.find_opt id state.catalog.snapshot_digests with
  | Some digest -> { locator with kind = "program"; digest }
  | None -> fail ("snapshot catalog has no locator " ^ id)

let program_type_origin state symbol =
  match Ty.Mts.find_opt symbol.Ity.its_ts state.catalog.type_locations with
  | Some locator ->
      snapshot_origin symbol.Ity.its_ts.Ty.ts_name
        (sibling_program_locator state locator)
  | None -> user_origin state.source symbol.Ity.its_ts.Ty.ts_name

let routine_origin state symbol =
  match symbol.Expr.rs_logic with
  | Expr.RLls logic ->
      begin match Term.Mls.find_opt logic state.catalog.logic_locations with
      | Some locator ->
          snapshot_origin symbol.Expr.rs_name
            (sibling_program_locator state locator)
      | None -> user_origin state.source symbol.Expr.rs_name
      end
  | Expr.RLnone | Expr.RLpv _ | Expr.RLlemma ->
      user_origin state.source symbol.Expr.rs_name

let rec root_identifier provenance identifier =
  match Ident.Mid.find_opt identifier provenance.clone_origins with
  | None -> identifier
  | Some original -> root_identifier provenance original

let observe_identifier_clone provenance original clone =
  provenance.clone_origins <-
    Ident.Mid.add clone original provenance.clone_origins

let track_identifier_provenance state identifier ty =
  match state.provenance with
  | None -> ()
  | Some provenance ->
      if Ident.Sid.mem identifier provenance.seen_identifiers then ()
      else begin
        provenance.seen_identifiers <-
          Ident.Sid.add identifier provenance.seen_identifiers;
        Option.iter
          (fun ty ->
            provenance.identifier_types <-
              Ident.Mid.add identifier ty provenance.identifier_types)
          ty;
        match state.generated_stage with
        | Some "encoding_smt_if_poly:guards" ->
            let rec nearest_ancestor_type candidate =
              match Ident.Mid.find_opt candidate provenance.clone_origins with
              | None -> None
              | Some original ->
                  begin match Ident.Mid.find_opt original
                                provenance.identifier_types with
                  | Some original_ty -> Some original_ty
                  | None -> nearest_ancestor_type original
                  end
            in
            let preserves_type =
              match ty, nearest_ancestor_type identifier with
              | Some current, Some original -> Ty.ty_equal current original
              | _ -> false
            in
            if not preserves_type then
              provenance.generated_identifiers <-
                Ident.Mid.add identifier "encoding_smt_if_poly:guards"
                  provenance.generated_identifiers
        | _ ->
          let identifier = root_identifier provenance identifier in
          if Ident.Sid.mem identifier provenance.raw_identifiers ||
             Ident.Mid.mem identifier provenance.generated_identifiers
          then ()
          else
            begin match state.generated_stage with
            | None ->
                provenance.raw_identifiers <-
                  Ident.Sid.add identifier provenance.raw_identifiers
            | Some stage ->
                provenance.generated_identifiers <-
                  Ident.Mid.add identifier stage
                    provenance.generated_identifiers
            end
      end

let generated_stage_of_identifier provenance ident =
  let rec find identifier =
    match Ident.Mid.find_opt identifier provenance.generated_identifiers with
    | Some stage -> Some stage
    | None ->
        begin match Ident.Mid.find_opt identifier provenance.clone_origins with
        | None -> None
        | Some original -> find original
        end
  in
  find ident

let rec canonical_ty state ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar variable ->
      tag "TyVar" [type_identity state.numbering variable.Ty.tv_name]
  | Ty.Tyapp (symbol, arguments) ->
      let symbol_id = type_identity state.numbering symbol.Ty.ts_name in
      let encoded_arguments = ordered_map (canonical_ty state) arguments in
      tag "TyApp" [symbol_id; `List encoded_arguments]

let canonical_ty_option state = option_json (canonical_ty state)

let canonical_type_definition state = function
  | Ty.NoDef -> tag "TypeDefinition.NoDef" []
  | Ty.Alias ty -> tag "TypeDefinition.Alias" [canonical_ty state ty]
  | Ty.Range range ->
      tag "TypeDefinition.Range"
        [bigint range.Number.ir_lower; bigint range.Number.ir_upper]
  | Ty.Float format ->
      tag "TypeDefinition.Float"
        [ `Int format.Number.fp_exponent_digits;
          `Int format.Number.fp_significand_digits ]

let canonical_type_symbol state symbol =
  let symbol_id = type_identity state.numbering symbol.Ty.ts_name in
  let parameters =
    ordered_map
      (fun variable -> type_identity state.numbering variable.Ty.tv_name)
      symbol.Ty.ts_args
  in
  otag "TypeSymbol"
    [ (fun () -> symbol_id);
      (fun () -> `String (hex_string symbol.Ty.ts_name.Ident.id_string));
      (fun () -> type_origin state symbol);
      (fun () -> `List parameters);
      (fun () -> canonical_type_definition state symbol.Ty.ts_def) ]

let ordered_type_variables types result =
  let seen = ref Ty.Stv.empty in
  let values = ref [] in
  let rec visit ty =
    match ty.Ty.ty_node with
    | Ty.Tyvar variable ->
        if not (Ty.Stv.mem variable !seen) then begin
          seen := Ty.Stv.add variable !seen;
          values := variable :: !values
        end
    | Ty.Tyapp (_, arguments) -> List.iter visit arguments
  in
  List.iter visit types;
  Option.iter visit result;
  List.rev !values

let canonical_lsymbol state symbol =
  let parameters = ordered_type_variables symbol.Term.ls_args symbol.Term.ls_value in
  otag "LSymbol"
    [ (fun () -> logic_identity state.numbering symbol);
      (fun () -> `String (hex_string symbol.Term.ls_name.Ident.id_string));
      (fun () -> logic_origin state symbol);
      (fun () ->
        `List
          (ordered_map
             (fun variable ->
               type_identity state.numbering variable.Ty.tv_name)
             parameters));
      (fun () ->
        `List (ordered_map (canonical_ty state) symbol.Term.ls_args));
      (fun () -> canonical_ty_option state symbol.Term.ls_value) ]

let canonical_prsymbol state symbol =
  otag "PrSymbol"
    [ (fun () -> proposition_identity state.numbering symbol);
      (fun () -> `String (hex_string symbol.Decl.pr_name.Ident.id_string));
      (fun () -> proposition_origin state symbol) ]

let canonical_constant = function
  | Constant.ConstInt literal ->
      let kind =
        match literal.Number.il_kind with
        | Number.ILitUnk -> "ILitUnk"
        | Number.ILitDec -> "ILitDec"
        | Number.ILitHex -> "ILitHex"
        | Number.ILitOct -> "ILitOct"
        | Number.ILitBin -> "ILitBin"
      in
      tag "ConstantInt" [`String kind; bigint literal.Number.il_int]
  | Constant.ConstReal literal ->
      let kind =
        match literal.Number.rl_kind with
        | Number.RLitUnk -> tag "RLitUnk" []
        | Number.RLitDec exponent -> tag "RLitDec" [`Int exponent]
        | Number.RLitHex exponent -> tag "RLitHex" [`Int exponent]
      in
      let real = literal.Number.rl_real in
      tag "ConstantReal"
        [ kind;
          bigint real.Number.rv_sig;
          bigint real.Number.rv_pow2;
          bigint real.Number.rv_pow5 ]
  | Constant.ConstStr value -> tag "ConstantString" [`String (hex_string value)]

let bound_variable_index bound variable =
  let rec search distance = function
    | [] -> None
    | candidate :: rest ->
        if Term.vs_equal candidate variable then Some distance
        else search (distance + 1) rest
  in
  search 0 (List.rev bound)

let canonical_vsymbol state symbol =
  otag "VSymbol"
    [ (fun () -> program_identity state.numbering symbol);
      (fun () -> `String (hex_string symbol.Term.vs_name.Ident.id_string));
      (fun () -> program_origin state symbol);
      (fun () -> canonical_ty state symbol.Term.vs_ty) ]

let canonical_variable_reference state bound variable =
  match bound_variable_index bound variable with
  | Some index -> tag "bound" [`Int index]
  | None -> tag "global" [canonical_vsymbol state variable]

let rec canonical_pattern state pattern =
  match pattern.Term.pat_node with
  | Term.Pwild -> tag "Pwild" [canonical_ty state pattern.Term.pat_ty]
  | Term.Pvar _ -> tag "Pvar" [canonical_ty state pattern.Term.pat_ty]
  | Term.Papp (symbol, arguments) ->
      otag "Papp"
        [ (fun () -> logic_identity state.numbering symbol);
          (fun () ->
            `List (ordered_map (canonical_pattern state) arguments));
          (fun () -> canonical_ty state pattern.Term.pat_ty) ]
  | Term.Por (left, right) ->
      otag "Por"
        [ (fun () -> canonical_pattern state left);
          (fun () -> canonical_pattern state right);
          (fun () -> canonical_ty state pattern.Term.pat_ty) ]
  | Term.Pas (inner, _) ->
      otag "Pas"
        [ (fun () -> canonical_pattern state inner);
          (fun () -> canonical_ty state pattern.Term.pat_ty) ]

let term_instantiation state symbol arguments result =
  let substitution = Term.ls_app_inst symbol arguments result in
  ordered_type_variables symbol.Term.ls_args symbol.Term.ls_value
  |> ordered_map (fun variable ->
         match Ty.Mtv.find_opt variable substitution with
         | None -> None
         | Some ty ->
             let variable_id =
               type_identity state.numbering variable.Ty.tv_name
             in
             let instantiated = canonical_ty state ty in
             Some (`List [variable_id; instantiated]))
  |> List.filter_map Fun.id
  |> fun values -> `List values

let rec canonical_term state bound term =
  let node =
    match term.Term.t_node with
    | Term.Tvar variable ->
        tag "Tvar" [canonical_variable_reference state bound variable]
    | Term.Tconst constant ->
        let ty =
          match term.Term.t_ty with
          | Some ty -> ty
          | None -> fail "typed constant has no result type"
        in
        otag "Tconst"
          [ (fun () -> canonical_constant constant);
            (fun () -> canonical_ty state ty) ]
    | Term.Tapp (symbol, arguments) ->
        otag "Tapp"
          [ (fun () -> logic_identity state.numbering symbol);
            (fun () ->
              term_instantiation state symbol arguments term.Term.t_ty);
            (fun () ->
              `List (ordered_map (canonical_term state bound) arguments));
            (fun () -> canonical_ty_option state term.Term.t_ty) ]
    | Term.Tif (condition, then_branch, else_branch) ->
        otag "Tif"
          [ (fun () -> canonical_term state bound condition);
            (fun () -> canonical_term state bound then_branch);
            (fun () -> canonical_term state bound else_branch);
            (fun () -> canonical_ty_option state term.Term.t_ty) ]
    | Term.Tlet (value, binding) ->
        let variable, body = Term.t_open_bound binding in
        track_identifier_provenance state (Term.t_peek_bound binding)
          (Some variable.Term.vs_ty);
        otag "Tlet"
          [ (fun () -> canonical_term state bound value);
            (fun () -> canonical_ty state variable.Term.vs_ty);
            (fun () -> canonical_term state (bound @ [variable]) body);
            (fun () -> canonical_ty_option state term.Term.t_ty) ]
    | Term.Tcase (scrutinee, branches) ->
        let branches =
          ordered_map
            (fun branch ->
              Ident.Sid.iter
                (fun identifier ->
                  track_identifier_provenance state identifier None)
                (Term.t_peek_branch branch);
              let pattern, body = Term.t_open_branch branch in
              let variables = Term.Svs.elements pattern.Term.pat_vars in
              olist
                [ (fun () -> canonical_pattern state pattern);
                  (fun () ->
                    canonical_term state (bound @ variables) body) ])
            branches
        in
        otag "Tcase"
          [ (fun () -> canonical_term state bound scrutinee);
            (fun () -> `List branches);
            (fun () -> canonical_ty_option state term.Term.t_ty) ]
    | Term.Teps binding ->
        let variable, body = Term.t_open_bound binding in
        track_identifier_provenance state (Term.t_peek_bound binding)
          (Some variable.Term.vs_ty);
        let ty =
          match term.Term.t_ty with
          | Some ty -> ty
          | None -> fail "epsilon has no result type"
        in
        otag "Teps"
          [ (fun () -> canonical_ty state variable.Term.vs_ty);
            (fun () -> canonical_term state (bound @ [variable]) body);
            (fun () -> canonical_ty state ty) ]
    | Term.Tquant (quantifier, quantified) ->
        let variables, triggers, body = Term.t_open_quant quantified in
        List.iter2
          (fun identifier variable ->
            track_identifier_provenance state identifier
              (Some variable.Term.vs_ty))
          (Term.t_peek_quant quantified) variables;
        let nested = bound @ variables in
        let encoded_triggers =
          ordered_map
            (fun group ->
              `List (ordered_map (canonical_term state nested) group))
            triggers
        in
        otag
          (match quantifier with
           | Term.Tforall -> "Tquant.Forall"
           | Term.Texists -> "Tquant.Exists")
          [ (fun () ->
              `List
                (ordered_map
                   (fun variable -> canonical_ty state variable.Term.vs_ty)
                   variables));
            (fun () -> `List encoded_triggers);
            (fun () -> canonical_term state nested body) ]
    | Term.Tbinop (operator, left, right) ->
        otag
          (match operator with
           | Term.Tand -> "Tbinop.And"
           | Term.Tor -> "Tbinop.Or"
           | Term.Timplies -> "Tbinop.Implies"
           | Term.Tiff -> "Tbinop.Iff")
          [ (fun () -> canonical_term state bound left);
            (fun () -> canonical_term state bound right) ]
    | Term.Tnot inner -> tag "Tnot" [canonical_term state bound inner]
    | Term.Ttrue -> tag "Ttrue" []
    | Term.Tfalse -> tag "Tfalse" []
  in
  if Ident.Sattr.is_empty term.Term.t_attrs then node
  else
    tag "TermDecorated"
      [node; none; attributes term.Term.t_attrs]

let canonical_logic_definition state (symbol, definition) =
  let parameters, body = Decl.open_ls_defn definition in
  begin match (Decl.ls_defn_axiom definition).Term.t_node with
  | Term.Tquant (_, quantified) ->
      List.iter2
        (fun identifier parameter ->
          track_identifier_provenance state identifier
            (Some parameter.Term.vs_ty))
        (Term.t_peek_quant quantified) parameters
  | _ -> ()
  end;
  olist
    [ (fun () -> canonical_lsymbol state symbol);
      (fun () ->
        `List
          (ordered_map
             (fun parameter -> canonical_ty state parameter.Term.vs_ty)
             parameters));
      (fun () -> canonical_term state parameters body) ]

let canonical_data_constructor state (symbol, projections) =
  olist
    [ (fun () -> canonical_lsymbol state symbol);
      (fun () ->
        `List
          (ordered_map
             (option_json (canonical_lsymbol state))
             projections)) ]

let canonical_data_declaration state (symbol, constructors) =
  olist
    [ (fun () -> canonical_type_symbol state symbol);
      (fun () ->
        `List (ordered_map (canonical_data_constructor state) constructors)) ]

let canonical_inductive_case state (proposition, formula) =
  olist
    [ (fun () -> canonical_prsymbol state proposition);
      (fun () -> canonical_term state [] formula) ]

let canonical_inductive_declaration state (predicate, cases) =
  olist
    [ (fun () -> canonical_lsymbol state predicate);
      (fun () ->
        `List (ordered_map (canonical_inductive_case state) cases)) ]

type dependency =
  | Type_dependency of Ty.tysymbol
  | Logic_dependency of Term.lsymbol
  | Proposition_dependency of Decl.prsymbol

type dependency_collector = {
  mutable seen_types : unit Ty.Mts.t;
  mutable seen_logic : unit Term.Mls.t;
  mutable seen_propositions : unit Decl.Mpr.t;
  mutable values_reversed : dependency list;
}

let new_dependency_collector () =
  { seen_types = Ty.Mts.empty;
    seen_logic = Term.Mls.empty;
    seen_propositions = Decl.Mpr.empty;
    values_reversed = [] }

let add_type_dependency collector symbol =
  if not (Ty.Mts.mem symbol collector.seen_types) then begin
    collector.seen_types <- Ty.Mts.add symbol () collector.seen_types;
    collector.values_reversed <- Type_dependency symbol :: collector.values_reversed
  end

let add_logic_dependency collector symbol =
  if not (Term.Mls.mem symbol collector.seen_logic) then begin
    collector.seen_logic <- Term.Mls.add symbol () collector.seen_logic;
    collector.values_reversed <- Logic_dependency symbol :: collector.values_reversed
  end

let add_proposition_dependency collector symbol =
  if not (Decl.Mpr.mem symbol collector.seen_propositions) then begin
    collector.seen_propositions <-
      Decl.Mpr.add symbol () collector.seen_propositions;
    collector.values_reversed <-
      Proposition_dependency symbol :: collector.values_reversed
  end

let rec collect_ty_dependencies collector ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar _ -> ()
  | Ty.Tyapp (symbol, arguments) ->
      add_type_dependency collector symbol;
      List.iter (collect_ty_dependencies collector) arguments

let collect_type_definition_dependencies collector symbol =
  match symbol.Ty.ts_def with
  | Ty.Alias ty -> collect_ty_dependencies collector ty
  | Ty.NoDef | Ty.Range _ | Ty.Float _ -> ()

let collect_logic_signature collector symbol =
  List.iter (collect_ty_dependencies collector) symbol.Term.ls_args;
  Option.iter (collect_ty_dependencies collector) symbol.Term.ls_value

let rec collect_pattern_dependencies collector pattern =
  collect_ty_dependencies collector pattern.Term.pat_ty;
  match pattern.Term.pat_node with
  | Term.Pwild | Term.Pvar _ -> ()
  | Term.Papp (symbol, arguments) ->
      add_logic_dependency collector symbol;
      collect_logic_signature collector symbol;
      List.iter (collect_pattern_dependencies collector) arguments
  | Term.Por (left, right) ->
      collect_pattern_dependencies collector left;
      collect_pattern_dependencies collector right
  | Term.Pas (inner, _) -> collect_pattern_dependencies collector inner

let rec collect_term_dependencies collector term =
  Option.iter (collect_ty_dependencies collector) term.Term.t_ty;
  match term.Term.t_node with
  | Term.Tvar variable -> collect_ty_dependencies collector variable.Term.vs_ty
  | Term.Tconst _ | Term.Ttrue | Term.Tfalse -> ()
  | Term.Tapp (symbol, arguments) ->
      add_logic_dependency collector symbol;
      collect_logic_signature collector symbol;
      let substitution = Term.ls_app_inst symbol arguments term.Term.t_ty in
      ordered_type_variables symbol.Term.ls_args symbol.Term.ls_value
      |> List.iter (fun variable ->
             Option.iter (collect_ty_dependencies collector)
               (Ty.Mtv.find_opt variable substitution));
      List.iter (collect_term_dependencies collector) arguments
  | Term.Tif (condition, then_branch, else_branch) ->
      collect_term_dependencies collector condition;
      collect_term_dependencies collector then_branch;
      collect_term_dependencies collector else_branch
  | Term.Tlet (value, binding) ->
      let variable, body = Term.t_open_bound binding in
      collect_ty_dependencies collector variable.Term.vs_ty;
      collect_term_dependencies collector value;
      collect_term_dependencies collector body
  | Term.Tcase (scrutinee, branches) ->
      collect_term_dependencies collector scrutinee;
      List.iter
        (fun branch ->
          let pattern, body = Term.t_open_branch branch in
          collect_pattern_dependencies collector pattern;
          collect_term_dependencies collector body)
        branches
  | Term.Teps binding ->
      let variable, body = Term.t_open_bound binding in
      collect_ty_dependencies collector variable.Term.vs_ty;
      collect_term_dependencies collector body
  | Term.Tquant (_, quantified) ->
      let variables, triggers, body = Term.t_open_quant quantified in
      List.iter
        (fun variable -> collect_ty_dependencies collector variable.Term.vs_ty)
        variables;
      List.iter
        (List.iter (collect_term_dependencies collector))
        triggers;
      collect_term_dependencies collector body
  | Term.Tbinop (_, left, right) ->
      collect_term_dependencies collector left;
      collect_term_dependencies collector right
  | Term.Tnot inner -> collect_term_dependencies collector inner

let introduced_symbols declaration =
  match declaration.Decl.d_node with
  | Decl.Dtype symbol -> [Type_dependency symbol]
  | Decl.Ddata declarations ->
      List.concat_map
        (fun (symbol, constructors) ->
          Type_dependency symbol
          :: List.concat_map
               (fun (constructor, projections) ->
                 Logic_dependency constructor
                 :: List.filter_map
                      (Option.map (fun symbol -> Logic_dependency symbol))
                      projections)
               constructors)
        declarations
  | Decl.Dparam symbol -> [Logic_dependency symbol]
  | Decl.Dlogic definitions ->
      List.map (fun (symbol, _) -> Logic_dependency symbol) definitions
  | Decl.Dind (_, declarations) ->
      List.concat_map
        (fun (predicate, cases) ->
          Logic_dependency predicate
          :: List.map
               (fun (proposition, _) -> Proposition_dependency proposition)
               cases)
        declarations
  | Decl.Dprop (_, proposition, _) -> [Proposition_dependency proposition]

let collect_node_dependencies collector declaration =
  match declaration.Decl.d_node with
  | Decl.Dtype symbol -> collect_type_definition_dependencies collector symbol
  | Decl.Ddata declarations ->
      List.iter
        (fun (_, constructors) ->
          List.iter
            (fun (constructor, projections) ->
              collect_logic_signature collector constructor;
              List.iter
                (Option.iter (collect_logic_signature collector))
                projections)
            constructors)
        declarations
  | Decl.Dparam symbol -> collect_logic_signature collector symbol
  | Decl.Dlogic definitions ->
      List.iter
        (fun (symbol, definition) ->
          collect_logic_signature collector symbol;
          let _, body = Decl.open_ls_defn definition in
          collect_term_dependencies collector body)
        definitions
  | Decl.Dind (_, declarations) ->
      List.iter
        (fun (predicate, cases) ->
          collect_logic_signature collector predicate;
          List.iter
            (fun (_, formula) -> collect_term_dependencies collector formula)
            cases)
        declarations
  | Decl.Dprop (_, _, formula) -> collect_term_dependencies collector formula

let dependency_is_introduced introduced = function
  | Type_dependency symbol ->
      List.exists
        (function Type_dependency value -> Ty.ts_equal symbol value | _ -> false)
        introduced
  | Logic_dependency symbol ->
      List.exists
        (function
          | Logic_dependency value -> Term.ls_equal symbol value
          | _ -> false)
        introduced
  | Proposition_dependency symbol ->
      List.exists
        (function
          | Proposition_dependency value -> Decl.pr_equal symbol value
          | _ -> false)
        introduced

let declaration_dependencies declaration =
  let collector = new_dependency_collector () in
  collect_node_dependencies collector declaration;
  let introduced = introduced_symbols declaration in
  List.rev collector.values_reversed
  |> List.filter (fun dependency ->
         not (dependency_is_introduced introduced dependency))

let canonical_dependency state = function
  | Type_dependency symbol -> canonical_type_symbol state symbol
  | Logic_dependency symbol -> canonical_lsymbol state symbol
  | Proposition_dependency symbol -> canonical_prsymbol state symbol

let declaration_origin state declaration =
  match introduced_symbols declaration with
  | Type_dependency symbol :: _ -> type_origin state symbol
  | Logic_dependency symbol :: _ -> logic_origin state symbol
  | Proposition_dependency symbol :: _ -> proposition_origin state symbol
  | [] -> fail "declaration introduces no symbol"

let canonical_decl_node state declaration =
  match declaration.Decl.d_node with
  | Decl.Dtype symbol -> tag "Dtype" [`List [canonical_type_symbol state symbol]]
  | Decl.Ddata declarations ->
      tag "Ddata"
        [`List (ordered_map (canonical_data_declaration state) declarations)]
  | Decl.Dparam symbol -> tag "Dparam" [canonical_lsymbol state symbol]
  | Decl.Dlogic definitions ->
      tag "Dlogic"
        [`List (ordered_map (canonical_logic_definition state) definitions)]
  | Decl.Dind (Decl.Ind, declarations) ->
      tag "Dind.Ind"
        [`List
          (ordered_map (canonical_inductive_declaration state) declarations)]
  | Decl.Dind (Decl.Coind, _) -> fail "coinductive declaration is outside schema v2"
  | Decl.Dprop (kind, proposition, formula) ->
      otag
        (match kind with
         | Decl.Paxiom -> "Dprop.Paxiom"
         | Decl.Plemma -> "Dprop.Plemma"
         | Decl.Pgoal -> "Dprop.Pgoal")
        [ (fun () -> canonical_prsymbol state proposition);
          (fun () -> canonical_term state [] formula) ]

let canonical_decl state declaration =
  otag "Decl"
    [ (fun () -> declaration_origin state declaration);
      (fun () ->
        `List
          (ordered_map
             (canonical_dependency state)
             (declaration_dependencies declaration)));
      (fun () -> canonical_decl_node state declaration) ]

let canonical_theory_key theory =
  tag "TheoryKey"
    [ `List
        (List.map
           (fun segment -> `String (hex_string segment))
           theory.Theory.th_path);
      `String (hex_string theory.Theory.th_name.Ident.id_string) ]

let canonical_theory_key_parts path name =
  tag "TheoryKey"
    [ `List (List.map (fun segment -> `String (hex_string segment)) path);
      `String (hex_string name) ]

let canonical_semantic_name source ident = user_origin source ident

let canonical_meta_argument state = function
  | Theory.MAty ty -> tag "MetaArgument.Type" [canonical_ty state ty]
  | Theory.MAts symbol ->
      tag "MetaArgument.TypeSymbol"
        [type_identity state.numbering symbol.Ty.ts_name]
  | Theory.MAls symbol ->
      tag "MetaArgument.LogicSymbol"
        [logic_identity state.numbering symbol]
  | Theory.MApr symbol ->
      tag "MetaArgument.PropositionSymbol"
        [proposition_identity state.numbering symbol]
  | Theory.MAstr value ->
      tag "MetaArgument.String" [`String (hex_string value)]
  | Theory.MAint value -> tag "MetaArgument.Integer" [`Int value]
  | Theory.MAid ident ->
      tag "MetaArgument.Identifier"
        [canonical_semantic_name state.source ident]

let canonical_meta state meta arguments =
  otag "Meta"
    [ (fun () -> `String (hex_string meta.Theory.meta_name));
      (fun () ->
        `List (ordered_map (canonical_meta_argument state) arguments)) ]

let type_locator state symbol =
  match Ty.Mts.find_opt symbol state.catalog.type_locations with
  | Some locator -> locator
  | None -> fail ("clone references uncatalogued type " ^ symbol.Ty.ts_name.id_string)

let logic_locator state symbol =
  match Term.Mls.find_opt symbol state.catalog.logic_locations with
  | Some locator -> locator
  | None -> fail ("clone references uncatalogued logic " ^ symbol.Term.ls_name.id_string)

let proposition_locator state symbol =
  match Decl.Mpr.find_opt symbol state.catalog.proposition_locations with
  | Some locator -> locator
  | None ->
      fail
        ("clone references uncatalogued proposition "
         ^ symbol.Decl.pr_name.id_string)

let locator_sort_key locator =
  locator_id locator.owner locator.item locator.inner locator.kind

let sort_by_locator locate entries =
  List.sort
    (fun (left, _) (right, _) ->
      String.compare (locator_sort_key (locate left))
        (locator_sort_key (locate right)))
    entries

let canonical_clone_type_instantiations state map =
  let types =
    sort_by_locator (type_locator state) (Ty.Mts.bindings map.Theory.sm_ty)
    |> ordered_map (fun (source, target) ->
           let source_id =
             type_identity state.numbering source.Ty.ts_name
           in
           let target = tag "Clone.Type" [canonical_ty state target] in
           (source_id, target))
  in
  let symbols =
    sort_by_locator (type_locator state) (Ty.Mts.bindings map.Theory.sm_ts)
    |> ordered_map (fun (source, target) ->
           let source_id =
             type_identity state.numbering source.Ty.ts_name
           in
           let target =
             tag "Clone.TypeSymbol"
               [type_identity state.numbering target.Ty.ts_name]
           in
           (source_id, target))
  in
  semantic_map (types @ symbols)

let canonical_clone_logic_instantiations state map =
  sort_by_locator (logic_locator state) (Term.Mls.bindings map.Theory.sm_ls)
  |> ordered_map (fun (source, target) ->
         let source_id = logic_identity state.numbering source in
         let target_id = logic_identity state.numbering target in
         (source_id, target_id))
  |> semantic_map

let canonical_clone_proposition_instantiations state map =
  sort_by_locator (proposition_locator state)
    (Decl.Mpr.bindings map.Theory.sm_pr)
  |> ordered_map (fun (source, target) ->
         let source_id = proposition_identity state.numbering source in
         let target_id = proposition_identity state.numbering target in
         (source_id, target_id))
  |> semantic_map

let canonical_clone_witness state source ordinal map =
  otag "CloneWitness"
    [ (fun () -> canonical_theory_key source);
      (fun () -> `Int ordinal);
      (fun () -> canonical_clone_type_instantiations state map);
      (fun () -> canonical_clone_logic_instantiations state map);
      (fun () -> canonical_clone_proposition_instantiations state map) ]

let rec canonical_namespace state namespace =
  let bytes_key name = `String (hex_string name) in
  otag "Namespace"
    [ (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ts
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value =
                    type_identity state.numbering symbol.Ty.ts_name
                  in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ls
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value = logic_identity state.numbering symbol in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_pr
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value = proposition_identity state.numbering symbol in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ns
           |> ordered_map (fun (name, nested) ->
                  let key = bytes_key name in
                  let value = canonical_namespace state nested in
                  (key, value)))) ]

let canonical_theory_item state ordinal tdecl =
  match tdecl.Theory.td_node with
  | Theory.Decl declaration ->
      tag "TheoryItem.Decl" [canonical_decl state declaration]
  | Theory.Use source -> tag "TheoryItem.Use" [canonical_theory_key source]
  | Theory.Clone (source, map) ->
      tag "TheoryItem.Clone"
        [canonical_clone_witness state source ordinal map]
  | Theory.Meta (meta, arguments) ->
      tag "TheoryItem.Meta" [canonical_meta state meta arguments]

let canonical_theory_with_state state theory =
  otag "Theory"
    [ (fun () -> canonical_theory_key theory);
      (fun () -> canonical_semantic_name state.source theory.Theory.th_name);
      (fun () ->
        `List
          (ordered_mapi
             (canonical_theory_item state)
             theory.Theory.th_decls));
      (fun () -> canonical_namespace state theory.Theory.th_export) ]

let canonical_theory catalog source theory =
  canonical_theory_with_state (new_state catalog source) theory

let rec canonical_program_pure_namespace state excluded namespace =
  let bytes_key name = `String (hex_string name) in
  otag "Namespace"
    [ (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ts
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value =
                    type_identity state.numbering symbol.Ty.ts_name
                  in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ls
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value = logic_identity state.numbering symbol in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_pr
           |> List.filter (fun (_, symbol) ->
                  not (Decl.Spr.mem symbol excluded))
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value = proposition_identity state.numbering symbol in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ns
           |> ordered_map (fun (name, nested) ->
                  let key = bytes_key name in
                  let value =
                    canonical_program_pure_namespace state excluded nested
                  in
                  (key, value)))) ]

let canonical_program_pure_theory state theory namespace =
  let excluded =
    List.fold_left
      (fun excluded declaration ->
        match declaration.Theory.td_node with
        | Theory.Decl
            { Decl.d_node = Decl.Dprop (Decl.Pgoal, proposition, _); _ } ->
            Decl.Spr.add proposition excluded
        | Theory.Decl _ | Theory.Use _ | Theory.Clone _ | Theory.Meta _ ->
            excluded)
      Decl.Spr.empty theory.Theory.th_decls
  in
  let declarations =
    List.filter
      (fun declaration ->
        match declaration.Theory.td_node with
        | Theory.Decl
            { Decl.d_node = Decl.Dprop (Decl.Pgoal, proposition, _); _ } ->
            not (Decl.Spr.mem proposition excluded)
        | Theory.Decl _ | Theory.Use _ | Theory.Clone _ | Theory.Meta _ -> true)
      theory.Theory.th_decls
  in
  otag "Theory"
    [ (fun () -> canonical_theory_key theory);
      (fun () -> canonical_semantic_name state.source theory.Theory.th_name);
      (fun () ->
        `List (ordered_mapi (canonical_theory_item state) declarations));
      (fun () ->
        canonical_program_pure_namespace state excluded
          namespace) ]

let rec canonical_ity state ity =
  match ity.Ity.ity_node with
  | Ity.Ityvar variable ->
      tag "ItyVar" [type_identity state.numbering variable.Ty.tv_name]
  | Ity.Ityapp (symbol, arguments, regions) ->
      if regions <> [] then fail "program MVP contains an Ity region";
      otag "ItyApp"
        [ (fun () ->
            program_identifier_identity state.numbering
              symbol.Ity.its_ts.Ty.ts_name);
          (fun () ->
            `List (ordered_map (canonical_ity state) arguments));
          (fun () -> `List []);
          (fun () -> canonical_ty state (Ity.ty_of_ity ity)) ]
  | Ity.Ityreg _ -> fail "program MVP contains a region type"

let canonical_program_type_argument_flag flag =
  `List
    [ `Bool flag.Ity.its_frozen;
      `Bool flag.Ity.its_exposed;
      `Bool flag.Ity.its_liable;
      `Bool flag.Ity.its_fixed;
      `Bool flag.Ity.its_visible ]

let canonical_program_type_flags symbol =
  `List
    [ `Bool symbol.Ity.its_nonfree;
      `Bool symbol.Ity.its_private;
      `Bool symbol.Ity.its_mutable;
      `Bool symbol.Ity.its_fragile;
      `List
        (ordered_map canonical_program_type_argument_flag
           symbol.Ity.its_arg_flg);
      `List
        (ordered_map canonical_program_type_argument_flag
           symbol.Ity.its_reg_flg) ]

let canonical_program_type_definition state symbol =
  match symbol.Ity.its_def with
  | Ty.NoDef -> tag "TypeDefinition.NoDef" []
  | Ty.Alias target ->
      tag "TypeDefinition.Alias" [canonical_ity state target]
  | Ty.Range range ->
      tag "TypeDefinition.Range"
        [bigint range.Number.ir_lower; bigint range.Number.ir_upper]
  | Ty.Float format ->
      tag "TypeDefinition.Float"
        [ `Int format.Number.fp_exponent_digits;
          `Int format.Number.fp_significand_digits ]

let canonical_program_type_symbol state symbol =
  otag "ProgramTypeSymbol"
    [ (fun () ->
        program_identifier_identity state.numbering
          symbol.Ity.its_ts.Ty.ts_name);
      (fun () ->
        type_identity state.numbering symbol.Ity.its_ts.Ty.ts_name);
      (fun () -> program_type_origin state symbol);
      (fun () -> canonical_program_type_flags symbol);
      (fun () -> canonical_program_type_definition state symbol) ]

let canonical_program_binder state variable =
  `List
    [ canonical_ity state variable.Ity.pv_ity;
      `Bool variable.Ity.pv_ghost ]

let canonical_program_mask = function
  | Ity.MaskVisible -> `String "Visible"
  | Ity.MaskGhost -> `String "Ghost"
  | Ity.MaskTuple _ -> fail "program MVP contains a tuple mask"

let canonical_effect state effect =
  if not (Ity.Mreg.is_empty effect.Ity.eff_writes)
     || not (Ity.Sreg.is_empty effect.Ity.eff_taints)
     || not (Ity.Sreg.is_empty effect.Ity.eff_covers)
     || not (Ity.Sreg.is_empty effect.Ity.eff_resets)
     || not (Ity.Sxs.is_empty effect.Ity.eff_raises)
     || not (Ty.Stv.is_empty effect.Ity.eff_spoils)
  then fail "program MVP contains a non-read effect";
  let termination =
    match effect.Ity.eff_oneway with
    | Ity.Total -> "Total"
    | Ity.Partial -> fail "program MVP contains a partial effect"
    | Ity.Diverges -> fail "program MVP contains a diverging effect"
  in
  otag "Effect"
    [ (fun () ->
        `List
          (ordered_map
             (fun variable ->
               program_identifier_identity state.numbering
                 variable.Ity.pv_vs.Term.vs_name)
             (Ity.Spv.elements effect.Ity.eff_reads)));
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> `String termination);
      (fun () -> `Bool effect.Ity.eff_ghost) ]

let cty_program_variables cty =
  let seen = ref Ity.Mpv.empty in
  let reversed = ref [] in
  let add variable =
    if not (Ity.Mpv.mem variable !seen) then begin
      seen := Ity.Mpv.add variable () !seen;
      reversed := variable :: !reversed
    end
  in
  List.iter add cty.Ity.cty_args;
  List.iter add (Ity.Spv.elements cty.Ity.cty_effect.Ity.eff_reads);
  List.iter
    (fun (snapshot, original) -> add snapshot; add original)
    (Ity.Mpv.bindings cty.Ity.cty_oldies);
  List.rev !reversed

let canonical_cty state cty =
  if not (Ity.Mxs.is_empty cty.Ity.cty_xpost)
     || not (Ity.Mpv.is_empty cty.Ity.cty_oldies)
     || not (Ty.Mtv.is_empty cty.Ity.cty_freeze.Ity.isb_var)
     || not (Ity.Mreg.is_empty cty.Ity.cty_freeze.Ity.isb_reg)
  then fail "program MVP contains unsupported Cty state";
  let variables = cty_program_variables cty in
  let term_bound = List.map (fun variable -> variable.Ity.pv_vs) variables in
  let postconditions =
    ordered_map
      (fun post ->
        let result, formula = Ity.open_post post in
        olist
          [ (fun () -> canonical_ty state result.Term.vs_ty);
            (fun () ->
              canonical_term state (term_bound @ [result]) formula) ])
      cty.Ity.cty_post
  in
  otag "Cty"
    [ (fun () ->
        `List
          (ordered_map (canonical_program_binder state) cty.Ity.cty_args));
      (fun () ->
        `List
          (ordered_map (canonical_term state term_bound) cty.Ity.cty_pre));
      (fun () ->
        `List postconditions);
      (fun () -> `List []);
      (fun () -> `List []);
      (fun () -> canonical_effect state cty.Ity.cty_effect);
      (fun () -> canonical_ity state cty.Ity.cty_result);
      (fun () -> canonical_program_mask cty.Ity.cty_mask);
      (fun () -> `List []) ]

let canonical_routine_logic state = function
  | Expr.RLnone -> none
  | Expr.RLls symbol -> some (logic_identity state.numbering symbol)
  | Expr.RLpv _ -> fail "program MVP contains an RLpv routine"
  | Expr.RLlemma -> fail "program MVP contains an RLlemma routine"

let canonical_program_variable_option state = function
  | None -> none
  | Some variable ->
      some
        (program_identifier_identity state.numbering
           variable.Ity.pv_vs.Term.vs_name)

let canonical_routine_symbol state symbol =
  otag "RoutineSymbol"
    [ (fun () ->
        program_identifier_identity state.numbering
          symbol.Expr.rs_name);
      (fun () ->
        `String (hex_string symbol.Expr.rs_name.Ident.id_string));
      (fun () -> routine_origin state symbol);
      (fun () -> canonical_cty state symbol.Expr.rs_cty);
      (fun () -> canonical_routine_logic state symbol.Expr.rs_logic);
      (fun () -> canonical_program_variable_option state symbol.Expr.rs_field) ]

let bound_program_variable_index bound variable =
  let rec search distance = function
    | [] -> None
    | candidate :: rest ->
        if Ity.pv_equal candidate variable then Some distance
        else search (distance + 1) rest
  in
  search 0 (List.rev bound)

let canonical_program_variable_reference state bound variable =
  match bound_program_variable_index bound variable with
  | Some index -> tag "bound" [`Int index]
  | None ->
      tag "global"
        [program_identifier_identity state.numbering
           variable.Ity.pv_vs.Term.vs_name]

let expression_user_origin state expression =
  tag "Origin.User"
    [ `String "";
      source_span_option state.source expression.Expr.e_loc;
      `List [] ]

let rec canonical_expr state bound expression =
  let ity () = canonical_ity state expression.Expr.e_ity in
  let node =
    match expression.Expr.e_node with
    | Expr.Evar variable ->
        otag "Evar"
          [ (fun () ->
              canonical_program_variable_reference state bound variable);
            ity ]
    | Expr.Econst constant ->
        otag "Econst"
          [ (fun () -> canonical_constant constant); ity ]
    | Expr.Eexec (computation, _) ->
        begin match computation.Expr.c_node with
        | Expr.Capp (symbol, arguments) ->
            otag "EroutineCall"
              [ (fun () ->
                  program_identifier_identity state.numbering
                    symbol.Expr.rs_name);
                (fun () ->
                  `List
                    (ordered_map
                       (canonical_program_variable_reference state bound)
                       arguments));
                ity ]
        | Expr.Cpur (symbol, arguments) ->
            otag "EpureApp"
              [ (fun () -> logic_identity state.numbering symbol);
                (fun () ->
                  `List
                    (ordered_map
                       (canonical_program_variable_reference state bound)
                       arguments));
                ity ]
        | Expr.Cfun _ | Expr.Cany ->
            fail "program MVP contains a nested computation expression"
        end
    | Expr.Elet (definition, body) ->
        begin match definition with
        | Expr.LDvar (binder, value) ->
            otag "Elet"
              [ (fun () -> canonical_program_binder state binder);
                (fun () -> canonical_expr state bound value);
                (fun () -> canonical_expr state (bound @ [binder]) body);
                ity ]
        | Expr.LDsym _ | Expr.LDrec _ ->
            fail "program MVP contains a local routine definition"
        end
    | Expr.Eif (condition, consequent, alternative) ->
        otag "Eif"
          [ (fun () -> canonical_expr state bound condition);
            (fun () -> canonical_expr state bound consequent);
            (fun () -> canonical_expr state bound alternative);
            ity ]
    | Expr.Eassert (Expr.Assert, formula) ->
        tag "Eassert"
          [canonical_term state
             (List.map (fun variable -> variable.Ity.pv_vs) bound)
             formula]
    | Expr.Eassert (Expr.Assume, formula) ->
        tag "Eassume"
          [canonical_term state
             (List.map (fun variable -> variable.Ity.pv_vs) bound)
             formula]
    | Expr.Eassert (Expr.Check, _) ->
        fail "program MVP contains a check assertion"
    | Expr.Eassign _ | Expr.Ematch _ | Expr.Ewhile _ | Expr.Efor _
    | Expr.Eraise _ | Expr.Eexn _ | Expr.Eghost _ | Expr.Epure _
    | Expr.Eabsurd ->
        fail "program MVP contains an unsupported expression"
  in
  otag "ExprDecorated"
    [ (fun () -> node);
      (fun () -> expression_user_origin state expression);
      (fun () -> attributes expression.Expr.e_attrs);
      (fun () -> canonical_effect state expression.Expr.e_effect);
      (fun () -> canonical_program_mask expression.Expr.e_mask) ]

let canonical_program_type_declaration state definition =
  `List
    [ canonical_program_type_symbol state definition.Pdecl.itd_its;
      `List
        (ordered_map
           (fun field ->
             program_identifier_identity state.numbering field.Expr.rs_name)
           definition.Pdecl.itd_fields);
      `List
        (ordered_map
           (fun constructor ->
             program_identifier_identity state.numbering
               constructor.Expr.rs_name)
           definition.Pdecl.itd_constructors);
      `List
        (ordered_map (canonical_term state []) definition.Pdecl.itd_invariant) ]

let canonical_program_declaration state declaration =
  if declaration.Pdecl.pd_meta <> [] then
    fail "program MVP contains declaration-local metas";
  let pure =
    `List
      (ordered_map (canonical_decl state) declaration.Pdecl.pd_pure)
  in
  let node =
    match declaration.Pdecl.pd_node with
    | Pdecl.PDtype definitions ->
        tag "Pdecl.PDtype"
          [`List
            (ordered_map
               (canonical_program_type_declaration state)
               definitions)]
    | Pdecl.PDpure -> tag "Pdecl.PDpure" []
    | Pdecl.PDlet (Expr.LDsym (symbol, computation)) ->
        let kind, projection =
          match computation.Expr.c_node with
          | Expr.Cany -> ("Cany", canonical_cty state computation.Expr.c_cty)
          | Expr.Cfun body ->
              let bound = cty_program_variables computation.Expr.c_cty in
              ( "Cfun",
                otag "CfunProjection"
                  [ (fun () -> canonical_cty state computation.Expr.c_cty);
                    (fun () -> canonical_expr state bound body) ] )
          | Expr.Capp _ | Expr.Cpur _ ->
              fail "top-level program declaration is not Cany/Cfun"
        in
        otag "Pdecl.PDlet"
          [ (fun () -> canonical_routine_symbol state symbol);
            (fun () -> `String kind);
            (fun () -> projection) ]
    | Pdecl.PDlet (Expr.LDvar _) | Pdecl.PDlet (Expr.LDrec _) ->
        fail "program MVP contains a non-routine top-level let"
    | Pdecl.PDexn _ -> fail "program MVP contains an exception declaration"
  in
  otag "Pdecl"
    [ (fun () -> none);
      (fun () -> pure);
      (fun () -> `List []);
      (fun () -> node) ]

let canonical_pmodule_key pmodule =
  let theory = pmodule.Pmodule.mod_theory in
  tag "PmoduleKey"
    [ `List
        (List.map
           (fun segment -> `String (hex_string segment))
           theory.Theory.th_path);
      `String (hex_string theory.Theory.th_name.Ident.id_string) ]

let canonical_module_items state units =
  let reversed = ref [] in
  let append value = reversed := value :: !reversed in
  let rec visit = function
    | Pmodule.Udecl declaration ->
        begin match declaration.Pdecl.pd_node with
        | Pdecl.PDpure ->
            (* Why3 eagerly inserts generated VC declarations next to a
               typed routine.  Stage 10 compares the pre-WP program IR; those
               goals enter the separate Stage 11 VC differential instead. *)
            ()
        | _ ->
            append
              (tag "PmoduleItem.ProgramDecl"
                 [canonical_program_declaration state declaration])
        end
    | Pmodule.Uuse source ->
        append (tag "PmoduleItem.Use" [canonical_pmodule_key source])
    | Pmodule.Uclone _ -> fail "program MVP contains a module clone"
    | Pmodule.Umeta (meta, arguments) ->
        append
          (tag "PmoduleItem.Meta"
             [canonical_meta state meta arguments])
    | Pmodule.Uscope (_, nested) -> List.iter visit nested
  in
  List.iter visit units;
  `List (List.rev !reversed)

let rec canonical_program_namespace state namespace =
  if not (Wstdlib.Mstr.is_empty namespace.Pmodule.ns_xs) then
    fail "program MVP contains an exception namespace entry";
  let bytes_key name = `String (hex_string name) in
  let program_symbol = function
    | Pmodule.RS symbol ->
        program_identifier_identity state.numbering symbol.Expr.rs_name
    | Pmodule.PV variable ->
        program_identifier_identity state.numbering
          variable.Ity.pv_vs.Term.vs_name
    | Pmodule.OO _ -> fail "program MVP contains an overload set"
  in
  otag "ProgramNamespace"
    [ (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ts
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value =
                    program_identifier_identity state.numbering
                      symbol.Ity.its_ts.Ty.ts_name
                  in
                  (key, value))));
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ps
           |> ordered_map (fun (name, symbol) ->
                  let key = bytes_key name in
                  let value = program_symbol symbol in
                  (key, value))));
      (fun () -> `List []);
      (fun () ->
        semantic_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ns
           |> ordered_map (fun (name, nested) ->
                  let key = bytes_key name in
                  let value = canonical_program_namespace state nested in
                  (key, value)))) ]

let canonical_pmodule catalog source pmodule =
  let state = new_state catalog source in
  (* MoonBit builds the flattened item array before assembling the outer
     Pmodule value, so first-encounter identities from declarations precede
     identities reached through the pure/export namespaces. *)
  let items = canonical_module_items state pmodule.Pmodule.mod_units in
  otag "Pmodule"
    [ (fun () -> canonical_pmodule_key pmodule);
      (fun () ->
        canonical_program_pure_theory state pmodule.Pmodule.mod_theory
          pmodule.Pmodule.mod_theory.Theory.th_export);
      (fun () -> items);
      (fun () ->
        canonical_program_namespace state pmodule.Pmodule.mod_export) ]

let add_type_target_owner catalog owners symbol =
  match Ty.Mts.find_opt symbol catalog.type_locations with
  | Some locator -> StringSet.add locator.owner owners
  | None -> owners

let rec add_ty_target_owners catalog owners ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar _ -> owners
  | Ty.Tyapp (symbol, arguments) ->
      List.fold_left (add_ty_target_owners catalog)
        (add_type_target_owner catalog owners symbol) arguments

let clone_target_owners state map =
  let owners =
    Ty.Mts.bindings map.Theory.sm_ty
    |> List.fold_left
         (fun owners (_, target) ->
           add_ty_target_owners state.catalog owners target)
         StringSet.empty
  in
  let owners =
    Ty.Mts.bindings map.Theory.sm_ts
    |> List.fold_left
         (fun owners (_, target) ->
           add_type_target_owner state.catalog owners target)
         owners
  in
  let owners =
    Term.Mls.bindings map.Theory.sm_ls
    |> List.fold_left
         (fun owners (_, target) ->
           match Term.Mls.find_opt target state.catalog.logic_locations with
           | Some locator -> StringSet.add locator.owner owners
           | None -> owners)
         owners
  in
  Decl.Mpr.bindings map.Theory.sm_pr
  |> List.fold_left
       (fun owners (_, target) ->
         match Decl.Mpr.find_opt target state.catalog.proposition_locations with
         | Some locator -> StringSet.add locator.owner owners
         | None -> owners)
       owners

let task_tdecl_ordinal state tdecl map =
  let occurrences =
    match Theory.Mtdecl.find_opt tdecl state.catalog.tdecl_occurrences with
    | Some occurrences -> occurrences
    | None -> fail "task clone marker has no frozen-theory occurrence"
  in
  let target_owners = clone_target_owners state map in
  let matching =
    List.filter
      (fun (owner, _) -> StringSet.mem owner target_owners)
      occurrences
  in
  let matching = if matching = [] then occurrences else matching in
  let owners =
    List.fold_left
      (fun owners (owner, _) -> StringSet.add owner owners)
      StringSet.empty matching
  in
  if StringSet.cardinal owners <> 1 then
    fail "task clone marker has ambiguous frozen-theory provenance";
  let owner = StringSet.choose owners in
  let ordinals =
    matching
    |> List.filter_map (fun (candidate, ordinal) ->
           if candidate = owner then Some ordinal else None)
    |> List.sort_uniq Int.compare
  in
  let offsets =
    Option.value ~default:StringMap.empty
      (Theory.Mtdecl.find_opt tdecl state.clone_offsets)
  in
  let offset = Option.value ~default:0 (StringMap.find_opt owner offsets) in
  let ordinal =
    match List.nth_opt ordinals offset with
    | Some ordinal -> ordinal
    | None -> fail "task clone occurrence exceeds frozen-theory history"
  in
  state.clone_offsets <-
    Theory.Mtdecl.add tdecl (StringMap.add owner (offset + 1) offsets)
      state.clone_offsets;
  ordinal

let canonical_task_item state tdecl =
  match tdecl.Theory.td_node with
  | Theory.Decl declaration ->
      tag "TaskItem.Decl" [canonical_decl state declaration]
  | Theory.Use source -> tag "TaskItem.Use" [canonical_theory_key source]
  | Theory.Clone (source, map) ->
      tag "TaskItem.Clone"
        [ canonical_clone_witness state source
            (task_tdecl_ordinal state tdecl map) map ]
  | Theory.Meta (meta, arguments) ->
      tag "TaskItem.Meta" [canonical_meta state meta arguments]

let canonical_task_with_state state task =
  tag "Task"
    [`List
      (ordered_map (canonical_task_item state) (Task.task_tdecls task))]

let canonical_task catalog source task =
  canonical_task_with_state (new_state catalog source) task

let task_trace_provenance catalog source task =
  let provenance = new_task_provenance () in
  let state = new_state ~provenance catalog source in
  ignore (canonical_task_with_state state task);
  provenance

let canonical_checkpoint_task catalog source provenance stage task =
  canonical_task_with_state
    (new_state ~provenance ~generated_stage:stage catalog source)
    task

type smt_token_kind =
  | Smt_left_parenthesis
  | Smt_right_parenthesis
  | Smt_atom
  | Smt_quoted_symbol
  | Smt_string_literal

type smt_token = {
  smt_kind : smt_token_kind;
  smt_bytes : string;
}

type smt_identifier_event = {
  marker_token : string;
  original_token : string;
  identifier : Ident.ident;
}

let smt_identifier_event ordinal identifier original_token =
  let marker_token = Printf.sprintf "|@why3-oracle-id-%d|" ordinal in
  ({ marker_token; original_token; identifier }, marker_token)

let smt_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let smt_atom_delimiter = function
  | '(' | ')' | ';' -> true
  | character -> smt_space character

let smt_lex_quoted input start =
  let length = String.length input in
  let rec loop index =
    if index >= length then fail "unterminated SMT-LIB quoted symbol";
    match input.[index] with
    | '|' -> index + 1
    | '\\' | '\000' | '\r' | '\n' ->
        fail "invalid character in SMT-LIB quoted symbol"
    | _ -> loop (index + 1)
  in
  loop (start + 1)

let smt_lex_string input start =
  let length = String.length input in
  let rec loop index =
    if index >= length then fail "unterminated SMT-LIB string";
    match input.[index] with
    | '\000' -> fail "NUL is not valid in an SMT-LIB string"
    | '"' when index + 1 < length && input.[index + 1] = '"' ->
        loop (index + 2)
    | '"' -> index + 1
    | _ -> loop (index + 1)
  in
  loop (start + 1)

let lex_smt_tokens input =
  let length = String.length input in
  let rec skip_comment index =
    if index < length && input.[index] <> '\n' then skip_comment (index + 1)
    else index
  in
  let rec atom_end index =
    if index < length && not (smt_atom_delimiter input.[index]) then begin
      if input.[index] = '\000' then fail "NUL is not valid in an SMT token";
      atom_end (index + 1)
    end else
      index
  in
  let rec loop index reversed =
    if index >= length then List.rev reversed
    else if smt_space input.[index] then loop (index + 1) reversed
    else if input.[index] = ';' then loop (skip_comment index) reversed
    else
      let kind, finish =
        match input.[index] with
        | '(' -> (Smt_left_parenthesis, index + 1)
        | ')' -> (Smt_right_parenthesis, index + 1)
        | '|' -> (Smt_quoted_symbol, smt_lex_quoted input index)
        | '"' -> (Smt_string_literal, smt_lex_string input index)
        | _ -> (Smt_atom, atom_end index)
      in
      if finish = index then fail "empty SMT token";
      let token =
        { smt_kind = kind;
          smt_bytes = String.sub input index (finish - index) }
      in
      loop finish (token :: reversed)
  in
  loop 0 []

let generated_ordinal generated stage identifier =
  let identifiers =
    Option.value ~default:Ident.Mid.empty (StringMap.find_opt stage !generated)
  in
  match Ident.Mid.find_opt identifier identifiers with
  | Some ordinal -> ordinal
  | None ->
      let ordinal = Ident.Mid.cardinal identifiers in
      generated :=
        StringMap.add stage (Ident.Mid.add identifier ordinal identifiers)
          !generated;
      ordinal

let canonical_smt_token_stream provenance events output =
  let event_map =
    List.fold_left
      (fun entries event ->
        if StringMap.mem event.marker_token entries then
          fail "duplicate SMT identifier marker";
        StringMap.add event.marker_token event entries)
      StringMap.empty events
  in
  let matched = ref StringSet.empty in
  let generated = ref StringMap.empty in
  let normalize token =
    match StringMap.find_opt token.smt_bytes event_map with
    | None -> token.smt_bytes
    | Some event ->
        if token.smt_kind <> Smt_quoted_symbol then
          fail "SMT identifier marker is not one quoted token";
        matched := StringSet.add event.marker_token !matched;
        begin match generated_stage_of_identifier provenance event.identifier with
        | None -> event.original_token
        | Some stage ->
            Printf.sprintf "$generated[%s][%d]" stage
              (generated_ordinal generated stage event.identifier)
        end
  in
  let tokens = List.map normalize (lex_smt_tokens output) in
  if StringSet.cardinal !matched <> List.length events then
    fail "not every SMT identifier marker reached the token stream";
  tag "SmtTokenStreamV1"
    [`List (List.map (fun token -> `String (hex_string token)) tokens)]

let semantic_profile_sha256 =
  "f788bd465967b186e1db9f910b8e04e3f4803413a705b661bafc2da5d07658ab"

let canonical_bytes value = compact value ^ "\n"
let source_sha256 source = sha256_string source.bytes

let portable_record source fields canonical =
  let canonical_text = canonical_bytes canonical in
  `Assoc
    ([ ("schema", `Int 2);
       ("semantic_profile_sha256", `String semantic_profile_sha256);
       ("fixture", `String source.label);
       ("source_sha256", `String (source_sha256 source)) ]
     @ fields
     @ [ ("canonical_sha256", `String (sha256_string canonical_text));
         ("canonical", canonical) ])

let typed_theory_record catalog source theory =
  let canonical = canonical_theory catalog source theory in
  portable_record source
    [ ("scope", `String "unit");
      ("unit_kind", `String "theory");
      ("unit_name_hex", `String (hex_string theory.Theory.th_name.id_string));
      ("stage", `String "typed-semantic") ]
    canonical

let typed_module_record catalog source pmodule =
  let theory = pmodule.Pmodule.mod_theory in
  let canonical = canonical_pmodule catalog source pmodule in
  portable_record source
    [ ("scope", `String "unit");
      ("unit_kind", `String "module");
      ("unit_name_hex", `String (hex_string theory.Theory.th_name.id_string));
      ("stage", `String "typed-program") ]
    canonical

let task_record source unit_name goal_name ordinal stage canonical =
  portable_record source
    [ ("scope", `String "goal");
      ("unit_kind", `String "theory");
      ("unit_name_hex", `String (hex_string unit_name));
      ("goal_name_hex", `String (hex_string goal_name));
      ("goal_ordinal", `Int ordinal);
      ("stage", `String stage) ]
    canonical

let raw_task_record catalog source unit_name ordinal task =
  let goal = Task.task_goal task in
  task_record source unit_name goal.Decl.pr_name.id_string ordinal "raw-task"
    (canonical_task catalog source task)

let checkpoint_task_record catalog source unit_name goal_name ordinal
    provenance stage task =
  task_record source unit_name goal_name ordinal stage
    (canonical_checkpoint_task catalog source provenance stage task)

let smt_token_record source unit_name goal_name ordinal provenance events
    output =
  task_record source unit_name goal_name ordinal "smt-token-stream"
    (canonical_smt_token_stream provenance events output)

let write_record output value =
  Yojson.Safe.to_channel ~std:true output value;
  output_char output '\n'

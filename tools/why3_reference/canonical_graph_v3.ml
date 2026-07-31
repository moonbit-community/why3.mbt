(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit canonical graph v3 reference adapter, modified          *)
(*  2026-07-24.                                                     *)
(*                                                                  *)
(********************************************************************)

open Why3
open Yojson.Safe
open Canonical_v3

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let fail message = invalid_arg ("canonical_graph_v3: " ^ message)

(* OCaml does not specify constructor-argument evaluation order. Canonical
   identities are allocated on first preorder encounter, so every
   identity-bearing list below is evaluated explicitly from left to right. *)
let ordered thunks =
  List.rev
    (List.fold_left (fun values thunk -> thunk () :: values) [] thunks)

let ordered_map encode values =
  List.rev
    (List.fold_left
       (fun encoded value -> encode value :: encoded)
       [] values)

let onode name fields = node name (ordered fields)
let oproduct fields = product (ordered fields)
let osequence fields = sequence (ordered fields)
let sequence_map encode values = sequence (ordered_map encode values)

let canonical_set values =
  values
  |> List.map (fun value -> (compact value, value))
  |> List.sort (fun (left, _) (right, _) -> String.compare left right)
  |> List.map snd
  |> fun sorted -> node "Set" [`List sorted]

let canonical_map entries =
  entries
  |> List.map (fun (key, value) -> (compact key, compact value, key, value))
  |> List.sort
       (fun (left_key, left_value, _, _) (right_key, right_value, _, _) ->
         let order = String.compare left_key right_key in
         if order <> 0 then order else String.compare left_value right_value)
  |> List.map (fun (_, _, key, value) -> `List [key; value])
  |> fun sorted -> node "Map" [`List sorted]

let graph_source_for_location selected file =
  let absolute = Unix.realpath file in
  if absolute = selected.absolute then selected
  else
    let marker = Filename.dir_sep ^ "stdlib" ^ Filename.dir_sep in
    let rec find start =
      let remaining = String.length absolute - start in
      if remaining < String.length marker then None
      else if String.sub absolute start (String.length marker) = marker then
        Some start
      else
        find (start + 1)
    in
    match find 0 with
    | Some start ->
        let relative_start = start + String.length marker in
        let relative =
          String.sub absolute relative_start
            (String.length absolute - relative_start)
        in
        read_source ("why3-1.7.2/stdlib/" ^ relative) absolute
    | None ->
        let label_length = String.length selected.label in
        let absolute_length = String.length selected.absolute in
        let source_root_length = absolute_length - label_length in
        if source_root_length < 0
           || String.sub selected.absolute source_root_length label_length
                <> selected.label
        then
          fail ("semantic source location is outside fixture/stdlib: " ^ file)
        else
          let source_root =
            String.sub selected.absolute 0 source_root_length
          in
          let prefix_length = String.length source_root in
          if String.length absolute <= prefix_length
             || String.sub absolute 0 prefix_length <> source_root
          then
            fail
              ("semantic source location is outside fixture/stdlib: " ^ file)
          else
            let relative =
              String.sub absolute prefix_length
                (String.length absolute - prefix_length)
            in
            read_source relative absolute

let graph_source_span selected position =
  let file, start_line, start_column, end_line, end_column =
    Loc.get position
  in
  let source = graph_source_for_location selected file in
  node "SourceSpan"
    [ `String (hex_string source.label);
      `Int (source_offset source file start_line start_column);
      `Int (source_offset source file end_line end_column);
      `Int start_line;
      `Int start_column;
      `Int end_line;
      `Int end_column ]

let graph_source_span_option selected = function
  | None -> none
  | Some position -> some (graph_source_span selected position)

let generated_source_span_option selected = function
  | None -> none
  | Some position ->
      let file, _, _, _, _ = Loc.get position in
      let absolute =
        try Some (Unix.realpath file) with Unix.Unix_error _ -> None
      in
      begin match absolute with
      | Some absolute when absolute = selected.absolute ->
          some (graph_source_span selected position)
      | Some _ | None -> none
      end

type origin_info = {
  origin_name : string;
  origin_location : Loc.position option;
  origin_attributes : string list;
  origin_generated_stage : string option;
}

let attribute_strings attributes extra =
  (Ident.Sattr.elements attributes
   |> List.map (fun attribute -> attribute.Ident.attr_string))
  @ extra
  |> List.sort_uniq String.compare

let user_info ?(extra = []) ident =
  { origin_name = ident.Ident.id_string;
    origin_location = ident.Ident.id_loc;
    origin_attributes = attribute_strings ident.Ident.id_attrs extra;
    origin_generated_stage = None }

let generated_info stage ident =
  { origin_name = ident.Ident.id_string;
    origin_location = ident.Ident.id_loc;
    origin_attributes = attribute_strings ident.Ident.id_attrs [];
    origin_generated_stage = Some stage }

let expression_info expression =
  { origin_name = "";
    origin_location = expression.Expr.e_loc;
    origin_attributes = [];
    origin_generated_stage = None }

type task_provenance = {
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

let origin_from_provenance provenance generated_stage ident is_raw
    find_generated add_raw add_generated =
  match provenance with
  | None -> user_info ident
  | Some provenance ->
      if is_raw provenance then user_info ident
      else
        begin match find_generated provenance with
        | Some stage -> generated_info stage ident
        | None ->
            begin match generated_stage with
            | None ->
                add_raw provenance;
                user_info ident
            | Some stage ->
                add_generated provenance stage;
                generated_info stage ident
            end
        end

let builtin_type_extra symbol =
  if Ty.ts_equal symbol Ty.ts_func then
    ["builtin"; "why3:builtin:function-type"]
  else if Ty.is_ts_tuple symbol then
    ["builtin"; "why3:builtin:tuple-type"]
  else
    []

let builtin_logic_extra symbol =
  if Term.ls_equal symbol Term.ps_equ then
    ["builtin"; "why3:builtin:equality"]
  else if Term.ls_equal symbol Term.fs_bool_true then
    ["builtin"; "why3:builtin:boolean:true"]
  else if Term.ls_equal symbol Term.fs_bool_false then
    ["builtin"; "why3:builtin:boolean:false"]
  else if Term.is_fs_tuple symbol then
    ["builtin"; "why3:builtin:tuple-constructor"]
  else if Term.ls_equal symbol Term.fs_func_app then
    ["builtin"; "why3:builtin:function-application"]
  else
    []

let type_origin provenance generated_stage symbol =
  let extra = builtin_type_extra symbol in
  if extra <> [] then user_info ~extra symbol.Ty.ts_name
  else
    origin_from_provenance provenance generated_stage symbol.Ty.ts_name
      (fun value -> Ident.Sid.mem symbol.Ty.ts_name value.raw_types)
      (fun value -> Ident.Mid.find_opt symbol.Ty.ts_name value.generated_types)
      (fun value ->
        value.raw_types <- Ident.Sid.add symbol.Ty.ts_name value.raw_types)
      (fun value stage ->
        value.generated_types <-
          Ident.Mid.add symbol.Ty.ts_name stage value.generated_types;
        value.generated_identifiers <-
          Ident.Mid.add symbol.Ty.ts_name stage value.generated_identifiers)

let logic_origin provenance generated_stage symbol =
  let extra = builtin_logic_extra symbol in
  if extra <> [] then user_info ~extra symbol.Term.ls_name
  else
    origin_from_provenance provenance generated_stage symbol.Term.ls_name
      (fun value -> Term.Sls.mem symbol value.raw_logic)
      (fun value -> Term.Mls.find_opt symbol value.generated_logic)
      (fun value -> value.raw_logic <- Term.Sls.add symbol value.raw_logic)
      (fun value stage ->
        value.generated_logic <- Term.Mls.add symbol stage value.generated_logic;
        value.generated_identifiers <-
          Ident.Mid.add symbol.Term.ls_name stage value.generated_identifiers)

let proposition_origin provenance generated_stage symbol =
  origin_from_provenance provenance generated_stage symbol.Decl.pr_name
    (fun value -> Decl.Spr.mem symbol value.raw_propositions)
    (fun value -> Decl.Mpr.find_opt symbol value.generated_propositions)
    (fun value ->
      value.raw_propositions <- Decl.Spr.add symbol value.raw_propositions)
    (fun value stage ->
      value.generated_propositions <-
        Decl.Mpr.add symbol stage value.generated_propositions;
      value.generated_identifiers <-
        Ident.Mid.add symbol.Decl.pr_name stage value.generated_identifiers)

let program_origin provenance generated_stage symbol =
  origin_from_provenance provenance generated_stage symbol.Term.vs_name
    (fun value -> Term.Svs.mem symbol value.raw_programs)
    (fun value -> Term.Mvs.find_opt symbol value.generated_programs)
    (fun value ->
      value.raw_programs <- Term.Svs.add symbol value.raw_programs;
      value.raw_identifiers <-
        Ident.Sid.add symbol.Term.vs_name value.raw_identifiers)
    (fun value stage ->
      value.generated_programs <-
        Term.Mvs.add symbol stage value.generated_programs;
      value.generated_identifiers <-
        Ident.Mid.add symbol.Term.vs_name stage value.generated_identifiers)

let rec root_identifier provenance identifier =
  match Ident.Mid.find_opt identifier provenance.clone_origins with
  | None -> identifier
  | Some original -> root_identifier provenance original

let observe_identifier_clone provenance original clone =
  provenance.clone_origins <-
    Ident.Mid.add clone original provenance.clone_origins

let track_identifier_provenance provenance generated_stage identifier ty =
  match provenance with
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
        match generated_stage with
        | Some "encoding_smt_if_poly:guards" ->
            let rec nearest_ancestor_type candidate =
              match Ident.Mid.find_opt candidate provenance.clone_origins with
              | None -> None
              | Some original ->
                  begin match
                    Ident.Mid.find_opt original provenance.identifier_types
                  with
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
              begin match generated_stage with
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

type definition_kind =
  | Attribute
  | Identifier
  | Type_variable
  | Type_symbol
  | Type
  | Logic_variable
  | Logic_symbol
  | Proposition_symbol
  | Pattern
  | Term
  | Declaration
  | Theory
  | Theory_declaration
  | Task
  | Program_type_symbol
  | Region
  | Program_variable
  | Exception_symbol
  | Computation_type
  | Routine_symbol
  | Program_pattern
  | Expression
  | Computation_expression
  | Program_declaration
  | Module

let kind_tag = function
  | Attribute -> 0
  | Identifier -> 1
  | Type_variable -> 2
  | Type_symbol -> 3
  | Type -> 4
  | Logic_variable -> 5
  | Logic_symbol -> 6
  | Proposition_symbol -> 7
  | Pattern -> 8
  | Term -> 9
  | Declaration -> 10
  | Theory -> 11
  | Theory_declaration -> 12
  | Task -> 13
  | Program_type_symbol -> 14
  | Region -> 15
  | Program_variable -> 16
  | Exception_symbol -> 17
  | Computation_type -> 18
  | Routine_symbol -> 19
  | Program_pattern -> 20
  | Expression -> 21
  | Computation_expression -> 22
  | Program_declaration -> 23
  | Module -> 24

let kind_name = function
  | Attribute -> "attribute"
  | Identifier -> "identifier"
  | Type_variable -> "type-variable"
  | Type_symbol -> "type-symbol"
  | Type -> "type"
  | Logic_variable -> "logic-variable"
  | Logic_symbol -> "logic-symbol"
  | Proposition_symbol -> "proposition-symbol"
  | Pattern -> "pattern"
  | Term -> "term"
  | Declaration -> "declaration"
  | Theory -> "theory"
  | Theory_declaration -> "theory-declaration"
  | Task -> "task"
  | Program_type_symbol -> "program-type-symbol"
  | Region -> "region"
  | Program_variable -> "program-variable"
  | Exception_symbol -> "exception-symbol"
  | Computation_type -> "computation-type"
  | Routine_symbol -> "routine-symbol"
  | Program_pattern -> "program-pattern"
  | Expression -> "expression"
  | Computation_expression -> "computation-expression"
  | Program_declaration -> "program-declaration"
  | Module -> "module"

type definition_cell = Yojson.Safe.t option ref

type state = {
  source : source;
  provenance : task_provenance option;
  generated_stage : string option;
  omit_generated_vcs : bool;
  next_indices : int array;
  mutable definitions_reversed : definition_cell list;
  mutable attribute_indices : int StringMap.t;
  mutable identifier_indices : int Ident.Mid.t;
  mutable type_variable_indices : int Ty.Mtv.t;
  mutable type_symbol_indices : int Ty.Mts.t;
  mutable type_indices : int Ty.Mty.t;
  mutable logic_variable_indices : int Term.Mvs.t;
  mutable logic_symbol_indices : int Term.Mls.t;
  mutable proposition_symbol_indices : int Decl.Mpr.t;
  mutable program_type_symbol_indices : int Ity.Mits.t;
  mutable region_indices : int Ity.Mreg.t;
  mutable program_variable_indices : int Ity.Mpv.t;
  mutable exception_symbol_indices : int Ity.Mxs.t;
  mutable routine_symbol_indices : int Expr.Mrs.t;
  mutable ity_indices : int Ity.Mity.t;
  mutable theory_indices : int StringMap.t;
  mutable module_indices : int StringMap.t;
}

let new_state ?provenance ?generated_stage ?(omit_generated_vcs = false)
    source =
  { source;
    provenance;
    generated_stage;
    omit_generated_vcs;
    next_indices = Array.make 25 0;
    definitions_reversed = [];
    attribute_indices = StringMap.empty;
    identifier_indices = Ident.Mid.empty;
    type_variable_indices = Ty.Mtv.empty;
    type_symbol_indices = Ty.Mts.empty;
    type_indices = Ty.Mty.empty;
    logic_variable_indices = Term.Mvs.empty;
    logic_symbol_indices = Term.Mls.empty;
    proposition_symbol_indices = Decl.Mpr.empty;
    program_type_symbol_indices = Ity.Mits.empty;
    region_indices = Ity.Mreg.empty;
    program_variable_indices = Ity.Mpv.empty;
    exception_symbol_indices = Ity.Mxs.empty;
    routine_symbol_indices = Expr.Mrs.empty;
    ity_indices = Ity.Mity.empty;
    theory_indices = StringMap.empty;
    module_indices = StringMap.empty }

let reserve state kind =
  let tag = kind_tag kind in
  let index = state.next_indices.(tag) in
  state.next_indices.(tag) <- index + 1;
  let cell = ref None in
  state.definitions_reversed <- cell :: state.definitions_reversed;
  (index, cell)

let reference kind index =
  node "Reference" [`String (kind_name kind); `Int index]

let fill kind index cell value =
  cell := Some (node "Definition" [`String (kind_name kind); `Int index; value])

let de_bruijn index = node "DeBruijn" [`Int index]

let finish state roots =
  let definitions =
    List.rev state.definitions_reversed
    |> List.map (fun cell ->
           match !cell with
           | Some definition -> definition
           | None -> fail "reserved canonical definition was never filled")
  in
  node "GraphV3" [`List roots; `List definitions]

let origin_value state info =
  let attributes =
    info.origin_attributes
    |> List.map bytes
    |> canonical_set
  in
  match info.origin_generated_stage with
  | None ->
      onode "Origin.User"
        [ (fun () -> bytes info.origin_name);
          (fun () ->
            graph_source_span_option state.source info.origin_location);
          (fun () -> attributes) ]
  | Some stage ->
      onode "Origin.Generated"
        [ (fun () -> bytes stage);
          (fun () -> bytes info.origin_name);
          (fun () ->
            generated_source_span_option state.source info.origin_location);
          (fun () -> attributes) ]

let v3_attribute state attribute =
  match StringMap.find_opt attribute state.attribute_indices with
  | Some index -> reference Attribute index
  | None ->
      let index, cell = reserve state Attribute in
      state.attribute_indices <-
        StringMap.add attribute index state.attribute_indices;
      fill Attribute index cell (node "Ident.attribute" [bytes attribute]);
      reference Attribute index

let v3_attributes state values =
  values
  |> List.map (v3_attribute state)
  |> canonical_set

let v3_identifier state ident info =
  match Ident.Mid.find_opt ident state.identifier_indices with
  | Some index -> reference Identifier index
  | None ->
      let index, cell = reserve state Identifier in
      state.identifier_indices <-
        Ident.Mid.add ident index state.identifier_indices;
      let ident_record =
        onode "Ident.ident"
          [ (fun () -> bytes info.origin_name);
            (fun () -> v3_attributes state info.origin_attributes);
            (fun () ->
              graph_source_span_option state.source info.origin_location) ]
      in
      fill Identifier index cell
        (oproduct
           [ (fun () -> ident_record);
             (fun () -> origin_value state info) ]);
      reference Identifier index

let v3_fresh_identifier state ident info =
  let index, cell = reserve state Identifier in
  let ident_record =
    onode "Ident.ident"
      [ (fun () -> bytes info.origin_name);
        (fun () -> v3_attributes state info.origin_attributes);
        (fun () ->
          graph_source_span_option state.source info.origin_location) ]
  in
  fill Identifier index cell
    (oproduct
       [ (fun () -> ident_record);
         (fun () -> origin_value state info) ]);
  reference Identifier index

let v3_type_variable state symbol =
  match Ty.Mtv.find_opt symbol state.type_variable_indices with
  | Some index -> reference Type_variable index
  | None ->
      let index, cell = reserve state Type_variable in
      state.type_variable_indices <-
        Ty.Mtv.add symbol index state.type_variable_indices;
      (* A type variable is a binder. Its spelling and runtime identity are
         deliberately outside the semantic graph. *)
      fill Type_variable index cell (node "Ty.tvsymbol" [unit_node]);
      reference Type_variable index

let rec v3_type_definition state = function
  | Ty.NoDef -> variant0 "Ty.type_def.NoDef"
  | Ty.Alias ty -> variant1 "Ty.type_def.Alias" (v3_ty state ty)
  | Ty.Range range ->
      variant1 "Ty.type_def.Range"
        (oproduct
           [ (fun () -> bigint range.Number.ir_lower);
             (fun () -> bigint range.Number.ir_upper) ])
  | Ty.Float format ->
      variant1 "Ty.type_def.Float"
        (oproduct
           [ (fun () -> integer format.Number.fp_exponent_digits);
             (fun () -> integer format.Number.fp_significand_digits) ])

and v3_type_symbol state symbol =
  match Ty.Mts.find_opt symbol state.type_symbol_indices with
  | Some index -> reference Type_symbol index
  | None ->
      let index, cell = reserve state Type_symbol in
      state.type_symbol_indices <-
        Ty.Mts.add symbol index state.type_symbol_indices;
      let info =
        type_origin state.provenance state.generated_stage symbol
      in
      fill Type_symbol index cell
        (onode "Ty.tysymbol"
           [ (fun () -> v3_identifier state symbol.Ty.ts_name info);
             (fun () ->
               sequence_map (v3_type_variable state) symbol.Ty.ts_args);
             (fun () -> v3_type_definition state symbol.Ty.ts_def) ]);
      reference Type_symbol index

and v3_ty state ty =
  match Ty.Mty.find_opt ty state.type_indices with
  | Some index -> reference Type index
  | None ->
      let index, cell = reserve state Type in
      state.type_indices <- Ty.Mty.add ty index state.type_indices;
      let ty_node =
        match ty.Ty.ty_node with
        | Ty.Tyvar variable ->
            variant1 "Ty.ty_node.Tyvar" (v3_type_variable state variable)
        | Ty.Tyapp (symbol, arguments) ->
            variant1 "Ty.ty_node.Tyapp"
              (oproduct
                 [ (fun () -> v3_type_symbol state symbol);
                   (fun () -> sequence_map (v3_ty state) arguments) ])
      in
      fill Type index cell (node "Ty.ty" [ty_node]);
      reference Type index

let v3_logic_variable state symbol =
  match Term.Mvs.find_opt symbol state.logic_variable_indices with
  | Some index -> reference Logic_variable index
  | None ->
      let index, cell = reserve state Logic_variable in
      state.logic_variable_indices <-
        Term.Mvs.add symbol index state.logic_variable_indices;
      let info =
        program_origin state.provenance state.generated_stage symbol
      in
      fill Logic_variable index cell
        (onode "Term.vsymbol"
           [ (fun () -> v3_identifier state symbol.Term.vs_name info);
             (fun () -> v3_ty state symbol.Term.vs_ty) ]);
      reference Logic_variable index

let v3_logic_symbol state symbol =
  match Term.Mls.find_opt symbol state.logic_symbol_indices with
  | Some index -> reference Logic_symbol index
  | None ->
      let index, cell = reserve state Logic_symbol in
      state.logic_symbol_indices <-
        Term.Mls.add symbol index state.logic_symbol_indices;
      let info =
        logic_origin state.provenance state.generated_stage symbol
      in
      fill Logic_symbol index cell
        (onode "Term.lsymbol"
           [ (fun () -> v3_identifier state symbol.Term.ls_name info);
             (fun () -> sequence_map (v3_ty state) symbol.Term.ls_args);
             (fun () ->
               option (v3_ty state) symbol.Term.ls_value);
             (fun () -> integer symbol.Term.ls_constr);
             (fun () -> boolean symbol.Term.ls_proj) ]);
      reference Logic_symbol index

let v3_proposition_symbol state symbol =
  match Decl.Mpr.find_opt symbol state.proposition_symbol_indices with
  | Some index -> reference Proposition_symbol index
  | None ->
      let index, cell = reserve state Proposition_symbol in
      state.proposition_symbol_indices <-
        Decl.Mpr.add symbol index state.proposition_symbol_indices;
      let info =
        proposition_origin state.provenance state.generated_stage symbol
      in
      fill Proposition_symbol index cell
        (node "Decl.prsymbol"
           [v3_identifier state symbol.Decl.pr_name info]);
      reference Proposition_symbol index

let bound_variable_index bound variable =
  let rec search distance = function
    | [] -> None
    | candidate :: rest ->
        if Term.vs_equal candidate variable then Some distance
        else search (distance + 1) rest
  in
  search 0 (List.rev bound)

let v3_variable_reference state bound variable =
  match bound_variable_index bound variable with
  | Some index -> de_bruijn index
  | None -> v3_logic_variable state variable

let v3_pattern_binder state bound variable =
  match bound_variable_index bound variable with
  | None -> fail "pattern binder is absent from its binding set"
  | Some index ->
      oproduct
        [ (fun () -> de_bruijn index);
          (fun () -> v3_ty state variable.Term.vs_ty) ]

let rec v3_pattern state bound pattern =
  let index, cell = reserve state Pattern in
  let pattern_node =
    match pattern.Term.pat_node with
    | Term.Pwild -> variant0 "Term.pattern_node.Pwild"
    | Term.Pvar variable ->
        variant1 "Term.pattern_node.Pvar"
          (v3_pattern_binder state bound variable)
    | Term.Papp (symbol, arguments) ->
        variant1 "Term.pattern_node.Papp"
          (oproduct
             [ (fun () -> v3_logic_symbol state symbol);
               (fun () ->
                 sequence_map (v3_pattern state bound) arguments) ])
    | Term.Por (left, right) ->
        variant1 "Term.pattern_node.Por"
          (oproduct
             [ (fun () -> v3_pattern state bound left);
               (fun () -> v3_pattern state bound right) ])
    | Term.Pas (inner, variable) ->
        variant1 "Term.pattern_node.Pas"
          (oproduct
             [ (fun () -> v3_pattern state bound inner);
               (fun () -> v3_pattern_binder state bound variable) ])
  in
  fill Pattern index cell
    (onode "Term.pattern"
       [ (fun () -> pattern_node);
         (fun () -> v3_ty state pattern.Term.pat_ty) ]);
  reference Pattern index

let v3_quantifier = function
  | Term.Tforall -> variant0 "Term.quant.Tforall"
  | Term.Texists -> variant0 "Term.quant.Texists"

let v3_binary_operator = function
  | Term.Tand -> variant0 "Term.binop.Tand"
  | Term.Tor -> variant0 "Term.binop.Tor"
  | Term.Timplies -> variant0 "Term.binop.Timplies"
  | Term.Tiff -> variant0 "Term.binop.Tiff"

let rec v3_term state bound term =
  let index, cell = reserve state Term in
  let term_node =
    match term.Term.t_node with
    | Term.Tvar variable ->
        variant1 "Term.term_node.Tvar"
          (v3_variable_reference state bound variable)
    | Term.Tconst constant ->
        variant1 "Term.term_node.Tconst" (canonical_constant constant)
    | Term.Tapp (symbol, arguments) ->
        variant1 "Term.term_node.Tapp"
          (oproduct
             [ (fun () -> v3_logic_symbol state symbol);
               (fun () -> sequence_map (v3_term state bound) arguments) ])
    | Term.Tif (condition, consequent, alternative) ->
        variant1 "Term.term_node.Tif"
          (oproduct
             [ (fun () -> v3_term state bound condition);
               (fun () -> v3_term state bound consequent);
               (fun () -> v3_term state bound alternative) ])
    | Term.Tlet (value, binding) ->
        let variable, body = Term.t_open_bound binding in
        track_identifier_provenance state.provenance state.generated_stage
          (Term.t_peek_bound binding) (Some variable.Term.vs_ty);
        variant1 "Term.term_node.Tlet"
          (oproduct
             [ (fun () -> v3_term state bound value);
               (fun () -> v3_ty state variable.Term.vs_ty);
               (fun () -> v3_term state (bound @ [variable]) body) ])
    | Term.Tcase (scrutinee, branches) ->
        variant1 "Term.term_node.Tcase"
          (oproduct
             [ (fun () -> v3_term state bound scrutinee);
               (fun () ->
                 sequence_map
                   (fun branch ->
                     Ident.Sid.iter
                       (fun identifier ->
                         track_identifier_provenance state.provenance
                           state.generated_stage identifier None)
                       (Term.t_peek_branch branch);
                     let pattern, body = Term.t_open_branch branch in
                     let variables =
                       Term.Svs.elements pattern.Term.pat_vars
                     in
                     oproduct
                       [ (fun () -> v3_pattern state variables pattern);
                         (fun () ->
                           v3_term state (bound @ variables) body) ])
                   branches) ])
    | Term.Teps binding ->
        let variable, body = Term.t_open_bound binding in
        track_identifier_provenance state.provenance state.generated_stage
          (Term.t_peek_bound binding) (Some variable.Term.vs_ty);
        variant1 "Term.term_node.Teps"
          (oproduct
             [ (fun () -> v3_ty state variable.Term.vs_ty);
               (fun () -> v3_term state (bound @ [variable]) body) ])
    | Term.Tquant (quantifier, quantified) ->
        let variables, triggers, body = Term.t_open_quant quantified in
        List.iter2
          (fun identifier variable ->
            track_identifier_provenance state.provenance
              state.generated_stage identifier (Some variable.Term.vs_ty))
          (Term.t_peek_quant quantified) variables;
        let extended = bound @ variables in
        variant1 "Term.term_node.Tquant"
          (oproduct
             [ (fun () -> v3_quantifier quantifier);
               (fun () ->
                 sequence_map
                   (fun variable -> v3_ty state variable.Term.vs_ty)
                   variables);
               (fun () ->
                 sequence_map
                   (fun trigger ->
                     sequence_map (v3_term state extended) trigger)
                   triggers);
               (fun () -> v3_term state extended body) ])
    | Term.Tbinop (operator, left, right) ->
        variant1 "Term.term_node.Tbinop"
          (oproduct
             [ (fun () -> v3_binary_operator operator);
               (fun () -> v3_term state bound left);
               (fun () -> v3_term state bound right) ])
    | Term.Tnot inner ->
        variant1 "Term.term_node.Tnot" (v3_term state bound inner)
    | Term.Ttrue -> variant0 "Term.term_node.Ttrue"
    | Term.Tfalse -> variant0 "Term.term_node.Tfalse"
  in
  let term_record =
    onode "Term.term"
      [ (fun () -> term_node);
        (fun () -> option (v3_ty state) term.Term.t_ty);
        (fun () ->
          v3_attributes state (attribute_strings term.Term.t_attrs []));
        (fun () -> graph_source_span_option state.source term.Term.t_loc) ]
  in
  (* Why3's Term.term has no semantic-origin field. MoonBit retains a
     separate optional projection so that generated terms can carry one;
     source and upstream transform terms therefore use Option.None. *)
  fill Term index cell
    (oproduct
       [ (fun () -> term_record);
         (fun () -> none) ]);
  reference Term index

let v3_proposition_kind = function
  | Decl.Paxiom -> variant0 "Decl.prop_kind.Paxiom"
  | Decl.Plemma -> variant0 "Decl.prop_kind.Plemma"
  | Decl.Pgoal -> variant0 "Decl.prop_kind.Pgoal"

let v3_inductive_sign = function
  | Decl.Ind -> variant0 "Decl.ind_sign.Ind"
  | Decl.Coind -> variant0 "Decl.ind_sign.Coind"

let declaration_origin state declaration =
  match declaration.Decl.d_node with
  | Decl.Dtype symbol ->
      type_origin state.provenance state.generated_stage symbol
  | Decl.Ddata ((symbol, _) :: _) ->
      type_origin state.provenance state.generated_stage symbol
  | Decl.Dparam symbol ->
      logic_origin state.provenance state.generated_stage symbol
  | Decl.Dlogic ((symbol, _) :: _) ->
      logic_origin state.provenance state.generated_stage symbol
  | Decl.Dind (_, (symbol, _) :: _) ->
      logic_origin state.provenance state.generated_stage symbol
  | Decl.Dprop (_, symbol, _) ->
      proposition_origin state.provenance state.generated_stage symbol
  | Decl.Ddata [] | Decl.Dlogic [] | Decl.Dind (_, []) ->
      fail "empty declaration group"

let v3_logic_definition state (symbol, definition) =
  let parameters, body = Decl.open_ls_defn definition in
  begin match (Decl.ls_defn_axiom definition).Term.t_node with
  | Term.Tquant (_, quantified) ->
      List.iter2
        (fun identifier parameter ->
          track_identifier_provenance state.provenance state.generated_stage
            identifier (Some parameter.Term.vs_ty))
        (Term.t_peek_quant quantified) parameters
  | _ -> ()
  end;
  oproduct
    [ (fun () -> v3_logic_symbol state symbol);
      (fun () ->
        sequence_map
          (fun parameter -> v3_ty state parameter.Term.vs_ty)
          parameters);
      (fun () -> v3_term state parameters body) ]

let v3_data_constructor state (symbol, projections) =
  oproduct
    [ (fun () -> v3_logic_symbol state symbol);
      (fun () ->
        sequence_map
          (fun projection -> option (v3_logic_symbol state) projection)
          projections) ]

let v3_data_declaration state (symbol, constructors) =
  oproduct
    [ (fun () -> v3_type_symbol state symbol);
      (fun () ->
        sequence_map (v3_data_constructor state) constructors) ]

let v3_inductive_case state (proposition, formula) =
  oproduct
    [ (fun () -> v3_proposition_symbol state proposition);
      (fun () -> v3_term state [] formula) ]

let v3_inductive_declaration state (predicate, cases) =
  oproduct
    [ (fun () -> v3_logic_symbol state predicate);
      (fun () -> sequence_map (v3_inductive_case state) cases) ]

let v3_declaration state declaration =
  let index, cell = reserve state Declaration in
  let declaration_node =
    match declaration.Decl.d_node with
    | Decl.Dtype symbol ->
        variant1 "Decl.decl_node.Dtype" (v3_type_symbol state symbol)
    | Decl.Ddata declarations ->
        variant1 "Decl.decl_node.Ddata"
          (sequence_map (v3_data_declaration state) declarations)
    | Decl.Dparam symbol ->
        variant1 "Decl.decl_node.Dparam" (v3_logic_symbol state symbol)
    | Decl.Dlogic definitions ->
        variant1 "Decl.decl_node.Dlogic"
          (sequence_map (v3_logic_definition state) definitions)
    | Decl.Dind (sign, declarations) ->
        variant1 "Decl.decl_node.Dind"
          (oproduct
             [ (fun () -> v3_inductive_sign sign);
               (fun () ->
                 sequence_map (v3_inductive_declaration state) declarations) ])
    | Decl.Dprop (kind, symbol, formula) ->
        variant1 "Decl.decl_node.Dprop"
          (oproduct
             [ (fun () -> v3_proposition_kind kind);
               (fun () -> v3_proposition_symbol state symbol);
               (fun () -> v3_term state [] formula) ])
  in
  fill Declaration index cell
    (oproduct
       [ (fun () -> node "Decl.decl" [declaration_node]);
         (fun () -> origin_value state (declaration_origin state declaration)) ]);
  reference Declaration index

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

let string_starts_with prefix value =
  let prefix_length = String.length prefix in
  String.length value >= prefix_length &&
  String.sub value 0 prefix_length = prefix

let is_generated_vc_proposition proposition =
  Ident.Sattr.elements proposition.Decl.pr_name.Ident.id_attrs
  |> List.exists (fun attribute ->
         string_starts_with "expl:VC for " attribute.Ident.attr_string)

let is_generated_vc_declaration declaration =
  match declaration.Decl.d_node with
  | Decl.Dprop (Decl.Pgoal, proposition, _) ->
      is_generated_vc_proposition proposition
  | _ -> false

let is_generated_vc_program_declaration declaration =
  match declaration.Pdecl.pd_node with
  | Pdecl.PDpure ->
      declaration.Pdecl.pd_pure <> [] &&
      List.for_all is_generated_vc_declaration declaration.Pdecl.pd_pure
  | Pdecl.PDtype _ | Pdecl.PDlet _ | Pdecl.PDexn _ -> false

let is_generated_vc_theory_declaration declaration =
  match declaration.Theory.td_node with
  | Theory.Decl value -> is_generated_vc_declaration value
  | Theory.Use _ | Theory.Clone _ | Theory.Meta _ -> false

let v3_meta_argument_type = function
  | Theory.MTty -> variant0 "Theory.meta_arg_type.MTty"
  | Theory.MTtysymbol -> variant0 "Theory.meta_arg_type.MTtysymbol"
  | Theory.MTlsymbol -> variant0 "Theory.meta_arg_type.MTlsymbol"
  | Theory.MTprsymbol -> variant0 "Theory.meta_arg_type.MTprsymbol"
  | Theory.MTstring -> variant0 "Theory.meta_arg_type.MTstring"
  | Theory.MTint -> variant0 "Theory.meta_arg_type.MTint"
  | Theory.MTid -> variant0 "Theory.meta_arg_type.MTid"

let v3_meta_descriptor meta =
  onode "Theory.meta"
    [ (fun () -> bytes meta.Theory.meta_name);
      (fun () ->
        sequence_map v3_meta_argument_type meta.Theory.meta_type);
      (fun () -> boolean meta.Theory.meta_excl) ]

let v3_meta_argument state = function
  | Theory.MAty ty ->
      variant1 "Theory.meta_arg.MAty" (v3_ty state ty)
  | Theory.MAts symbol ->
      variant1 "Theory.meta_arg.MAts" (v3_type_symbol state symbol)
  | Theory.MAls symbol ->
      variant1 "Theory.meta_arg.MAls" (v3_logic_symbol state symbol)
  | Theory.MApr symbol ->
      variant1 "Theory.meta_arg.MApr" (v3_proposition_symbol state symbol)
  | Theory.MAstr value ->
      variant1 "Theory.meta_arg.MAstr" (bytes value)
  | Theory.MAint value ->
      variant1 "Theory.meta_arg.MAint" (integer value)
  | Theory.MAid ident ->
      variant1 "Theory.meta_arg.MAid"
        (v3_fresh_identifier state ident (user_info ident))

let v3_meta_application state meta arguments =
  oproduct
    [ (fun () -> v3_meta_descriptor meta);
      (fun () -> sequence_map (v3_meta_argument state) arguments) ]

let v3_symbol_map state map =
  onode "Theory.symbol_map"
    [ (fun () ->
        canonical_map
          (Ty.Mts.bindings map.Theory.sm_ty
           |> ordered_map (fun (source, target) ->
                  (v3_type_symbol state source, v3_ty state target))));
      (fun () ->
        canonical_map
          (Ty.Mts.bindings map.Theory.sm_ts
           |> ordered_map (fun (source, target) ->
                  (v3_type_symbol state source,
                   v3_type_symbol state target))));
      (fun () ->
        canonical_map
          (Term.Mls.bindings map.Theory.sm_ls
           |> ordered_map (fun (source, target) ->
                  (v3_logic_symbol state source,
                   v3_logic_symbol state target))));
      (fun () ->
        canonical_map
          (Decl.Mpr.bindings map.Theory.sm_pr
           |> ordered_map (fun (source, target) ->
                  (v3_proposition_symbol state source,
                   v3_proposition_symbol state target)))) ]

let rec v3_namespace state namespace =
  onode "Theory.namespace"
    [ (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ts
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_type_symbol state symbol))));
      (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ls
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_logic_symbol state symbol))));
      (fun () ->
        canonical_map
          ((Wstdlib.Mstr.bindings namespace.Theory.ns_pr
            |> List.filter (fun (_, symbol) ->
                   (not state.omit_generated_vcs) ||
                   not (is_generated_vc_proposition symbol)))
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_proposition_symbol state symbol))));
      (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Theory.ns_ns
           |> ordered_map (fun (name, nested) ->
                  (bytes name, v3_namespace state nested)))) ]

let rec v3_theory state theory =
  let key = theory_key theory in
  match StringMap.find_opt key state.theory_indices with
  | Some index -> reference Theory index
  | None ->
      let index, cell = reserve state Theory in
      state.theory_indices <-
        StringMap.add key index state.theory_indices;
      fill Theory index cell
        (onode "Theory.theory"
           [ (fun () ->
               v3_identifier state theory.Theory.th_name
                 (user_info theory.Theory.th_name));
             (fun () ->
               sequence_map bytes theory.Theory.th_path);
             (fun () ->
               let declarations =
                 if state.omit_generated_vcs then
                   List.filter
                     (fun declaration ->
                       not
                         (is_generated_vc_theory_declaration declaration))
                     theory.Theory.th_decls
                 else
                   theory.Theory.th_decls
               in
               sequence_map (v3_theory_declaration state) declarations);
             (fun () ->
               v3_namespace state theory.Theory.th_export) ]);
      reference Theory index

and v3_theory_declaration state declaration =
  let index, cell = reserve state Theory_declaration in
  let declaration_node =
    match declaration.Theory.td_node with
    | Theory.Decl value ->
        variant1 "Theory.tdecl_node.Decl" (v3_declaration state value)
    | Theory.Use source ->
        variant1 "Theory.tdecl_node.Use" (v3_theory state source)
    | Theory.Clone (source, map) ->
        variant1 "Theory.tdecl_node.Clone"
          (oproduct
             [ (fun () -> v3_theory state source);
               (fun () -> v3_symbol_map state map) ])
    | Theory.Meta (meta, arguments) ->
        variant1 "Theory.tdecl_node.Meta"
          (v3_meta_application state meta arguments)
  in
  fill Theory_declaration index cell
    (node "Theory.tdecl" [declaration_node]);
  reference Theory_declaration index

let rec v3_task_head state head =
  let index, cell = reserve state Task in
  fill Task index cell
    (onode "Task.task_hd"
       [ (fun () ->
           v3_theory_declaration state head.Task.task_decl);
         (fun () -> option (v3_task_head state) head.Task.task_prev) ]);
  reference Task index

let v3_task state = function
  | None -> fail "canonical v3 cannot encode an empty task"
  | Some head -> v3_task_head state head

let graph_of_ty source ty =
  let state = new_state source in
  finish state [v3_ty state ty]

let graph_of_type_symbol source symbol =
  let state = new_state source in
  finish state [v3_type_symbol state symbol]

let graph_of_logic_variable source symbol =
  let state = new_state source in
  finish state [v3_logic_variable state symbol]

let graph_of_logic_symbol source symbol =
  let state = new_state source in
  finish state [v3_logic_symbol state symbol]

let graph_of_proposition_symbol source symbol =
  let state = new_state source in
  finish state [v3_proposition_symbol state symbol]

let graph_of_term source term =
  let state = new_state source in
  finish state [v3_term state [] term]

let graph_of_declaration source declaration =
  let state = new_state source in
  finish state [v3_declaration state declaration]

let graph_of_theory source theory =
  let state = new_state source in
  finish state [v3_theory state theory]

let graph_of_task source task =
  let state = new_state source in
  finish state [v3_task state task]

let task_trace_provenance source task =
  let provenance = new_task_provenance () in
  let state = new_state ~provenance source in
  ignore (v3_task state task);
  provenance

let graph_of_checkpoint_task source provenance stage task =
  let state = new_state ~provenance ~generated_stage:stage source in
  finish state [v3_task state task]

let rec v3_program_mask = function
  | Ity.MaskVisible -> variant0 "Ity.mask.MaskVisible"
  | Ity.MaskTuple masks ->
      variant1 "Ity.mask.MaskTuple"
        (sequence_map v3_program_mask masks)
  | Ity.MaskGhost -> variant0 "Ity.mask.MaskGhost"

let v3_program_type_flag flag =
  onode "Ity.its_flag"
    [ (fun () -> boolean flag.Ity.its_frozen);
      (fun () -> boolean flag.Ity.its_exposed);
      (fun () -> boolean flag.Ity.its_liable);
      (fun () -> boolean flag.Ity.its_fixed);
      (fun () -> boolean flag.Ity.its_visible) ]

let rec v3_program_type_definition state = function
  | Ty.NoDef -> variant0 "Ty.type_def.NoDef"
  | Ty.Alias ity -> variant1 "Ty.type_def.Alias" (v3_ity state ity)
  | Ty.Range range ->
      variant1 "Ty.type_def.Range"
        (oproduct
           [ (fun () -> bigint range.Number.ir_lower);
             (fun () -> bigint range.Number.ir_upper) ])
  | Ty.Float format ->
      variant1 "Ty.type_def.Float"
        (oproduct
           [ (fun () -> integer format.Number.fp_exponent_digits);
             (fun () -> integer format.Number.fp_significand_digits) ])

and v3_program_type_symbol state symbol =
  match Ity.Mits.find_opt symbol state.program_type_symbol_indices with
  | Some index -> reference Program_type_symbol index
  | None ->
      let index, cell = reserve state Program_type_symbol in
      state.program_type_symbol_indices <-
        Ity.Mits.add symbol index state.program_type_symbol_indices;
      let info =
        type_origin state.provenance state.generated_stage
          symbol.Ity.its_ts
      in
      let symbol_record =
        onode "Ity.itysymbol"
          [ (fun () -> v3_type_symbol state symbol.Ity.its_ts);
            (fun () -> boolean symbol.Ity.its_nonfree);
            (fun () -> boolean symbol.Ity.its_private);
            (fun () -> boolean symbol.Ity.its_mutable);
            (fun () -> boolean symbol.Ity.its_fragile);
            (fun () ->
              sequence_map (v3_program_variable state)
                symbol.Ity.its_mfields);
            (fun () ->
              sequence_map (v3_program_variable state)
                symbol.Ity.its_ofields);
            (fun () ->
              sequence_map (v3_region state) symbol.Ity.its_regions);
            (fun () ->
              sequence_map v3_program_type_flag symbol.Ity.its_arg_flg);
            (fun () ->
              sequence_map v3_program_type_flag symbol.Ity.its_reg_flg);
            (fun () ->
              v3_program_type_definition state symbol.Ity.its_def) ]
      in
      fill Program_type_symbol index cell
        (oproduct
           [ (fun () -> symbol_record);
             (fun () -> origin_value state info) ]);
      reference Program_type_symbol index

and v3_region state region =
  match Ity.Mreg.find_opt region state.region_indices with
  | Some index -> reference Region index
  | None ->
      let index, cell = reserve state Region in
      state.region_indices <- Ity.Mreg.add region index state.region_indices;
      fill Region index cell
        (onode "Ity.region"
           [ (fun () ->
               v3_identifier state region.Ity.reg_name
                 (user_info region.Ity.reg_name));
             (fun () -> v3_program_type_symbol state region.Ity.reg_its);
             (fun () -> sequence_map (v3_ity state) region.Ity.reg_args);
             (fun () -> sequence_map (v3_ity state) region.Ity.reg_regs) ]);
      reference Region index

and v3_ity state ity =
  match Ity.Mity.find_opt ity state.ity_indices with
  | Some index -> reference Type index
  | None ->
      let index, cell = reserve state Type in
      state.ity_indices <- Ity.Mity.add ity index state.ity_indices;
      let ity_node =
        match ity.Ity.ity_node with
        | Ity.Ityvar variable ->
            variant1 "Ity.ity_node.Ityvar"
              (v3_type_variable state variable)
        | Ity.Ityapp (symbol, arguments, regions) ->
            variant1 "Ity.ity_node.Ityapp"
              (oproduct
                 [ (fun () -> v3_program_type_symbol state symbol);
                   (fun () -> sequence_map (v3_ity state) arguments);
                   (fun () -> sequence_map (v3_ity state) regions) ])
        | Ity.Ityreg region ->
            variant1 "Ity.ity_node.Ityreg" (v3_region state region)
      in
      fill Type index cell (node "Ity.ity" [ity_node]);
      reference Type index

and v3_program_variable state variable =
  match Ity.Mpv.find_opt variable state.program_variable_indices with
  | Some index -> reference Program_variable index
  | None ->
      let index, cell = reserve state Program_variable in
      state.program_variable_indices <-
        Ity.Mpv.add variable index state.program_variable_indices;
      fill Program_variable index cell
        (onode "Ity.pvsymbol"
           [ (fun () -> v3_logic_variable state variable.Ity.pv_vs);
             (fun () -> v3_ity state variable.Ity.pv_ity);
             (fun () -> boolean variable.Ity.pv_ghost) ]);
      reference Program_variable index

let v3_exception_symbol state symbol =
  match Ity.Mxs.find_opt symbol state.exception_symbol_indices with
  | Some index -> reference Exception_symbol index
  | None ->
      let index, cell = reserve state Exception_symbol in
      state.exception_symbol_indices <-
        Ity.Mxs.add symbol index state.exception_symbol_indices;
      fill Exception_symbol index cell
        (onode "Ity.xsymbol"
           [ (fun () ->
               v3_identifier state symbol.Ity.xs_name
                 (user_info symbol.Ity.xs_name));
             (fun () -> v3_ity state symbol.Ity.xs_ity);
             (fun () -> v3_program_mask symbol.Ity.xs_mask) ]);
      reference Exception_symbol index

let bound_program_variable_index bound variable =
  let rec search distance = function
    | [] -> None
    | candidate :: rest ->
        if Ity.pv_equal candidate variable then Some distance
        else search (distance + 1) rest
  in
  search 0 (List.rev bound)

let v3_program_variable_reference state bound variable =
  match bound_program_variable_index bound variable with
  | Some index -> de_bruijn index
  | None -> v3_program_variable state variable

let v3_program_binder state bound variable =
  let identity =
    match bound_program_variable_index bound variable with
    | Some index -> de_bruijn index
    | None -> v3_program_variable state variable
  in
  oproduct
    [ (fun () -> identity);
      (fun () -> v3_ity state variable.Ity.pv_ity);
      (fun () -> boolean variable.Ity.pv_ghost) ]

let v3_program_termination = function
  | Ity.Total -> variant0 "Ity.oneway.Total"
  | Ity.Partial -> variant0 "Ity.oneway.Partial"
  | Ity.Diverges -> variant0 "Ity.oneway.Diverges"

let v3_effect state bound effect =
  onode "Ity.effect"
    [ (fun () ->
        Ity.Spv.elements effect.Ity.eff_reads
        |> ordered_map (v3_program_variable_reference state bound)
        |> canonical_set);
      (fun () ->
        Ity.Mreg.bindings effect.Ity.eff_writes
        |> ordered_map (fun (region, fields) ->
               let key = v3_region state region in
               let value =
                 Ity.Spv.elements fields
                 |> ordered_map
                      (v3_program_variable_reference state bound)
                 |> canonical_set
               in
               (key, value))
        |> canonical_map);
      (fun () ->
        Ity.Sreg.elements effect.Ity.eff_taints
        |> ordered_map (v3_region state)
        |> canonical_set);
      (fun () ->
        Ity.Sreg.elements effect.Ity.eff_covers
        |> ordered_map (v3_region state)
        |> canonical_set);
      (fun () ->
        Ity.Sreg.elements effect.Ity.eff_resets
        |> ordered_map (v3_region state)
        |> canonical_set);
      (fun () ->
        Ity.Sxs.elements effect.Ity.eff_raises
        |> ordered_map (v3_exception_symbol state)
        |> canonical_set);
      (fun () ->
        Ty.Stv.elements effect.Ity.eff_spoils
        |> ordered_map (v3_type_variable state)
        |> canonical_set);
      (fun () -> v3_program_termination effect.Ity.eff_oneway);
      (fun () -> boolean effect.Ity.eff_ghost) ]

let v3_ity_substitution state substitution =
  onode "Ity.ity_subst"
    [ (fun () ->
        canonical_map
          (Ty.Mtv.bindings substitution.Ity.isb_var
           |> ordered_map (fun (variable, ity) ->
                  (v3_type_variable state variable, v3_ity state ity))));
      (fun () ->
        canonical_map
          (Ity.Mreg.bindings substitution.Ity.isb_reg
           |> ordered_map (fun (region, ity) ->
                  (v3_region state region, v3_ity state ity)))) ]

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
    (fun (snapshot, original) ->
      add snapshot;
      add original)
    (Ity.Mpv.bindings cty.Ity.cty_oldies);
  List.rev !reversed

let v3_postcondition state bound post =
  let result, formula = Ity.open_post post in
  oproduct
    [ (fun () -> v3_ty state result.Term.vs_ty);
      (fun () -> v3_term state (bound @ [result]) formula) ]

let v3_cty state cty =
  let index, cell = reserve state Computation_type in
  let bound_program = cty_program_variables cty in
  let bound_pure =
    List.map (fun variable -> variable.Ity.pv_vs) bound_program
  in
  fill Computation_type index cell
    (onode "Ity.cty"
       [ (fun () ->
           sequence_map (v3_program_binder state bound_program)
             cty.Ity.cty_args);
         (fun () ->
           sequence_map (v3_term state bound_pure) cty.Ity.cty_pre);
         (fun () ->
           sequence_map (v3_postcondition state bound_pure)
             cty.Ity.cty_post);
         (fun () ->
           canonical_map
             (Ity.Mxs.bindings cty.Ity.cty_xpost
              |> ordered_map (fun (exception_, posts) ->
                     (v3_exception_symbol state exception_,
                      sequence_map
                        (v3_postcondition state bound_pure)
                        posts))));
         (fun () ->
           canonical_map
             (Ity.Mpv.bindings cty.Ity.cty_oldies
              |> ordered_map (fun (snapshot, original) ->
                     (v3_program_variable_reference state bound_program
                        snapshot,
                      v3_program_variable_reference state bound_program
                        original))));
         (fun () ->
           v3_effect state bound_program cty.Ity.cty_effect);
         (fun () -> v3_ity state cty.Ity.cty_result);
         (fun () -> v3_program_mask cty.Ity.cty_mask);
         (fun () -> v3_ity_substitution state cty.Ity.cty_freeze) ]);
  reference Computation_type index

let v3_routine_logic state = function
  | Expr.RLnone -> variant0 "Expr.rs_logic.RLnone"
  | Expr.RLpv variable ->
      variant1 "Expr.rs_logic.RLpv" (v3_program_variable state variable)
  | Expr.RLls symbol ->
      variant1 "Expr.rs_logic.RLls" (v3_logic_symbol state symbol)
  | Expr.RLlemma -> variant0 "Expr.rs_logic.RLlemma"

let v3_routine_symbol state symbol =
  match Expr.Mrs.find_opt symbol state.routine_symbol_indices with
  | Some index -> reference Routine_symbol index
  | None ->
      let index, cell = reserve state Routine_symbol in
      state.routine_symbol_indices <-
        Expr.Mrs.add symbol index state.routine_symbol_indices;
      let info =
        match symbol.Expr.rs_logic with
        | Expr.RLls logic ->
            logic_origin state.provenance state.generated_stage logic
        | Expr.RLpv variable ->
            program_origin state.provenance state.generated_stage
              variable.Ity.pv_vs
        | Expr.RLnone | Expr.RLlemma ->
            user_info symbol.Expr.rs_name
      in
      let symbol_record =
        onode "Expr.rsymbol"
          [ (fun () -> v3_identifier state symbol.Expr.rs_name info);
            (fun () -> v3_cty state symbol.Expr.rs_cty);
            (fun () -> v3_routine_logic state symbol.Expr.rs_logic);
            (fun () ->
              option (v3_program_variable state) symbol.Expr.rs_field) ]
      in
      fill Routine_symbol index cell
        (oproduct
           [ (fun () -> symbol_record);
             (fun () -> origin_value state info) ]);
      reference Routine_symbol index

let graph_of_ity source ity =
  let state = new_state source in
  finish state [v3_ity state ity]

let graph_of_program_type_symbol source symbol =
  let state = new_state source in
  finish state [v3_program_type_symbol state symbol]

let graph_of_routine_symbol source symbol =
  let state = new_state source in
  finish state [v3_routine_symbol state symbol]

let bound_program_pure_symbols bound =
  List.map (fun variable -> variable.Ity.pv_vs) bound

let v3_pattern_ghost = function
  | Expr.PGfail -> variant0 "Expr.pat_ghost.PGfail"
  | Expr.PGlast -> variant0 "Expr.pat_ghost.PGlast"
  | Expr.PGnone -> variant0 "Expr.pat_ghost.PGnone"

let program_pattern_variables pattern =
  Term.Svs.elements pattern.Expr.pp_pat.Term.pat_vars
  |> List.map (fun variable ->
         try Ity.restore_pv variable
         with Not_found ->
           fail "program pattern variable has no pvsymbol projection")

let v3_program_pattern state pattern =
  let index, cell = reserve state Program_pattern in
  let variables = program_pattern_variables pattern in
  let pure_variables =
    List.map (fun variable -> variable.Ity.pv_vs) variables
  in
  fill Program_pattern index cell
    (onode "Expr.prog_pattern"
       [ (fun () -> v3_pattern state pure_variables pattern.Expr.pp_pat);
         (fun () -> v3_ity state pattern.Expr.pp_ity);
         (fun () -> v3_program_mask pattern.Expr.pp_mask);
         (fun () -> v3_pattern_ghost pattern.Expr.pp_fail) ]);
  reference Program_pattern index

let v3_program_variant state bound (term, relation) =
  oproduct
    [ (fun () ->
        v3_term state (bound_program_pure_symbols bound) term);
      (fun () -> option (v3_logic_symbol state) relation) ]

let rec v3_computation_expression state bound computation =
  let index, cell = reserve state Computation_expression in
  let computation_node =
    match computation.Expr.c_node with
    | Expr.Capp (symbol, arguments) ->
        variant1 "Expr.cexp_node.Capp"
          (oproduct
             [ (fun () -> v3_routine_symbol state symbol);
               (fun () ->
                 sequence_map
                   (v3_program_variable_reference state bound)
                   arguments) ])
    | Expr.Cpur (symbol, arguments) ->
        variant1 "Expr.cexp_node.Cpur"
          (oproduct
             [ (fun () -> v3_logic_symbol state symbol);
               (fun () ->
                 sequence_map
                   (v3_program_variable_reference state bound)
                   arguments) ])
    | Expr.Cfun body ->
        variant1 "Expr.cexp_node.Cfun"
          (v3_expression state
             (bound @ computation.Expr.c_cty.Ity.cty_args)
             body)
    | Expr.Cany -> variant0 "Expr.cexp_node.Cany"
  in
  fill Computation_expression index cell
    (onode "Expr.cexp"
       [ (fun () -> computation_node);
         (fun () -> v3_cty state computation.Expr.c_cty) ]);
  reference Computation_expression index

and v3_recursive_definition state bound definition =
  onode "Expr.rec_defn"
    [ (fun () -> v3_routine_symbol state definition.Expr.rec_sym);
      (fun () -> v3_routine_symbol state definition.Expr.rec_rsym);
      (fun () ->
        v3_computation_expression state bound definition.Expr.rec_fun);
      (fun () ->
        sequence_map (v3_program_variant state bound)
          definition.Expr.rec_varl) ]

and v3_let_definition state bound = function
  | Expr.LDvar (variable, value) ->
      variant1 "Expr.let_defn.LDvar"
        (oproduct
           [ (fun () -> v3_program_binder state [variable] variable);
             (fun () -> v3_expression state bound value) ])
  | Expr.LDsym (symbol, computation) ->
      variant1 "Expr.let_defn.LDsym"
        (oproduct
           [ (fun () -> v3_routine_symbol state symbol);
             (fun () ->
               v3_computation_expression state bound computation) ])
  | Expr.LDrec definitions ->
      variant1 "Expr.let_defn.LDrec"
        (sequence_map (v3_recursive_definition state bound) definitions)

and v3_expression state bound expression =
  let index, cell = reserve state Expression in
  let expression_node =
    match expression.Expr.e_node with
    | Expr.Evar variable ->
        variant1 "Expr.expr_node.Evar"
          (v3_program_variable_reference state bound variable)
    | Expr.Econst constant ->
        variant1 "Expr.expr_node.Econst" (canonical_constant constant)
    | Expr.Eexec (computation, cty) ->
        variant1 "Expr.expr_node.Eexec"
          (oproduct
             [ (fun () ->
                 v3_computation_expression state bound computation);
               (fun () -> v3_cty state cty) ])
    | Expr.Eassign assignments ->
        variant1 "Expr.expr_node.Eassign"
          (sequence_map
             (fun (region, field, value) ->
               oproduct
                 [ (fun () ->
                     v3_program_variable_reference state bound region);
                   (fun () -> v3_routine_symbol state field);
                   (fun () ->
                     v3_program_variable_reference state bound value) ])
             assignments)
    | Expr.Elet (definition, body) ->
        let body_bound =
          match definition with
          | Expr.LDvar (variable, _) -> bound @ [variable]
          | Expr.LDsym _ | Expr.LDrec _ -> bound
        in
        variant1 "Expr.expr_node.Elet"
          (oproduct
             [ (fun () -> v3_let_definition state bound definition);
               (fun () -> v3_expression state body_bound body) ])
    | Expr.Eif (condition, consequent, alternative) ->
        variant1 "Expr.expr_node.Eif"
          (oproduct
             [ (fun () -> v3_expression state bound condition);
               (fun () -> v3_expression state bound consequent);
               (fun () -> v3_expression state bound alternative) ])
    | Expr.Ematch (scrutinee, regular, exceptional) ->
        variant1 "Expr.expr_node.Ematch"
          (oproduct
             [ (fun () -> v3_expression state bound scrutinee);
               (fun () ->
                 sequence_map
                   (fun (pattern, body) ->
                     let variables = program_pattern_variables pattern in
                     oproduct
                       [ (fun () -> v3_program_pattern state pattern);
                         (fun () ->
                           v3_expression state (bound @ variables) body) ])
                   regular);
               (fun () ->
                 canonical_map
                   (Ity.Mxs.bindings exceptional
                    |> ordered_map (fun (exception_, (variables, body)) ->
                           let key =
                             v3_exception_symbol state exception_
                           in
                           let value =
                             oproduct
                               [ (fun () ->
                                   sequence_map
                                     (v3_program_binder state variables)
                                     variables);
                                 (fun () ->
                                   v3_expression state
                                     (bound @ variables) body) ]
                           in
                           (key, value)))) ])
    | Expr.Ewhile (condition, invariants, variants, body) ->
        variant1 "Expr.expr_node.Ewhile"
          (oproduct
             [ (fun () -> v3_expression state bound condition);
               (fun () ->
                 sequence_map
                   (v3_term state (bound_program_pure_symbols bound))
                   invariants);
               (fun () ->
                 sequence_map (v3_program_variant state bound) variants);
               (fun () -> v3_expression state bound body) ])
    | Expr.Efor
        (variable, (first, direction, last), internal, invariants, body) ->
        let loop_bound = bound @ [variable; internal] in
        variant1 "Expr.expr_node.Efor"
          (oproduct
             [ (fun () -> v3_program_binder state [variable] variable);
               (fun () ->
                 v3_program_variable_reference state bound first);
               (fun () -> v3_for_direction direction);
               (fun () ->
                 v3_program_variable_reference state bound last);
               (fun () -> v3_program_binder state [internal] internal);
               (fun () ->
                 sequence_map
                   (v3_term state (bound_program_pure_symbols loop_bound))
                   invariants);
               (fun () -> v3_expression state loop_bound body) ])
    | Expr.Eraise (exception_, payload) ->
        variant1 "Expr.expr_node.Eraise"
          (oproduct
             [ (fun () -> v3_exception_symbol state exception_);
               (fun () -> v3_expression state bound payload) ])
    | Expr.Eexn (exception_, body) ->
        variant1 "Expr.expr_node.Eexn"
          (oproduct
             [ (fun () -> v3_exception_symbol state exception_);
               (fun () -> v3_expression state bound body) ])
    | Expr.Eassert (kind, formula) ->
        variant1 "Expr.expr_node.Eassert"
          (oproduct
             [ (fun () -> v3_assertion_kind kind);
               (fun () ->
                 v3_term state (bound_program_pure_symbols bound) formula) ])
    | Expr.Eghost body ->
        variant1 "Expr.expr_node.Eghost"
          (v3_expression state bound body)
    | Expr.Epure term ->
        variant1 "Expr.expr_node.Epure"
          (v3_term state (bound_program_pure_symbols bound) term)
    | Expr.Eabsurd -> variant0 "Expr.expr_node.Eabsurd"
  in
  let info = expression_info expression in
  let expression_record =
    onode "Expr.expr"
      [ (fun () -> expression_node);
        (fun () -> v3_ity state expression.Expr.e_ity);
        (fun () -> v3_program_mask expression.Expr.e_mask);
        (fun () -> v3_effect state bound expression.Expr.e_effect);
        (fun () ->
          v3_attributes state
            (attribute_strings expression.Expr.e_attrs []));
        (fun () ->
          graph_source_span_option state.source expression.Expr.e_loc) ]
  in
  fill Expression index cell
    (oproduct
       [ (fun () -> expression_record);
         (fun () -> origin_value state info) ]);
  reference Expression index

and v3_assertion_kind = function
  | Expr.Assert -> variant0 "Expr.assertion_kind.Assert"
  | Expr.Assume -> variant0 "Expr.assertion_kind.Assume"
  | Expr.Check -> variant0 "Expr.assertion_kind.Check"

and v3_for_direction = function
  | Expr.To -> variant0 "Expr.for_direction.To"
  | Expr.DownTo -> variant0 "Expr.for_direction.DownTo"

let graph_of_expression source expression =
  let state = new_state source in
  finish state [v3_expression state [] expression]

let v3_program_type_declaration state declaration =
  onode "Pdecl.its_defn"
    [ (fun () ->
        v3_program_type_symbol state declaration.Pdecl.itd_its);
      (fun () ->
        sequence_map (v3_routine_symbol state)
          declaration.Pdecl.itd_fields);
      (fun () ->
        sequence_map (v3_routine_symbol state)
          declaration.Pdecl.itd_constructors);
      (fun () ->
        sequence_map (v3_term state [])
          declaration.Pdecl.itd_invariant);
      (fun () ->
        option (v3_expression state [])
          declaration.Pdecl.itd_witness) ]

let v3_program_declaration state declaration =
  let index, cell = reserve state Program_declaration in
  let declaration_node =
    match declaration.Pdecl.pd_node with
    | Pdecl.PDtype declarations ->
        variant1 "Pdecl.pdecl_node.PDtype"
          (sequence_map (v3_program_type_declaration state) declarations)
    | Pdecl.PDpure ->
        variant1 "Pdecl.pdecl_node.PDpure" unit_node
    | Pdecl.PDlet definition ->
        variant1 "Pdecl.pdecl_node.PDlet"
          (v3_let_definition state [] definition)
    | Pdecl.PDexn exception_ ->
        variant1 "Pdecl.pdecl_node.PDexn"
          (v3_exception_symbol state exception_)
  in
  fill Program_declaration index cell
    (onode "Pdecl.pdecl"
       [ (fun () -> declaration_node);
         (fun () ->
           sequence_map (v3_declaration state)
             declaration.Pdecl.pd_pure);
         (fun () ->
           sequence_map
             (fun (meta, arguments) ->
               v3_meta_application state meta arguments)
             declaration.Pdecl.pd_meta) ]);
  reference Program_declaration index

let v3_program_symbol state = function
  | Pmodule.PV variable ->
      variant1 "Pmodule.prog_symbol.PV"
        (v3_program_variable state variable)
  | Pmodule.RS routine ->
      variant1 "Pmodule.prog_symbol.RS"
        (v3_routine_symbol state routine)
  | Pmodule.OO routines ->
      variant1 "Pmodule.prog_symbol.OO"
        (Expr.Srs.elements routines
         |> ordered_map (v3_routine_symbol state)
         |> canonical_set)

let rec v3_program_namespace state namespace =
  onode "Pmodule.namespace"
    [ (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ts
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_program_type_symbol state symbol))));
      (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ps
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_program_symbol state symbol))));
      (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_xs
           |> ordered_map (fun (name, symbol) ->
                  (bytes name, v3_exception_symbol state symbol))));
      (fun () ->
        canonical_map
          (Wstdlib.Mstr.bindings namespace.Pmodule.ns_ns
           |> ordered_map (fun (name, nested) ->
                  (bytes name, v3_program_namespace state nested)))) ]

let rec v3_pmodule state pmodule =
  let key = theory_key pmodule.Pmodule.mod_theory in
  match StringMap.find_opt key state.module_indices with
  | Some index -> reference Module index
  | None ->
      let index, cell = reserve state Module in
      state.module_indices <-
        StringMap.add key index state.module_indices;
      fill Module index cell
        (onode "Pmodule.pmodule"
           [ (fun () -> v3_theory state pmodule.Pmodule.mod_theory);
             (fun () ->
               sequence_map (v3_module_unit state)
                 (v3_module_units state pmodule.Pmodule.mod_units));
             (fun () ->
               v3_program_namespace state pmodule.Pmodule.mod_export) ]);
      reference Module index

and v3_module_units state units =
  if state.omit_generated_vcs then
    List.filter
      (function
        | Pmodule.Udecl declaration ->
            not (is_generated_vc_program_declaration declaration)
        | Pmodule.Uuse _ | Pmodule.Uclone _ | Pmodule.Umeta _
        | Pmodule.Uscope _ -> true)
      units
  else
    units

and v3_module_inst state instance =
  onode "Pmodule.mod_inst"
    [ (fun () -> v3_pmodule state instance.Pmodule.mi_mod);
      (fun () ->
        canonical_map
          (Ty.Mts.bindings instance.Pmodule.mi_ty
           |> ordered_map (fun (source, target) ->
                  (v3_type_symbol state source, v3_ity state target))));
      (fun () ->
        canonical_map
          (Ty.Mts.bindings instance.Pmodule.mi_ts
           |> ordered_map (fun (source, target) ->
                  (v3_type_symbol state source,
                   v3_program_type_symbol state target))));
      (fun () ->
        canonical_map
          (Term.Mls.bindings instance.Pmodule.mi_ls
           |> ordered_map (fun (source, target) ->
                  (v3_logic_symbol state source,
                   v3_logic_symbol state target))));
      (fun () ->
        canonical_map
          (Decl.Mpr.bindings instance.Pmodule.mi_pr
           |> ordered_map (fun (source, target) ->
                  (v3_proposition_symbol state source,
                   v3_proposition_symbol state target))));
      (fun () ->
        canonical_map
          (Decl.Mpr.bindings instance.Pmodule.mi_pk
           |> ordered_map (fun (source, target) ->
                  (v3_proposition_symbol state source,
                   v3_proposition_kind target))));
      (fun () ->
        canonical_map
          (Term.Mvs.bindings instance.Pmodule.mi_pv
           |> ordered_map (fun (source, target) ->
                  (v3_logic_variable state source,
                   v3_program_variable state target))));
      (fun () ->
        canonical_map
          (Expr.Mrs.bindings instance.Pmodule.mi_rs
           |> ordered_map (fun (source, target) ->
                  (v3_routine_symbol state source,
                   v3_routine_symbol state target))));
      (fun () ->
        canonical_map
          (Ity.Mxs.bindings instance.Pmodule.mi_xs
           |> ordered_map (fun (source, target) ->
                  (v3_exception_symbol state source,
                   v3_exception_symbol state target))));
      (fun () -> v3_proposition_kind instance.Pmodule.mi_df) ]

and v3_module_unit state = function
  | Pmodule.Udecl declaration ->
      variant1 "Pmodule.mod_unit.Udecl"
        (v3_program_declaration state declaration)
  | Pmodule.Uuse source ->
      variant1 "Pmodule.mod_unit.Uuse" (v3_pmodule state source)
  | Pmodule.Uclone instance ->
      variant1 "Pmodule.mod_unit.Uclone"
        (v3_module_inst state instance)
  | Pmodule.Umeta (meta, arguments) ->
      variant1 "Pmodule.mod_unit.Umeta"
        (v3_meta_application state meta arguments)
  | Pmodule.Uscope (name, units) ->
      variant1 "Pmodule.mod_unit.Uscope"
        (oproduct
           [ (fun () -> bytes name);
             (fun () ->
               sequence_map (v3_module_unit state)
                 (v3_module_units state units)) ])

let graph_of_program_declaration source declaration =
  let state = new_state source in
  finish state [v3_program_declaration state declaration]

let graph_of_pmodule source pmodule =
  let state = new_state source in
  finish state [v3_pmodule state pmodule]

let graph_of_pre_wp_pmodule source pmodule =
  let state = new_state ~omit_generated_vcs:true source in
  finish state [v3_pmodule state pmodule]

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
  let marker_token = Printf.sprintf "|@why3-reference-id-%d|" ordinal in
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
    if index < length && input.[index] <> '\n' then
      skip_comment (index + 1)
    else
      index
  in
  let rec atom_end index =
    if index < length && not (smt_atom_delimiter input.[index]) then begin
      if input.[index] = '\000' then fail "NUL is not valid in an SMT token";
      atom_end (index + 1)
    end else
      index
  in
  let rec loop index reversed =
    if index >= length then
      List.rev reversed
    else if smt_space input.[index] then
      loop (index + 1) reversed
    else if input.[index] = ';' then
      loop (skip_comment index) reversed
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
    Option.value ~default:Ident.Mid.empty
      (StringMap.find_opt stage !generated)
  in
  match Ident.Mid.find_opt identifier identifiers with
  | Some ordinal -> ordinal
  | None ->
      let ordinal = Ident.Mid.cardinal identifiers in
      generated :=
        StringMap.add stage
          (Ident.Mid.add identifier ordinal identifiers)
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
        begin match
          generated_stage_of_identifier provenance event.identifier
        with
        | None -> event.original_token
        | Some stage ->
            Printf.sprintf "$generated[%s][%d]" stage
              (generated_ordinal generated stage event.identifier)
        end
  in
  let tokens = List.map normalize (lex_smt_tokens output) in
  if StringSet.cardinal !matched <> List.length events then
    fail "not every SMT identifier marker reached the token stream";
  node "SmtTokenStreamV1"
    [`List (List.map (fun token -> `String (hex_string token)) tokens)]

let source_sha256 source = sha256_string source.bytes

let portable_record source fields canonical =
  let canonical_text = canonical_bytes canonical in
  `Assoc
    ([ ("schema", `Int 3);
       ( "semantic_profile_sha256",
         `String Canonical_v3_profile.semantic_profile_sha256 );
       ( "diagnostic_contract_sha256",
         `String Canonical_v3_profile.diagnostic_contract_sha256 );
       ("fixture", `String source.label);
       ("source_sha256", `String (source_sha256 source)) ]
     @ fields
     @ [ ("canonical_sha256", `String (sha256_string canonical_text));
         ("canonical", canonical) ])

let typed_theory_record source theory =
  portable_record source
    [ ("scope", `String "unit");
      ("unit_kind", `String "theory");
      ("unit_name_hex",
       `String (hex_string theory.Theory.th_name.Ident.id_string));
      ("stage", `String "typed-semantic") ]
    (graph_of_theory source theory)

let typed_module_record source pmodule =
  let theory = pmodule.Pmodule.mod_theory in
  portable_record source
    [ ("scope", `String "unit");
      ("unit_kind", `String "module");
      ("unit_name_hex",
       `String (hex_string theory.Theory.th_name.Ident.id_string));
      ("stage", `String "typed-program") ]
    (graph_of_pre_wp_pmodule source pmodule)

let task_record source unit_name goal_name ordinal stage canonical =
  portable_record source
    [ ("scope", `String "goal");
      ("unit_kind", `String "theory");
      ("unit_name_hex", `String (hex_string unit_name));
      ("goal_name_hex", `String (hex_string goal_name));
      ("goal_ordinal", `Int ordinal);
      ("stage", `String stage) ]
    canonical

let raw_task_record source unit_name ordinal task =
  let goal = Task.task_goal task in
  task_record source unit_name goal.Decl.pr_name.Ident.id_string ordinal
    "raw-task" (graph_of_task source task)

let checkpoint_task_record source unit_name goal_name ordinal provenance
    stage task =
  task_record source unit_name goal_name ordinal stage
    (graph_of_checkpoint_task source provenance stage task)

let smt_token_record source unit_name goal_name ordinal provenance events
    output =
  task_record source unit_name goal_name ordinal "smt-tokens"
    (canonical_smt_token_stream provenance events output)

let write_record output value =
  Yojson.Safe.to_channel ~std:true output value;
  output_char output '\n'

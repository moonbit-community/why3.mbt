(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit Z3-profile oracle adapter, modified 2026-07-21.         *)
(*                                                                  *)
(********************************************************************)

open Why3

module StringSet = Set.Make (String)

let fail message =
  prerr_endline ("export_z3_profile: " ^ message);
  exit 1

let required name = function
  | Some value -> value
  | None -> fail (name ^ " is required")

let theory_key theory =
  String.concat "."
    (theory.Theory.th_path @ [theory.Theory.th_name.Ident.id_string])

let split_qualified name =
  match List.rev (String.split_on_char '.' name) with
  | [] -> assert false
  | leaf :: reversed_path -> (List.rev reversed_path, leaf)

let read_theory environment name =
  let path, leaf = split_qualified name in
  Env.read_theory environment path leaf

let json_string value = `String value

let json_int value = `Int value

let locator_json locator =
  `Assoc
    [ ("theoryKey", json_string locator.Canonical_v2.owner);
      ("theoryItemOrdinal", json_int locator.Canonical_v2.item);
      ("declarationInnerOrdinal", json_int locator.Canonical_v2.inner);
      ("symbolKind", json_string locator.Canonical_v2.kind);
      ("digest", json_string locator.Canonical_v2.digest) ]

let type_key catalog symbol =
  match Ty.Mts.find_opt symbol catalog.Canonical_v2.type_locations with
  | Some locator -> locator_json locator
  | None -> fail ("uncatalogued type symbol " ^ symbol.Ty.ts_name.Ident.id_string)

let logic_key catalog symbol =
  match Term.Mls.find_opt symbol catalog.Canonical_v2.logic_locations with
  | Some locator -> locator_json locator
  | None -> fail ("uncatalogued logic symbol " ^ symbol.Term.ls_name.Ident.id_string)

let proposition_key catalog symbol =
  match Decl.Mpr.find_opt symbol catalog.Canonical_v2.proposition_locations with
  | Some locator -> locator_json locator
  | None ->
      fail
        ("uncatalogued proposition symbol "
         ^ symbol.Decl.pr_name.Ident.id_string)

let rec type_json catalog ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar variable ->
      `Assoc
        [ ("kind", json_string "variable");
          ("name", json_string variable.Ty.tv_name.Ident.id_string) ]
  | Ty.Tyapp (symbol, arguments) ->
      `Assoc
        [ ("kind", json_string "application");
          ("symbol", type_key catalog symbol);
          ("arguments", `List (List.map (type_json catalog) arguments)) ]

let meta_argument_json catalog = function
  | Theory.MAty ty ->
      `Assoc [ ("kind", json_string "type"); ("value", type_json catalog ty) ]
  | Theory.MAts symbol ->
      `Assoc
        [ ("kind", json_string "typeSymbol");
          ("value", type_key catalog symbol) ]
  | Theory.MAls symbol ->
      `Assoc
        [ ("kind", json_string "logicSymbol");
          ("value", logic_key catalog symbol) ]
  | Theory.MApr symbol ->
      `Assoc
        [ ("kind", json_string "propositionSymbol");
          ("value", proposition_key catalog symbol) ]
  | Theory.MAstr value ->
      `Assoc [ ("kind", json_string "string"); ("value", json_string value) ]
  | Theory.MAint value ->
      `Assoc [ ("kind", json_string "integer"); ("value", json_int value) ]
  | Theory.MAid ident ->
      `Assoc
        [ ("kind", json_string "identifier");
          ("name", json_string ident.Ident.id_string) ]

let meta_tdecl_json catalog ordinal tdecl =
  match tdecl.Theory.td_node with
  | Theory.Meta (meta, arguments) ->
      `Assoc
        [ ("ordinal", json_int ordinal);
          ("name", json_string meta.Theory.meta_name);
          ("arguments", `List (List.map (meta_argument_json catalog) arguments)) ]
  | Theory.Decl _ | Theory.Use _ | Theory.Clone _ ->
      fail "driver meta map contains a non-meta theory declaration"

let answer_json = function
  | Call_provers.Valid -> `Assoc [ ("kind", json_string "valid") ]
  | Call_provers.Invalid -> `Assoc [ ("kind", json_string "invalid") ]
  | Call_provers.Timeout -> `Assoc [ ("kind", json_string "timeout") ]
  | Call_provers.OutOfMemory -> `Assoc [ ("kind", json_string "outOfMemory") ]
  | Call_provers.StepLimitExceeded ->
      `Assoc [ ("kind", json_string "stepLimitExceeded") ]
  | Call_provers.Unknown message ->
      `Assoc
        [ ("kind", json_string "unknown");
          ("message", json_string message) ]
  | Call_provers.Failure message ->
      `Assoc
        [ ("kind", json_string "failure");
          ("message", json_string message) ]
  | Call_provers.HighFailure -> `Assoc [ ("kind", json_string "highFailure") ]

let snapshot_meta_names =
  StringSet.of_list
    [ "remove_unused:dependency";
      "remove_unused:remove_constant";
      "remove_unused:keep" ]

let snapshot_theories environment snapshot =
  let open Canonical_v2 in
  json_member "theories" snapshot
  |> json_list
  |> List.map (fun value -> json_string (json_member "key" value))
  |> List.map (read_theory environment)

let snapshot_meta_closure catalog theories =
  theories
  |> List.fold_left
       (fun result theory ->
         let selected =
           theory.Theory.th_decls
           |> List.filter_map (fun tdecl ->
                  match tdecl.Theory.td_node with
                  | Theory.Meta (meta, _) when
                      StringSet.mem meta.Theory.meta_name snapshot_meta_names ->
                      Some tdecl
                  | Theory.Meta _ | Theory.Decl _ | Theory.Use _ | Theory.Clone _ ->
                      None)
         in
         if selected = [] then result
         else
           `Assoc
             [ ("theoryKey", json_string (theory_key theory));
               ("entries", `List (List.mapi (meta_tdecl_json catalog) selected)) ]
           :: result)
       []
  |> List.rev

let theory_for_ident theories ident =
  match
    List.find_opt
      (fun theory -> Ident.id_equal theory.Theory.th_name ident)
      theories
  with
  | Some theory -> theory
  | None -> fail ("profile references uncatalogued theory " ^ ident.Ident.id_string)

let () =
  let stdlib = ref None in
  let snapshot_path = ref None in
  let root_driver = ref "z3_487.drv" in
  Arg.parse
    [ ("--stdlib", Arg.String (fun value -> stdlib := Some value), "PATH");
      ("--snapshot", Arg.String (fun value -> snapshot_path := Some value), "PATH");
      ("--driver", Arg.String (fun value -> root_driver := value), "NAME") ]
    (fun value -> fail ("unexpected argument " ^ value))
    "export_z3_profile --stdlib PATH --snapshot JSON";
  let stdlib = Unix.realpath (required "--stdlib" !stdlib) in
  let snapshot_path = Unix.realpath (required "--snapshot" !snapshot_path) in
  let environment = Env.create_env [stdlib] in
  let catalog = Canonical_v2.load_catalog environment snapshot_path in
  let snapshot = Yojson.Safe.from_file snapshot_path in
  let theories = snapshot_theories environment snapshot in
  let config = Whyconf.init_config None in
  let main = Whyconf.get_main config in
  let driver =
    Driver.load_driver_file_and_extras main environment ~extra_dir:None
      !root_driver []
  in
  let profile = Driver.oracle_profile_view driver in
  let meta_groups =
    List.map
      (fun (theory, declarations) ->
        `Assoc
          [ ("theoryKey", json_string (theory_key theory));
            ("entries", `List (List.mapi (meta_tdecl_json catalog) declarations)) ])
      profile.Driver.oracle_metas
  in
  let prelude_groups =
    List.map
      (fun (ident, values) ->
        let theory = theory_for_ident theories ident in
        `Assoc
          [ ("theoryKey", json_string (theory_key theory));
            ("values", `List (List.map json_string values)) ])
      profile.Driver.oracle_theory_preludes
  in
  let use_groups =
    List.map
      (fun (source, export) ->
        let uses =
          export.Theory.th_decls
          |> List.filter_map (fun declaration ->
                 match declaration.Theory.td_node with
                 | Theory.Use theory -> Some (json_string (theory_key theory))
                 | Theory.Decl _ | Theory.Clone _ | Theory.Meta _ -> None)
        in
        `Assoc
          [ ("theoryKey", json_string (theory_key source));
            ("uses", `List uses) ])
      profile.Driver.oracle_theory_uses
  in
  let result_regexps =
    List.map
      (fun (pattern, answer) ->
        `Assoc
          [ ("pattern", json_string pattern);
            ("answer", answer_json answer) ])
      profile.Driver.oracle_result_parser.Call_provers.prp_regexps
  in
  let result_exit_codes =
    List.map
      (fun (code, answer) ->
        `Assoc [ ("code", json_int code); ("answer", answer_json answer) ])
      profile.Driver.oracle_result_parser.Call_provers.prp_exitcodes
  in
  let output =
    `Assoc
      [ ("schemaVersion", json_int 1);
        ("driverProfile", json_string "z3_487");
        ("rootDriver", json_string !root_driver);
        ("printer", json_string (required "printer" profile.Driver.oracle_printer));
        ("filename", json_string (required "filename" profile.Driver.oracle_filename));
        ("transforms", `List (List.map json_string profile.Driver.oracle_transforms));
        ("preludes", `List (List.map json_string profile.Driver.oracle_preludes));
        ("theoryPreludes", `List prelude_groups);
        ("theoryUses", `List use_groups);
        ("driverMetaGroups", `List meta_groups);
        ("snapshotMetaClosure", `List (snapshot_meta_closure catalog theories));
        ("resultRegexps", `List result_regexps);
        ("resultExitCodes", `List result_exit_codes);
        ("blacklist", `List (List.map json_string profile.Driver.oracle_blacklist)) ]
  in
  Yojson.Safe.to_channel ~std:true stdout output;
  output_char stdout '\n'

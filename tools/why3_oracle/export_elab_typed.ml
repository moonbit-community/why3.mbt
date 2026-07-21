(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit typed-semantic oracle adapter, modified 2026-07-22.      *)
(*                                                                  *)
(********************************************************************)

open Why3

let fail message =
  prerr_endline ("export_elab_typed: " ^ message);
  exit 1

let required name = function
  | Some value -> value
  | None -> fail (name ^ " is required")

let () =
  let stdlib = ref None in
  let snapshot = ref None in
  let fixture = ref None in
  let file = ref None in
  let theories = ref [] in
  let program_modules = ref [] in
  Arg.parse
    [ ("--stdlib", Arg.String (fun value -> stdlib := Some value), "PATH");
      ("--snapshot", Arg.String (fun value -> snapshot := Some value), "PATH");
      ("--fixture", Arg.String (fun value -> fixture := Some value), "PATH");
      ("--file", Arg.String (fun value -> file := Some value), "PATH");
      ("--unit", Arg.String (fun value -> theories := value :: !theories), "NAME");
      ("--module", Arg.String (fun value -> program_modules := value :: !program_modules), "NAME") ]
    (fun value -> fail ("unexpected argument " ^ value))
    "export_elab_typed --stdlib PATH --snapshot JSON --fixture LABEL --file PATH --unit NAME... --module NAME...";
  let stdlib = required "--stdlib" !stdlib in
  let snapshot = required "--snapshot" !snapshot in
  let fixture = required "--fixture" !fixture in
  let file = required "--file" !file in
  let theories = List.rev !theories in
  let program_modules = List.rev !program_modules in
  if theories = [] && program_modules = [] then
    fail "at least one --unit or --module is required";
  let environment = Env.create_env [stdlib; Filename.dirname file] in
  let catalog = Canonical_v2.load_catalog environment snapshot in
  let source = Canonical_v2.read_source fixture file in
  let modules, _ = Env.read_file Pmodule.mlw_language environment file in
  List.iter
    (fun name ->
      let pmodule =
        match Wstdlib.Mstr.find_opt name modules with
        | Some value -> value
        | None -> fail ("typed file has no unit " ^ name)
      in
      Canonical_v2.write_record stdout
        (Canonical_v2.typed_theory_record catalog source
           pmodule.Pmodule.mod_theory))
    theories;
  List.iter
    (fun name ->
      let pmodule =
        match Wstdlib.Mstr.find_opt name modules with
        | Some value -> value
        | None -> fail ("typed file has no program module " ^ name)
      in
      Canonical_v2.write_record stdout
        (Canonical_v2.typed_module_record catalog source pmodule))
    program_modules

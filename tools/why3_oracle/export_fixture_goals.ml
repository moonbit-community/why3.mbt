(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit fixture inventory adapter, modified 2026-07-21.         *)
(*                                                                  *)
(********************************************************************)

open Why3

let fail message =
  prerr_endline ("export_fixture_goals: " ^ message);
  exit 1

let write_hex value =
  String.iter (fun character -> Printf.printf "%02x" (Char.code character)) value

let write_field value =
  write_hex value;
  print_char '\t'

let write_unit unit_name pmodule =
  let theory = pmodule.Pmodule.mod_theory in
  let tasks = Task.split_theory theory None None in
  List.iteri
    (fun ordinal task ->
      let goal = Task.task_goal task in
      write_field unit_name;
      Printf.printf "%d\t" ordinal;
      write_hex goal.Decl.pr_name.Ident.id_string;
      print_newline ())
    tasks;
  if tasks = [] then begin
    write_field unit_name;
    print_endline "-\t-"
  end

let () =
  match Array.to_list Sys.argv with
  | [_program; stdlib; file] ->
      let environment = Env.create_env [stdlib; Filename.dirname file] in
      let modules, _format =
        Env.read_file Pmodule.mlw_language environment file
      in
      Wstdlib.Mstr.iter write_unit modules
  | _ -> fail "usage: export_fixture_goals STDLIB FILE"

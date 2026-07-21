(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                            *)
(*                                                                  *)
(*  MoonBit SMT token oracle adapter, modified 2026-07-21.          *)
(*                                                                  *)
(********************************************************************)

open Why3

let fail message =
  prerr_endline ("export_smt_trace: " ^ message);
  exit 1

let required name = function
  | Some value -> value
  | None -> fail (name ^ " is required")

let selected_unit modules name =
  match Wstdlib.Mstr.find_opt name modules with
  | Some value -> value
  | None -> fail ("typed file has no unit " ^ name)

let print_with_identifier_markers driver provenance prepared =
  let output = Buffer.create 65536 in
  let formatter = Format.formatter_of_buffer output in
  let ordinal = ref 0 in
  let events_reversed = ref [] in
  let rewrite candidate identifier original =
    if candidate != formatter then original
    else begin
      let event, marker =
        Canonical_v2.smt_identifier_event !ordinal identifier original
      in
      incr ordinal;
      events_reversed := event :: !events_reversed;
      marker
    end
  in
  ignore
    (Ident.with_clone_observer
       (Canonical_v2.observe_identifier_clone provenance)
       (fun () ->
         Smtv2.with_identifier_rewriter rewrite (fun () ->
           Driver.print_task_prepared driver formatter prepared)));
  Format.pp_print_flush formatter ();
  (List.rev !events_reversed, Buffer.contents output)

let () =
  let why3_root = ref None in
  let snapshot = ref None in
  let fixture = ref None in
  let file = ref None in
  let root_driver = ref "z3_487.drv" in
  let units = ref [] in
  Arg.parse
    [ ("--why3-root", Arg.String (fun value -> why3_root := Some value), "PATH");
      ("--snapshot", Arg.String (fun value -> snapshot := Some value), "PATH");
      ("--fixture", Arg.String (fun value -> fixture := Some value), "PATH");
      ("--file", Arg.String (fun value -> file := Some value), "PATH");
      ("--driver", Arg.String (fun value -> root_driver := value), "NAME");
      ("--unit", Arg.String (fun value -> units := value :: !units), "NAME") ]
    (fun value -> fail ("unexpected argument " ^ value))
    "export_smt_trace --why3-root PATH --snapshot JSON --fixture LABEL --file PATH --unit NAME...";
  let why3_root = Unix.realpath (required "--why3-root" !why3_root) in
  let stdlib = Filename.concat why3_root "stdlib" in
  let snapshot = Unix.realpath (required "--snapshot" !snapshot) in
  let fixture = required "--fixture" !fixture in
  let file = Unix.realpath (required "--file" !file) in
  let units = List.rev !units in
  if units = [] then fail "at least one --unit is required";
  let environment = Env.create_env [stdlib; Filename.dirname file] in
  let catalog = Canonical_v2.load_catalog environment snapshot in
  let source = Canonical_v2.read_source fixture file in
  let modules, _ = Env.read_file Pmodule.mlw_language environment file in
  let config = Whyconf.init_config None in
  let main =
    Whyconf.get_main config
    |> fun main -> Whyconf.set_datadir main why3_root
  in
  let driver =
    Driver.load_driver_file_and_extras main environment ~extra_dir:None
      !root_driver []
  in
  List.iter
    (fun name ->
      let theory = (selected_unit modules name).Pmodule.mod_theory in
      Task.split_theory theory None None
      |> List.iteri (fun ordinal raw_task ->
             let raw_goal = Task.task_goal raw_task in
             let goal_name = raw_goal.Decl.pr_name.Ident.id_string in
             let provenance =
               Canonical_v2.task_trace_provenance catalog source raw_task
             in
             let trace stage task =
               ignore
                 (Canonical_v2.canonical_checkpoint_task catalog source
                    provenance stage task)
             in
             let prepared =
               Ident.with_clone_observer
                 (Canonical_v2.observe_identifier_clone provenance)
                 (fun () ->
                   Driver.prepare_task_trace trace driver raw_task)
             in
             let ordinary = Driver.prepare_task driver raw_task in
             if not (Task.task_equal prepared ordinary) then
               fail
                 (Printf.sprintf
                    "%s goal %d: traced prepare_task changed the final Task"
                    name ordinal);
             let events, output =
               print_with_identifier_markers driver provenance prepared
             in
             Canonical_v2.write_record stdout
               (Canonical_v2.smt_token_record source name goal_name ordinal
                  provenance events output)))
    units

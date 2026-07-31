(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception   *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(*  MoonBit lossless WhyML reference adapter, modified 2026-07-24.  *)
(*                                                                  *)
(********************************************************************)

open Why3

let fail message =
  prerr_endline ("export_full_mlw: " ^ message);
  exit 1

let required name = function
  | Some value -> value
  | None -> fail (name ^ " is required")

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

let parse_full_file file =
  let channel = open_in_bin file in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () ->
      let lexbuf = Lexing.from_channel channel in
      Loc.set_file file lexbuf;
      Lexer.parse_full_mlw_file lexbuf)

let category_name = function
  | Ptree.FullSyntax -> "Syntax"
  | Ptree.FullNestedModule -> "NestedUnit"
  | Ptree.FullUnsupportedEpsilon -> "UnsupportedConcreteSyntax"

let output_accepted () =
  print_endline {|{"schema":1,"accepted":true}|}

let read_file file =
  let channel = open_in_bin file in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let source_offset source line column =
  let rec find_line index current_line =
    if current_line = line then index + column
    else if index >= String.length source then
      fail (Printf.sprintf "source has no line %d" line)
    else if source.[index] = '\n' then find_line (index + 1) (current_line + 1)
    else find_line (index + 1) current_line
  in
  find_line 0 1

let output_rejected relative_path source category location =
  let location_fields =
    match location with
    | None ->
        {|null,"end_byte":null,"start_line":null,"start_column":null,|}
        ^ {|"end_line":null,"end_column":null|}
    | Some position ->
        let _, start_line, start_column, end_line, end_column =
          Loc.get position
        in
        Printf.sprintf
          "%d,\"end_byte\":%d,\"start_line\":%d,\"start_column\":%d,"
          (source_offset source start_line start_column)
          (source_offset source end_line end_column)
          start_line start_column
        ^ Printf.sprintf
            "\"end_line\":%d,\"end_column\":%d"
            end_line end_column
  in
  Printf.printf
    {|{"schema":1,"accepted":false,"stage":"parsing","severity":"error",|}
  ;
  Printf.printf
    {|"category":"%s","warning_code":null,"relative_path_hex":"%s",|}
    (category_name category) (hex_string relative_path);
  Printf.printf "\"start_byte\":%s}\n" location_fields

let rec output_parse_exception relative_path source location exception_ =
  match exception_ with
  | Loc.Located (nested_location, nested) ->
      output_parse_exception relative_path source (Some nested_location) nested
  | exception_ ->
      begin match Lexer.classify_full_parse_error exception_ with
      | Some category ->
          output_rejected relative_path source category location
      | None -> raise exception_
      end

let () =
  let stdlib = ref None in
  let file = ref None in
  let relative_path = ref None in
  let diagnostic = ref false in
  let canonical_v3 = ref false in
  Arg.parse
    [ ("--stdlib", Arg.String (fun value -> stdlib := Some value), "PATH");
      ("--file", Arg.String (fun value -> file := Some value), "PATH");
      ( "--relative-path",
        Arg.String (fun value -> relative_path := Some value),
        "PATH" );
      ("--diagnostic", Arg.Set diagnostic, "");
      ("--canonical-v3", Arg.Set canonical_v3, "") ]
    (fun value -> fail ("unexpected argument " ^ value))
    "export_full_mlw \
     [(--diagnostic|--canonical-v3) --relative-path PATH] \
     [--stdlib PATH] --file PATH";
  let file = required "--file" !file in
  if !diagnostic && !canonical_v3 then
    fail "--diagnostic and --canonical-v3 are mutually exclusive";
  if !diagnostic then begin
    let relative_path = required "--relative-path" !relative_path in
    let source = read_file file in
    try
      ignore (parse_full_file file);
      output_accepted ()
    with exception_ ->
      output_parse_exception relative_path source None exception_
  end else if !canonical_v3 then begin
    let relative_path = required "--relative-path" !relative_path in
    let source = Canonical_v3.read_source relative_path file in
    let parsed = parse_full_file file in
    print_string
      (Canonical_v3.canonical_bytes
         (Canonical_v3.surface_file_record source parsed))
  end else begin
    let stdlib = required "--stdlib" !stdlib in
    let parsed = parse_full_file file in
    let environment = Env.create_env [stdlib; Filename.dirname file] in
    ignore (Env.read_file Pmodule.mlw_language environment file);
    Mysexplib.output Format.std_formatter (Ptree.sexp_of_full_mlw_file parsed)
  end

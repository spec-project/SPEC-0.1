(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2006 David Baelde, Alwen Tiu, Axelle Ziegler          *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

exception Invalid_command
exception Assertion_failed

let welcome_msg =
  "Bedwyr welcomes you.

This software is under GNU Public License.
Copyright (c) 2005-2011 Slimmer project.

For a little help, type #help.
\n"

let usage_msg =
  "Bedwyr prover (version 1.1-alt).
This software is under GNU Public License.
Copyright (c) 2005-2011 Slimmer project.

Usage: bedwyr [filename | option]*
"

let help_msg =
  "Useful commands in query mode:
#help.                               Display this message.
#exit.                               Exit.
#debug [flag].                       Turn debugging on/off (flag=on/off).
#time [flag].                        Turn timing on/off (flag=on/off).
#session \"file_1\" ... \"file_N\".      Load these files as the current \
session.
#reload.                             Reload the current session.
#reset.                              Clears the current session.
#show_table [pred].                  Displays the predicate's table.
#save_table [pred] [file].           Save the predicate's table in a file. 
Or type in a formula to ask for its verification.
For more information (including commands relevant in definition mode),
see the user guide.

"

let interactive = ref true
let test        = ref false
let session     = ref []
let queries     = ref []
let inclfiles   = ref []

let _ =
  Arg.parse [
      "-I", Arg.Clear interactive,
      "Do not enter interactive mode." ;

      "-t", Arg.Set test, "Run tests in definition files." ;

      "-e", Arg.String (fun s -> queries := s::!queries),
      "Execute query."
    ]
    (fun f -> session := f::!session)
    usage_msg

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      Format.sprintf ": file %s, line %d, character %d" file line char

let do_cleanup f x clean =
  try f x ; clean () with e -> clean () ; raise e

let process_spi ?(interactive=false) parse lexbuf =
  try while true do try
    let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
    in
    begin match parse Spilexer.token lexbuf with
      | Spi.Def (agent, n, b) -> 
           Spi.add_spi_sig agent n ; 
           System.add_clause (System.Normal) (Spi.Process.agent_def) 2 b
      | Spi.Query a       -> do_cleanup Prover.simple_toplevel_prove a reset
      | Spi.Command (c,a) -> ()
    end 
  with
    | Failure "eof" as e -> raise e
    | Parsing.Parse_error ->
        Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Failure "lexing: empty token" ->
        Format.printf "Lexing error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Assertion_failed ->
        Format.printf "Assertion failed%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Spi.Duplicate_agent_def m ->
        Format.printf "Agent %s was already defined!\n" m ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Spi.Sig_mismatch (m,n) ->
        Format.printf "Agent %s with arity %d was not defined! \n" m n ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | e when not interactive ->
        Format.printf "Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        raise e
  done with
  | Failure "eof" -> ()

let input_spi_defs lexbuf = process_spi Spiparser.input_def lexbuf 

let input_from_spi_file file = 
  let cwd = Sys.getcwd () in
  let f = open_in file in 
  let lexbuf = Lexing.from_channel f in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = file } ;
    input_spi_defs lexbuf ;
    close_in f ; 
    Sys.chdir cwd



let rec process ?(interactive=false) parse lexbuf =
  try while true do try
    let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
    in
    if interactive then Format.printf "?= %!" ;
    begin match parse Lexer.token lexbuf with
      | System.Def (k,h,a,b) -> System.add_clause k h a b
      | System.Query a       -> do_cleanup Prover.toplevel_prove a reset
      | System.Command (c,a) ->
          if not (List.mem c ["include";"reset";"reload";"session"]) then
            do_cleanup (command lexbuf) (c,a) reset
          else
            command lexbuf (c,a)
    end ;
    if interactive then flush stdout
  with
    | Failure "eof" as e -> raise e
    | Parsing.Parse_error ->
        Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
        if not interactive then exit 1;
    | Failure "lexing: empty token" ->
        Format.printf "Lexing error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Assertion_failed ->
        Format.printf "Assertion failed%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | e when not interactive ->
        Format.printf "Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
    | System.Undefined s ->
        Format.printf "No definition found for %a !\n%!" Pprint.pp_term s
    | System.Inconsistent_definition s ->
        Format.printf "Inconsistent extension of definition %a !\n"
          Pprint.pp_term s
    | System.Arity_mismatch (s,a) ->
        Format.printf "Definition %a doesn't have arity %d !\n%!"
          Pprint.pp_term s a
    | System.Interrupt ->
        Format.printf "User interruption.\n%!"
    | Prover.Level_inconsistency ->
        Format.printf "This formula cannot be handled by the left prover!\n%!"
    | Prover.Abort_search ->
       Format.printf "Proof search aborted!\n"
    | Unify.NotLLambda t ->
        Format.printf "Not LLambda unification encountered: %a\n%!"
          Pprint.pp_term t
    | Invalid_command ->
        Format.printf "Invalid command, or wrong arity!\n%!"
    | Failure s ->
        Format.printf "Error: %s\n" s
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        raise e
  done with
  | Failure "eof" -> ()

and input_from_file file =
  let cwd = Sys.getcwd () in
  let lexbuf = Lexing.from_channel (open_in file) in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = file } ;
    input_defs lexbuf ;
    Sys.chdir cwd
and input_defs lexbuf = process Parser.input_def lexbuf
and input_queries ?(interactive=false) lexbuf =
  process ~interactive Parser.input_query lexbuf


and load_session () =
  System.reset_defs () ;
  inclfiles := [] ;
  List.iter input_from_file !session

and command lexbuf = function
  | "exit",[] -> System.close_all_files () ; exit 0
  | "help",[] -> Format.printf "%s" help_msg

  (* Session management *)
  | "include",[f] ->
      let f = Term.get_name f in
      let not_included fname = 
          if (List.mem fname !inclfiles) then
             false
          else (
             inclfiles := fname :: !inclfiles ;
             true
          )
       in
        if not_included f then input_from_file f else () 
        

  | "reset",[] -> inclfiles := [] ; session := [] ; load_session ()
  | "reload",[] -> load_session ()
  | "session",l ->
      session := List.map Term.get_name l ;
      load_session ()

  (* AT: Turn trace printing on/off. This only sets the flag. The actual trace printing
     is up to the program. The value of this flag can be queried by a program via
     the predicate _trace. *)
  | "trace",[] -> System.trace := true
  | "trace",[d] ->
      System.trace :=
        begin match Term.observe d with
          | Term.Var v when v==System.Logic.var_on -> true
          | Term.Var v when v==System.Logic.var_truth -> true
          | Term.Var v when v==System.Logic.var_off -> false
          | Term.Var v when v==System.Logic.var_falsity -> false
          | _ -> raise Invalid_command
        end


  (* Turn debugging on/off. *)
  | "debug",[] -> System.debug := true
  | "debug",[d] ->
      System.debug :=
        begin match Term.observe d with
          | Term.Var v when v==System.Logic.var_on -> true
          | Term.Var v when v==System.Logic.var_truth -> true
          | Term.Var v when v==System.Logic.var_off -> false
          | Term.Var v when v==System.Logic.var_falsity -> false
          | _ -> raise Invalid_command
        end

  (* Turn timing on/off. *)
  | "time",[d] ->
      System.time :=
        begin match Term.observe d with
          | Term.Var v when v==System.Logic.var_on -> true
          | Term.Var v when v==System.Logic.var_truth -> true
          | Term.Var v when v==System.Logic.var_off -> false
          | Term.Var v when v==System.Logic.var_falsity -> false
          | _ -> raise Invalid_command
        end

  (* Tabling-related commands *)
  | "show_table",[p] ->
      System.show_table p
  | "clear_tables",[] ->
      Hashtbl.iter
        (fun k v -> match v with
           | (_,_,Some t) -> Table.reset t
           | _ -> ())
        System.defs
  | "clear_table",[p] ->
      begin match
        try
          let _,_,x = Hashtbl.find System.defs (Term.get_var p) in x
        with _ -> None
      with
        | Some t ->
            Table.reset t
        | None -> 
            Format.printf "Table not found.\n"
      end

  (* AT: save a table to a file *)
   | "save_table",[p;f] -> 
      let f = Term.get_name f in
          System.save_table p f  

  (* AT: read a spi definition file *)
   | "load_spi",[f] ->
     let fname = Term.get_name f in 
       ( 
         input_from_spi_file fname
       )

  (* Testing commands *)
  | "assert",[query] ->
      if !test then begin
        Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@\n%!"
          Pprint.pp_term query ;
        Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
          ~success:(fun _ _ -> ()) ~failure:(fun () -> raise Assertion_failed)
      end
  | "assert_not",[query] ->
      if !test then begin
        Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@\n%!"
          Pprint.pp_term query ;
        Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
          ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
      end
  | "assert_raise",[query] ->
      if !test then begin
        Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@\n%!"
          Pprint.pp_term query ;
        if
          try
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:(fun _ _ -> ()) ~failure:ignore ;
            true
          with _ -> false
        then raise Assertion_failed
      end

  (* Experimental command, only taken into account in bedwyr programs
   * performing static analysis on .def files. *)
  | "type",_ -> ()

  | _ -> raise Invalid_command

let _ =
  load_session () ;
  List.iter (fun s -> input_queries (Lexing.from_string s)) !queries ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end

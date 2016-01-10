(****************************************************************************)
(* SPEC                                                                     *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
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
exception Read_def_failed 
exception Def_file_missing

let welcome_msg =
  "SPEC: An equivalence checker for the spi-calculus. 

Version 0.1

This software is under GNU Public License.
Copyright (c) 2011 Alwen Tiu

\n"

let usage_msg =
  "SPEC.  
This software is under GNU Public License.
Copyright (c) 2011 Alwen Tiu. 

Usage: spec [filename]*
"

let help_msg =
  "List of commands: 
#help;                               Display this message.
#exit;                               Exit.
#load [file];                        Load a process definition file.
#reset;                              Clears the current session. 
#show_bisim;                         Displays the current bisimulation set. 
#save_bisim [file];                  Save the bisimulation set to a file. 
#save_bisim_latex [file];            Save the current bisimulation set to a file in the LaTeX format. 
#save_bisim_raw [file];              Save the current bisimulation set in the internal Bedwyr syntax. 
#show_def [name]                     Show the definition for an agent. 
#show_defs;                          Show all the definitions. 
#time [on/off]                       Show/hide the execution time of a query.
"

let interactive = ref true
let queries     = ref []
let inclfiles   = ref []

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

let clean_tables () = 
      Hashtbl.iter
        (fun k v -> match v with
           | (_,_,Some t) -> Table.reset t
           | _ -> ())
        System.defs


let count_bisim = (fun () -> 
      try
        let _,_,table = Hashtbl.find System.defs (Spi.Process.var_bisim) in
        begin 
         match table with
         | Some table ->              
             Spi.bisim_size table
         | None -> 
             failwith ("No bisimulation set found!\n")
        end
        with
         | Not_found -> raise (System.Undefined (Spi.Process.bisim))
      )

let prove_bisim a = 
  let t0 = Unix.gettimeofday () in 
  let time =
      (fun () ->
         if !System.time then
           Format.printf "Running time: + %.0fs\n" (Unix.gettimeofday () -. t0))
  in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> 
         time () ;
         found := true ;
         Printf.printf "\nThe two processes are bisimilar.\n" ;
         Printf.printf "Size of bisimulation set: %d.  " (count_bisim ()) ;
         Printf.printf "Use #show_bisim to show the set.\n"
    )
  in    
  let failure = (fun () -> 
       time () ; 
       if not !found then Printf.printf "\nThe two processes are not bisimilar.\n"
     ) 
  in 
     do_cleanup (Prover.custom_toplevel_prove success failure) a reset

let prove_show_def a = 
  let query = Term.app (Spi.Process.cmd_show_def) [a] in 
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> found := true) in    
  let failure = (fun () -> 
       if not !found then Printf.printf "\nNo definition found for %s.\n" (Term.get_name a)
     ) 
  in 
     do_cleanup (Prover.custom_toplevel_prove success failure) query reset
  
let prove_show_defs () =
  let q = Char.escaped '"' in 
  List.iter (fun (a,n) -> prove_show_def (Term.string (q^a^q))) (List.rev !Spi.spi_sig)
  

(* [show_bisim] 
   NOTE: we need to find out the (local) timestamps of the entries in the table. 
   This is because we use a bedwyr program to print (instead of doing it inside
   ocaml), so we need to feed the correct timestamp to the prover. 
*) 

let show_bisim_query n g = 
    Term.app Spi.Process.cmd_show_bisim [Term.string (string_of_int n) ; g] 

let save_bisim_query f n g = 
    Term.app Spi.Process.cmd_save_bisim [f ; Term.string (string_of_int n) ; g] 

let save_bisim_latex_query f n g = 
    Term.app Spi.Process.cmd_save_bisim_latex [f ; g] 

let save_latex_header fout =
  Printf.fprintf fout "\\documentclass{article}\n"; 
  Printf.fprintf fout "\\usepackage[margin=2cm]{geometry}\n"; 
  Printf.fprintf fout "\\begin{document} \n" ;
  Printf.fprintf fout "\\begin{enumerate} \n" 

let save_latex_footer fout =
  Printf.fprintf fout "\\end{enumerate}\n";
  Printf.fprintf fout "\\end{document} \n" 

let show_bisim query table  = 
  let s = (fun ts k -> ()) in
  let f = (fun () -> ()) in 
  let prv x y g = 
      Prover.prove ~level:Prover.One ~local:x
                   g
                   ~timestamp:y ~success:s ~failure:f 
  in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let i = ref 1 in 
  Table.iter_fun table 
    (fun t tag -> 
      let r = Norm.deep_norm (Term.app t [Spi.Process.bisim]) in 
      match tag with
      | Table.Proved -> 
          let (ts,lts) = Spi.get_timestamps r in 
          do_cleanup (prv (lts) (ts)) (query !i r) reset;
          i := !i + 1
      | _ -> ()
    )


let do_query a = 
    let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
    in
     do_cleanup Prover.simple_toplevel_prove a reset

let check_def a =
  let q = Char.escaped '"' in 
  let a = Term.string (q^a^q) in 
  let query = Term.app (Term.atom "check_def") [a] in
  let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
  in
  let found = ref false in
  let success = (fun s k -> found := true)  in    
  let failure = (fun () -> 
       if not !found then Printf.printf "Query failed.\n"
     ) 
  in 
     do_cleanup (Prover.custom_toplevel_prove success failure) query reset

let rec process_spi ?(interactive=false) parse lexbuf =
  try while true do try
    if interactive then Format.printf "SPEC> %!" ;
    begin match parse Spilexer.token lexbuf with
      | Spi.Def (agent, n, b) -> 
           Spi.add_spi_sig agent n ; 
           System.add_clause (System.Normal) (Spi.Process.agent_def) 2 b ;
           check_def agent 
      | Spi.Query a       -> clean_tables () ; prove_bisim a
      | Spi.Command (c,a) -> command lexbuf (c,a)
    end ;
    if interactive then flush stdout
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
    | Spi.Duplicate_agent_def m  ->
        Format.printf "Agent %s was already defined!\n" m ;
        if interactive then Lexing.flush_input lexbuf else raise Read_def_failed
    | Spi.Sig_mismatch (m,n) ->
        Format.printf "Agent %s with arity %d was not defined! \n" m n ;
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

and input_from_spi_file file = 
 let num_def = List.length !Spi.spi_sig in
 let cwd = Sys.getcwd () in
 let f = open_in file in 
 let lexbuf = Lexing.from_channel f in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = file } ;
    (
     try 
      input_spi_defs lexbuf 
     with Read_def_failed -> Printf.printf "File loading aborted\n"
    );
    close_in f ; 
    Sys.chdir cwd ;
    Printf.printf "%d process definition(s) read. Use #show_defs to show all definitions\n" 
                  (List.length !Spi.spi_sig - num_def)

and input_spi_defs lexbuf = process_spi Spiparser.input_def lexbuf 
and input_spi_queries ?(interactive=false) lexbuf = 
  process_spi ~interactive Spiparser.input_query lexbuf
and command lexbuf = function
  | "exit",[] -> System.close_all_files () ; exit 0
  | "help",[] -> Format.printf "%s" help_msg
  | "load",[f] -> 
     let fname = Term.get_name f in 
       begin try 
         input_from_spi_file fname
       with 
       | Sys_error e -> Printf.printf "Error: %s \n" e 
       end 
  | "reset",[] ->
     clean_tables () ; 
     Spi.reset_spi_sig () ; 
     System.close_all_files () ;
     System.remove_def Spi.Process.agent_def 
  | "show_bisim",[] -> 
     (
       try
        let _,_,table = Hashtbl.find System.defs (Spi.Process.var_bisim) in
        begin 
         match table with
         | Some table ->              
                show_bisim show_bisim_query table 
         | None ->
             failwith ("No bisimulation set found!\n")
        end
        with
         | Not_found -> raise (System.Undefined (Spi.Process.bisim))
     )
  | "show_table",[] -> 
       System.show_table (Spi.Process.bisim) 
  | "save_bisim",[f] -> 
    (
      try
        let _,_,table = Hashtbl.find System.defs (Spi.Process.var_bisim) in
        let name = Term.get_name f in 
        let _ = System.open_user_file name in
        begin 
         match table with
         | Some table ->              
             show_bisim (fun n g -> save_bisim_query f n g) table ;
             System.close_user_file name 
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end        
      with
      | Not_found -> raise (System.Undefined (Spi.Process.bisim))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;
      
     )
  | "save_bisim_latex",[f] ->
    (
      try
        let _,_,table = Hashtbl.find System.defs (Spi.Process.var_bisim) in
        let name = Term.get_name f in 
        let fout = System.open_user_file name in
        begin 
         match table with
         | Some table ->              
             save_latex_header fout ; 
             show_bisim (fun n g -> 
                     Printf.fprintf fout "\\item \n" ; 
                     save_bisim_latex_query f n g) table ;
             save_latex_footer fout ; 
             System.close_user_file name 
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end        
      with
      | Not_found -> raise (System.Undefined (Spi.Process.bisim))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;      
   )

  | "save_bisim_raw",[f] -> 
    (
      try
        let _,_,table = Hashtbl.find System.defs (Spi.Process.var_bisim) in
        let name = Term.get_name f in 
        let fout = System.open_user_file name in
        begin 
         match table with
         | Some table ->              
             Spi.save_bisim_raw fout table ;
             System.close_user_file name
         | None ->
             System.close_user_file name ;
             failwith ("No bisimulation set found!\n")
        end        
      with
      | Not_found -> raise (System.Undefined (Spi.Process.bisim))
      | Sys_error e -> Printf.printf "Error: %s \n" e ;      
   )

  | "show_def",[a] -> prove_show_def a 
        
  | "show_defs",[] -> prove_show_defs ()

  | "time",[d] ->
      System.time :=
        begin match Term.observe d with
          | Term.Var v when v==System.Logic.var_on -> true
          | Term.Var v when v==System.Logic.var_truth -> true
          | Term.Var v when v==System.Logic.var_off -> false
          | Term.Var v when v==System.Logic.var_falsity -> false
          | _ -> raise Invalid_command
        end

  | _ -> raise Invalid_command

let get_exe_dir () = 
  try 
    let exe_name = Sys.executable_name in 
    let i = String.rindex exe_name '/' in 
     String.sub exe_name 0 (i+1) 
  with
  | Not_found -> "" 
      
let get_def_file () = 
  let file = (get_exe_dir ()) ^ "defs/spec.def" in 
    if Sys.file_exists file then file 
    else raise Def_file_missing 
 
let rec process_def lexbuf =
  try while true do try
    begin match Parser.input_def Lexer.token lexbuf with
      | System.Def (k,h,a,b) -> System.add_clause k h a b
      | System.Query a -> () 
      | System.Command (c,a) -> 
          if (c = "include") then include_def a
          else ()
    end ;
  with
    | Failure "eof" as e -> raise e
    | Parsing.Parse_error ->
        Format.printf "[bedwyr] Syntax error%s.\n%!" (position lexbuf) ;
        exit 1 
    | Failure "lexing: empty token" ->
        Format.printf "[bedwyr] Lexing error%s.\n%!" (position lexbuf) ;
        exit 1
    | Assertion_failed ->
        Format.printf "[bedwyr] Assertion failed%s.\n%!" (position lexbuf) ;
        exit 1
    | e ->
        Format.printf "[bedwyr] Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
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
and input_defs lexbuf = process_def lexbuf

and load_session () =
  let def_file = get_def_file () in 
    System.reset_defs () ;
    Spi.reset_spi_sig () ;
    inclfiles := [] ;
    input_from_file def_file

and include_def f = 
  match f with
  | [g] -> 
    let g = Term.get_name g in
    let not_included fname = 
       if (List.mem fname !inclfiles) then
        false
     else (
        inclfiles := fname :: !inclfiles ;
        true
     )
    in
       if not_included g then input_from_file g else () 
  | _ -> assert false

let _ =
  load_session () ;
  List.iter (fun s -> input_spi_queries (Lexing.from_string s)) !queries ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_spi_queries ~interactive:true (Lexing.from_channel stdin)
  end


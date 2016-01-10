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

module Process = 
struct 
  let agent_def = Term.atom "agent_def" 
  let bisim = Term.atom "bisim" 
  let cmd_show_bisim = Term.atom "show_bisim"
  let cmd_save_bisim = Term.atom "save_bisim"
  let cmd_save_bisim_latex = Term.atom "bisim2latex"
  let cmd_show_def = Term.atom "show_def" 
  let obj_cons = Term.atom "cons"
  let obj_nil  = Term.atom "nil"

  let proc_inp = Term.atom "inp"
  let proc_outp = Term.atom "outp"
  let bt_in = Term.atom "in"
  let bt_out = Term.atom "out"
  let msg_pr = Term.atom "pr"
  let msg_en = Term.atom "en"
  let msg_ct = Term.atom "ct"
  let msg_nm = Term.atom "nm"
  let msg_bn = Term.atom "bn"

  let var_obj_cons = Term.get_var obj_cons
  let var_agent_def = Term.get_var agent_def 
  let var_bisim = Term.get_var bisim
end

(* for spi-specific exception *)
exception Duplicate_agent_def of string
exception Sig_mismatch of string*int

type input =
  | Def  of string * int * Term.term
  | Query   of Term.term
  | Command of string * Term.term list



(* spi-calculus specific functions *) 
let spi_sig : ((string*int) list) ref = ref []
let reset_spi_sig () = spi_sig := []

let add_spi_sig name arity =
  try 
    ignore(List.find (fun (a,b) -> a = name) !spi_sig)
  with
  | Not_found -> spi_sig := (name,arity) :: !spi_sig

let find_spi_name name = 
  try 
    ignore (List.find (fun (a,b) -> (a = name) ) !spi_sig) ;
    true
  with
  | Not_found -> false
   
let find_spi_sig name arity =
  try 
    ignore (List.find (fun (a,b) -> (a = name) & (b = arity)) !spi_sig ) ;
    true
  with
  | Not_found -> false

let bisim_size table =
    let i = ref 0 in
      Table.iter_fun table 
        (fun t tag -> 
           match tag with
           | Table.Proved -> i := (!i + 1) 
           | _ -> ()
        ) ;
      !i


let save_bisim_raw fout table = 
  let fmt = Format.formatter_of_out_channel fout in
  Table.iter_fun table 
    (fun t tag -> 
      let t = Table.nabla_abstract (Term.app t [Process.bisim]) in 
      match tag with
      | Table.Proved -> Format.fprintf fmt "proved %a. \n" Pprint.pp_term t
      | _ -> ()
    )

let get_timestamps t = 
  let ts = ref 0 in 
  let lts = ref 0 in 
  let rec max_ts r = 
      match (Term.observe r) with
      | Term.Var v -> 
         let vts = Term.get_var_ts v in
         let vlts = Term.get_var_lts v in 
            if vts > !ts then ts := vts ;
            if vlts > !lts then lts := vlts 
      | Term.DB n -> ()
         (* if n > !lts then lts := n; *)
      | Term.NB n -> 
         if n > !lts then lts := n; 
      | Term.Lam (n,p) -> max_ts p 
      | Term.App (h,l) -> 
         ignore (List.map max_ts (h::l))
      | _ -> ()
   in
      max_ts t ; 
      (!ts,!lts)



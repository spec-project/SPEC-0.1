(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2007 David Baelde, Alwen Tiu, Axelle Ziegler          *)
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

exception Invalid_definition
exception Level_inconsistency

(* added by AT: this exception is raised when a variable is detected in 
 * a goal that is supposed to be ground *)
exception Variable_leakage

(* [AT]: exception thrown when aborting search *)
exception Abort_search

open Format
open System
open Term

(* Internal design of the prover has two levels, Zero and One.
 * On level One, logic vars are instantiated and eigenvars are constants.
 * On level Zero, logic vars are forbidden and eigenvars can be instantiated. *)

type level = Zero | One

let assert_level_one = function
  | One -> ()
  | Zero -> raise Level_inconsistency

module Right =
  Unify.Make (struct
                let instantiatable = Logic
                let constant_like = Eigen
              end)
module Left =
  Unify.Make (struct
                let instantiatable = Eigen
                let constant_like = Constant
              end)

let unify lvl a b =
  try
    (if lvl = Zero then Left.pattern_unify else Right.pattern_unify) a b ;
    true
  with
    | Unify.Error _ -> false

(* Tabling provides a way to cut some parts of the search,
 * but we should take care not to mistake shortcuts and disproving. *)

let disprovable_stack = Stack.create ()

let clear_disprovable () =
  try
    while true do
      let s,_ = Stack.pop disprovable_stack in s := Table.Unset
    done
  with Stack.Empty -> ()

exception Found
let mark_not_disprovable_until d =
  try
    Stack.iter (fun (_,disprovable) ->
      if disprovable == d
      then raise Found
      else disprovable := false)
      disprovable_stack
  with Found -> ()
  
type 'a answer = Known of 'a | Unknown | OffTopic

let do_open_file g =
  match g with
  | [n] ->
     let name = Term.get_name n in 
     (
       try  
         ignore (open_user_file name) ; true
       with 
       | Sys_error e -> Printf.printf "fopen_out: failed opening file %s\n %s \n" name e ; false
     )
  | _ -> false 

let do_close_file g =
  match g with
  | [n] ->
     let name = Term.get_name n in 
     (
       try  
         close_user_file name ; true
       with 
       | Sys_error e ->  Printf.printf "fopen_out: failed closing file %s\n %s \n" name e ; false
     )
  | _ -> false 
  
let do_fprint newline goals = 
  let print_fun fmt t = 
      if newline then fprintf fmt "%a\n%!" Pprint.pp_term t
      else  fprintf fmt "%a%!" Pprint.pp_term t
  in
    begin match goals with
    | (h::l) -> 
      (
        try 
          let f = get_user_file (Term.get_name h) in
          let fmt = Format.formatter_of_out_channel f in 
          List.iter (print_fun fmt) l ;
          true
        with 
        | Not_found -> false
        | e -> raise e
       )
     | _ -> false
     end 


(* Attemps to prove that the goal [(nabla x_1..x_local . g)(S)] by
 * destructively instantiating it,
 * calling [success] on every success, and finishing with [failure]
 * which can be seen as a more usual continuation, typically
 * restoring modifications and backtracking.
 * [timestamp] must be the oldest timestamp in the goal. *)
let rec prove ~success ~failure ~level ~timestamp ~local g =

  if System.check_interrupt () then begin
    clear_disprovable () ;
    raise System.Interrupt
  end ;

  let g = Norm.hnorm g in
  let invalid_goal () =
    failwith (sprintf "Invalid goal %s" (Pprint.term_to_string g))
  in

  let prove_distinct goals =
      let sol = ref [] in 
      let match_list l1 l2 = List.for_all2 (fun x y -> Term.eq x y) l1 l2 in 
      let a = match goals with [a] -> a | _ -> invalid_goal () in
      let a = Norm.deep_norm a in 
      let vars = if level = Zero then Term.eigen_vars [a] else Term.logic_vars [a] in
          (* printf "List of variables: " ;
           * ignore (List.map (fun t -> printf "%a " Pprint.pp_term t) vars) ; 
           * printf "\n" ; *)
          prove ~level ~timestamp ~failure ~local a
                ~success:(fun ts k ->
                              let tm_list = List.map (fun v -> Term.shared_copy v) vars in 
                              let p = try Some (List.find (fun vs -> match_list tm_list vs) !sol )  
                                      with Not_found -> None
                              in
                                begin match p with 
                                | Some _ -> k ()
                                | None   -> 
                                    sol := tm_list :: !sol ; 
                                    success ts k 
                                end                               
                         )
  in

  let prove_abstract goals =
      let a,b,c = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
      let a = Norm.deep_norm a in
      let b = Norm.deep_norm b in  
      let c = Norm.deep_norm c in 
      let vars = 
        if level = Zero then Term.eigen_vars [a] else Term.logic_vars [a] 
      in
      let d = 
          List.fold_left (fun t v -> Term.app b [Term.abstract_flex v t]) a vars
      in
      let g = Term.app (Logic.eq) [c;d] in 
         prove ~level ~success ~failure ~timestamp ~local g
  in
        
  let prove_not goals = 
      let a = match goals with [a] -> a | _ -> invalid_goal () in
      let a = Norm.deep_norm a in
      let state = Term.save_state() in
      prove ~level ~timestamp ~local a
      ~success:(fun ts k -> 
                  Term.restore_state state ;
                  failure ())
      ~failure:(fun () -> 
                  Term.restore_state state ; 
                  success timestamp failure )
  in

  let prove_ite goals = 
     let (a,b,c) = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
     let a = Norm.deep_norm a in
     let b = Norm.deep_norm b in
     let c = Norm.deep_norm c in
     let succeeded = ref false in 
     let state = Term.save_state () in 
     prove ~level ~timestamp ~local a
     ~success:(fun ts k ->                 
                (*  Term.restore_state state ; *)
                (*  prove ~success ~failure ~level ~timestamp ~local (Term.app (Logic.andc) [a;b]) *)
                succeeded := true ; 
                prove ~success ~level ~timestamp:ts ~local b 
                      ~failure:k
                (* (fun () -> Term.restore_state state ; failure()) *)
              )
     ~failure:(fun () ->
               Term.restore_state state ; 
               if !succeeded then failure () else 
                prove ~success ~failure ~level ~timestamp ~local c
              )
  in

  let prove_atom d args =
    if !debug then 
     printf "Proving %a...\n" Pprint.pp_term g ; 
    let kind,body,table = System.get_def ~check_arity:(List.length args) d in
    let status =
      match table with
        | None -> OffTopic
        | Some table ->
            try match Table.find table args with
              | Some {contents=c} -> Known c
              | None -> Unknown
            with
              | Index.Cannot_table -> OffTopic
    in
      match status with
        | OffTopic ->
            prove ~level ~timestamp ~local ~success ~failure
              (Term.app body args)
        | Known Table.Proved -> 
            if !debug then 
               printf "Goal %a proved using table\n" Pprint.pp_term g; 
            success timestamp failure
        | Known Table.Disproved -> failure ()
        | Known (Table.Working disprovable) ->
            if kind = System.CoInductive then
              success timestamp failure
            else begin
              mark_not_disprovable_until disprovable ;
              failure ()
            end
        | Unknown
        | Known Table.Unset ->
            (* This handles the cases where nothing is in the table,
             * or Unset has been left, in which case the [Table.add]
             * will overwrite it. *)
            let disprovable = ref true in
            let status = ref (Table.Working disprovable) in
            let s0 = Term.save_state () in
            let table_update_success ts k =
              status := Table.Proved ;
              ignore (Stack.pop disprovable_stack) ;
              disprovable := false ;
              (* TODO check that optimization: since we know that
               * there is at most one success, we ignore
               * the continuation [k] and directly jump to the
               * [failure] continuation. It _seems_ OK regarding the
               * cleanup handlers, which are just jumps to
               * previous states.
               * It is actually quite useful in examples/graph-alt.def. *)
              success ts
                (fun () ->
                   Term.restore_state s0 ; failure ())
            in
            let table_update_failure () =
              begin match !status with
                | Table.Proved ->
                    (* This is just backtracking, we are seeing the tabling
                     * entry corresponding to a previous goal.
                     * Never happens if we skipped the success continuation. *)
                    assert false
                | Table.Working _ ->
                    ignore (Stack.pop disprovable_stack) ;
                    if !disprovable then begin
                      status := Table.Disproved ;
                      disprovable := false ;
                    end else
                      status := Table.Unset
                | Table.Disproved | Table.Unset -> assert false
              end ;
              failure ()
            in
            let table = match table with Some t -> t | None -> assert false in
              if try
                Table.add ~allow_eigenvar:(level=One) table args status ;
                true
              with
                | Index.Cannot_table -> false
              then begin
                Stack.push (status,disprovable) disprovable_stack ;
                prove ~level ~local ~timestamp
                  ~success:table_update_success
                  ~failure:table_update_failure
                  (Term.app body args)
              end else
                prove ~level ~local ~success ~failure ~timestamp
                  (Term.app body args)
  in

  match Term.observe g with
  | Var v when v == Logic.var_truth -> success timestamp failure
  | Var v when v == Logic.var_falsity -> failure ()

  (* Abort search: throw an exception *)
  | Var v when v == Logic.var_abort_search ->  raise Abort_search

  (* Trace flag *)
  | Var v when v == Logic.var_traceflag -> 
      if (!trace) then success timestamp failure
      else failure ()

  | Var v -> prove_atom g []
  | App (hd,goals) ->
      let goals = List.map Norm.hnorm goals in
      begin match Term.observe hd with
        (* Solving an equality *)
        | Var v when v == Logic.var_eq ->
            let state = Term.save_state () in
            let failure () = Term.restore_state state ; failure () in
            if unify level (List.hd goals) (List.hd (List.tl goals)) then
              success timestamp failure
            else
              failure ()

        (* Proving a conjunction *)
        | Var v when v == Logic.var_andc ->
            let rec conj ts failure = function
              | [] -> success ts failure
              | goal::goals ->
                  prove
                    ~local ~level ~timestamp
                    ~success:(fun ts k -> conj ts k goals)
                    ~failure
                    goal
            in
              conj timestamp failure goals

        (* Proving a disjunction *)
        | Var v when v == Logic.var_orc ->
            let rec alt = function
              | [] -> failure ()
              | g::goals ->
                  prove
                    ~level ~local ~success ~timestamp
                    ~failure:(fun () -> alt goals)
                    g
            in
              alt goals

        (* Proving a negation-as-failure *)
        | Var v when v == Logic.var_not -> 
            prove_not goals 

        (* Proving if-then-else *)
        | Var v when v == Logic.var_ite ->
            prove_ite goals

        (* Proving abstract-predicate *)
        | Var v when v == Logic.var_abspred ->
            prove_abstract goals 

        (* Checking rigidity assumption *)
        | Var v when v == Logic.var_assert_rigid ->
           let a = match goals with [a] -> a | _ -> invalid_goal () in
           let a = Norm.deep_norm a in 
           let vars = if level = Zero then Term.eigen_vars [a] else Term.logic_vars [a] in
            begin match vars with
            | [] -> success timestamp failure
            | _ -> raise Variable_leakage
            end 

        (* proving cut predicate *) 
        | Var v when v == Logic.var_cutpred -> 
           let a = match goals with [a] -> a | _ -> invalid_goal () in
           let a = Norm.deep_norm a in 
           let state = Term.save_state () in 
             prove ~level ~local ~timestamp ~failure a 
                   ~success:(fun ts k -> success ts (fun () -> Term.restore_state state ; failure ()) )

        (* Proving distinct-predicate *)
        | Var v when v == Logic.var_distinct ->
            prove_distinct goals

        (* Level 1: Implication *)
        | Var v when v == Logic.var_imp ->
            assert_level_one level ;
            let (a,b) = match goals with [a;b] -> a,b | _ -> invalid_goal () in
            let a = Norm.deep_norm a in
            let b = Norm.deep_norm b in
            let check_variables =
              let eigen = eigen_vars [a] in
              let logic = logic_vars [b] in
              let var v =
                match Term.observe v with
                  | Var v -> v
                  | _ -> assert false
              in
              let max = (* maximum logic variable timestamp *)
                List.fold_left
                  (fun m v -> max m (var v).ts) (-1) logic
              in
              let eigen = List.filter (fun v -> (var v).ts <= max) eigen in
                (* Check that all eigen-variables on which logic vars
                 * can depend are instantiated to distinct eigenvars.
                 * Then LLambda unifications will be preserved. *)
                match eigen with
                  | [] -> fun () -> ()
                  | _ ->
                      let var v =
                        match Term.observe v with
                          | Var v when v.tag = Eigen -> v
                          | _ -> raise (Unify.NotLLambda v)
                      in
                        fun () ->
                          (* This is called when some left solution has been
                           * found. We check that everything is a variable. *)
                          let eigen = List.map (fun v -> v,var v) eigen in
                          let rec unicity = function
                            | [] -> ()
                            | (va,a)::tl ->
                                if List.exists (fun (_,b) -> a=b) tl then
                                  raise (Unify.NotLLambda va) ;
                                unicity tl
                          in
                            unicity eigen
            in
            (* Solve [a] using level 0,
             * remind of the solution substitutions as slices of the bind stack,
             * then prove [b] at level 1 for every solution for [a],
             * thanks to the commutability between patches for [a] and [b],
             * one modifying eigenvars,
             * the other modifying logical variables. *)
            let ev_substs = ref [] in
            let state = Term.save_state () in
            let store_subst ts k =
              (* We store the state in which we should leave the system
               * when calling [k].
               * Then we complete the current solution with the reverse
               * flip of variables to eigenvariables, and we get sigma which
               * we store. *)
              check_variables () ;
              ev_substs := (ts,get_subst state)::!ev_substs ;
              k ()
            in
            let make_copies evs g = 
                List.map (fun (ts,sigma) ->
                          let unsig = apply_subst sigma in
                          let newg = Term.shared_copy g in 
                            undo_subst unsig ; 
                            (ts, newg) 
                         )  evs 
            in   
            let rec prove_conj ts failure = function 
              | [] -> success ts failure
              | (ts,g)::gs ->
                 prove ~level ~local ~timestamp:ts ~failure 
                       ~success:(fun ts' k -> prove_conj ts k gs)
                       g
            in 
               prove ~level:Zero ~local ~timestamp a
                     ~success:store_subst
                     ~failure:(fun () -> 
                          prove_conj timestamp failure (make_copies !ev_substs b))

        (* Level 1: Universal quantification *)
        | Var v when v == Logic.var_forall ->
            assert_level_one level ;
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let timestamp = timestamp + 1 in
                  let var = Term.fresh ~lts:local Eigen ~ts:timestamp in
                  let goal = app goal [var] in
                    prove ~local ~timestamp ~level ~success ~failure goal
              | _ -> invalid_goal ()
            end

        (* Local quantification *)
        | Var v when v == Logic.var_nabla ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let local = local + 1 in
                    prove ~local ~level ~timestamp ~success ~failure
                      (app goal [Term.nabla local])
              | _ -> invalid_goal ()
            end

        (* Existential quantification *)
        | Var v when v == Logic.var_exists ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (1,_) ->
                  let timestamp,tag =
                    match level with
                      | Zero ->
                          1+timestamp, Eigen
                      | One ->
                          timestamp, Logic
                  in
                  let var =
                    Term.fresh ~ts:timestamp ~lts:local tag
                  in
                    prove ~local ~level ~timestamp
                      ~success ~failure (app goal [var])
              | _ -> invalid_goal ()
            end

        (* Output *)
        | Var v when v == Logic.var_print ->
            List.iter (fun t -> printf "%a%!" Pprint.pp_term t) goals ;
            success timestamp failure

        | Var v when v == Logic.var_println ->
            List.iter (fun t -> printf "%a\n%!" Pprint.pp_term t) goals ;
            success timestamp failure

        | Var v when v == Logic.var_fprint -> 
            if do_fprint false goals then success timestamp failure
            else failure ()

        | Var v when v == Logic.var_fprintln -> 
            if do_fprint true goals then success timestamp failure
            else failure ()

        (* Opening file for output *)
        | Var v when v == Logic.var_fopen_out -> 
            assert_level_one level ;
            if (do_open_file goals) then success timestamp failure
            else failure () 

        | Var v when v == Logic.var_fclose_out -> 
            assert_level_one level ; 
            if (do_close_file goals) then success timestamp failure
            else failure () 
            
        
        (* Get an AST *)
        | Var v when v == Logic.var_parse ->
            begin match goals with
              | [file;t] ->
                  begin match Term.observe file with
                    | Term.Var v ->
                        let file = Term.get_name file in
                        let state = Term.save_state () in
                        let failure () =
                          Term.restore_state state ; failure ()
                        in
                        let ast = Parser.to_term Lexer.token file in
                          if unify level ast t then
                            success timestamp failure
                          else
                            failure ()
                    | _ -> assert false
                  end
              | _ -> invalid_goal ()
            end

        (* Get an AST: but without expanding the include directive *)
        | Var v when v == Logic.var_simp_parse ->
            begin match goals with
              | [file;t] ->
                  begin match Term.observe file with
                    | Term.Var v ->
                        let file = Term.get_name file in
                        let state = Term.save_state () in
                        let failure () =
                          Term.restore_state state ; failure ()
                        in
                        let ast = Parser.to_term ~incl:false Lexer.token file in
                          if unify level ast t then
                            success timestamp failure
                          else
                            failure ()
                    | _ -> assert false
                  end
              | _ -> invalid_goal ()
            end

        (* Check for definitions *)
        | Var v -> prove_atom hd goals

        (* Invalid goal *)
        | _ -> invalid_goal ()
      end

  (* Failure *)
  | _ -> invalid_goal ()

(* Wrap prove with sanity checks. *)
let prove ~success ~failure ~level ~timestamp ~local g =
  let s0 = Term.save_state () in
  let success ts k =
    assert (Stack.is_empty disprovable_stack) ;
    success ts k
  in
  let failure () =
    assert (Stack.is_empty disprovable_stack) ;
    assert (s0 = Term.save_state ()) ;
    failure ()
  in
  try
    prove ~success ~failure ~level ~timestamp ~local g
  with e ->
    clear_disprovable () ;
    Term.restore_state s0 ;
    raise e

let toplevel_prove g =
  let s0 = Term.save_state () in
  let vars = List.map (fun t -> Pprint.term_to_string t, t)
               (List.rev (Term.logic_vars [g])) in
  let found = ref false in
  let reset,time =
    let t0 = ref (Unix.gettimeofday ()) in
      (fun () -> t0 := Unix.gettimeofday ()),
      (fun () ->
         if !System.time then
           printf "+ %.0fms\n" (1000. *. (Unix.gettimeofday () -. !t0)))
  in
  let show _ k =
    time () ;
    found := true ;
    if vars = [] then printf "Yes.\n" else
      printf "Solution found:\n" ;
    List.iter
      (fun (o,t) -> printf " %s = %a\n" o Pprint.pp_term t)
      vars ;
    printf "More [y] ? %!" ;
    let l = input_line stdin in
      if l = "" || l.[0] = 'y' || l.[0] = 'Y' then begin
        reset () ;
        k ()
      end else begin
        Term.restore_state s0 ;
        printf "Search stopped.\n"
      end
  in
     prove ~level:One ~local:0 ~timestamp:0 g
      ~success:show
      ~failure:(fun () ->
                  time () ;
                  if !found then printf "No more solutions.\n"
                  else printf "No.\n")

let simple_toplevel_prove g = 
  let found = ref false in
  let reset,time =
    let t0 = ref (Unix.gettimeofday ()) in
      (fun () -> t0 := Unix.gettimeofday ()),
      (fun () ->
         if !System.time then
           printf "+ %.0fms\n" (1000. *. (Unix.gettimeofday () -. !t0)))
  in
  let show _ k =
    time () ;
    found := true ;
    printf "Yes.\n" ;
  in
    prove ~level:One ~local:0 ~timestamp:0 g
      ~success:show
      ~failure:(fun () ->
                  time () ; 
                  if not !found then printf "No.\n"
               )

let custom_toplevel_prove s f g = 
  prove ~level:One ~local:0 ~timestamp:0 g ~success:s ~failure:f

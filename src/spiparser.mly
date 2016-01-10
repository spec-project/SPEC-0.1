/***************************************************************************
* SPEC                                                                     *
* Copyright (C) 2011 Alwen Tiu                                             *
*                                                                          *
* This program is free software; you can redistribute it and/or modify     *
* it under the terms of the GNU General Public License as published by     *
* the Free Software Foundation; either version 2 of the License, or        *
* (at your option) any later version.                                      *
*                                                                          *
* This program is distributed in the hope that it will be useful,          *
* but WITHOUT ANY WARRANTY; without even the implied warranty of           *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *
* GNU General Public License for more details.                             *
*                                                                          *
* You should have received a copy of the GNU General Public License        *
* along with this code; if not, write to the Free Software Foundation,     *
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *
****************************************************************************/

%{
  let eq   a b = Term.app System.Logic.eq   [a;b]

  let qatom name = Term.atom ("_" ^ name)
  let agent_atom name = 
      let p = Char.escaped '"' in 
      Term.string (p ^ name ^ p) 

  (* Transform a term so that all constants with names starting a quote are transformed
     into object level constants by applying a constructor to them. *)

  let objectify c tm = 
    let tm = Norm.deep_norm tm in 
    let rec obj t = 
       match Term.observe t with
       | Term.NB i | Term.DB i -> t
       | Term.Var v ->  
          let name = Term.get_name t in 
           begin  match name.[0] with 
             | '_' -> (* Term.app c [t]  *)
                 ( 
                   try
                    let newname = String.sub name 1 ((String.length name) - 1) in 
                       Term.app c [Term.atom newname] 
                   with
                   | Invalid_argument e -> t
                 )                    
             | _ -> t
           end
       | Term.App (a,l) -> 
          Term.app (obj a) (List.map obj l)
       | Term.Lam (n,b) ->
          Term.lambda n  (obj b) 
       | _ -> t
     in
       obj tm 

  let par a b = Term.app (Term.atom "par") [a;b]
  let outproc a b c = Term.app (Term.atom "outp") [a;b;c]
  let inproc a b c = 
      let was_free = Term.is_free b in
      let a = qatom a in 
      let v = qatom b in
      let x = Term.abstract v c in
        if was_free then Term.free b; 
        (Term.app (Term.atom "inp") [a;x])

  let nuproc a b = 
      let abs_var x t = 
          let was_free = Term.is_free x in
          let v = qatom x in
          let s = Term.abstract v t in
            if was_free then Term.free x ; 
            Term.app (Term.atom "nu") [s]
      in
         List.fold_right abs_var a b 

  let caseproc m v t p = 
      let was_free = Term.is_free v in
      let w = qatom v in 
      let q = Term.abstract w p in
        if was_free then Term.free v ;
        Term.app (Term.atom "case") [m;t;q]      

  let letproc m v1 v2 p = 
      let was_free_v1 = Term.is_free v1 in
      let was_free_v2 = Term.is_free v2 in
      let w1 = qatom v1 in
      let w2 = qatom v2 in
      let q = Term.abstract w2 p in
      let r = Term.abstract w1 q in
          if was_free_v1 then Term.free v1 ;
          if was_free_v2 then Term.free v2 ;
          Term.app (Term.atom "let") [m;r]

  let to_string t = Term.get_name t

  let rec mkpairs c l = 
     match l with
     | [] | [_] -> assert false
     | [a;b] -> Term.app c [a;b]
     | x::r -> let t = mkpairs c r in Term.app c [x;t] 
      
        
  let mkdef a b = 
      let agentname,vars = a in 
      let arity = List.length vars in 
      let agent = agent_atom agentname in 
      let abs_var x t = 
          let was_free = Term.is_free x in
          let v = qatom x in
          let s = Term.abstract v t in
            if was_free then Term.free x ; 
            Term.app (Term.atom "defAbs") [s]
      in
      let b = List.fold_right abs_var vars (Term.app (Term.atom "defProc") [b]) in
      let params = [agent ; b] in 
      let () =
         let v = Term.logic_vars params in
           List.iter (fun v -> Term.free (Term.get_name v)) v
      in
      let new_params,prolog =
        List.fold_left
        (fun (new_params,prolog) p ->
           match Term.observe p with
             | Term.Var {Term.tag=Term.Logic}
                 when List.for_all (fun v -> v!=p) new_params ->
                 p::new_params,prolog
             | _  ->
                 let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
                   (v::new_params, (eq v p)::prolog))
        ([],[])
        params 
      in 
    (* Add prolog to the body *)
    let body = Term.app System.Logic.andc prolog  in

    (* Quantify existentially over the initial free variables. *)
    let body =
      List.fold_left
        (fun body v ->
           if List.exists (Term.eq v) new_params then body else
             Term.app System.Logic.exists [Term.abstract v body])
        body
        (Term.logic_vars (body::params))
    in
    (* Finally, abstract over parameters *)
    let body =
      if new_params = [] then body else
        let body =
          List.fold_left (fun body v -> Term.abstract v body)
            body
            new_params
        in match Term.observe body with
          | Term.Lam (n,b) -> b
          | _ -> assert false
    in
      Spi.Def (agentname, arity, objectify (Term.atom "ct") body)

   let mkquery a b = 
       let t = Term.app (Term.atom "bisim_def") [a ; b] in 
       Spi.Query (objectify (Term.atom "ct") t) 

(* | outpref { let a,b = $1 in outproc a b (Term.atom "zero") } *)
(* | inpref { let a,b = $1 in inproc a b (Term.atom "zero") } *)

%}

%token LPAREN RPAREN LBRAK RBRAK LANGLE RANGLE LBRAC RBRAC SEMICOLON BISIM
%token ZERO DOT EQ COMMA NU PAR ENC DEF CASE LET OF IN SHARP BANG
%token <string> ID
%token <string> AID
%token <string> STRING

%right PAR
%nonassoc BANG
%nonassoc DOT
%nonassoc RBRAK IN


%start input_def input_query
%type <Spi.input> input_def
%type <Spi.input> input_query


%%
input_def:
| head DEF pexp SEMICOLON { mkdef $1 $3 }
input_query:
| head DEF pexp SEMICOLON { mkdef $1 $3  }
| BISIM LPAREN pexp COMMA pexp RPAREN SEMICOLON  { mkquery $3 $5 }
| SHARP ID SEMICOLON { Spi.Command ($2, [])}
| SHARP ID STRING SEMICOLON { Spi.Command ($2, [Term.string $3]) }
| SHARP ID AID SEMICOLON { Spi.Command ($2, [agent_atom $3] ) }
| SHARP ID ID SEMICOLON { Spi.Command ($2, [Term.atom $3] ) }

head:
| AID { let was_defined = Spi.find_spi_name $1 in
         if was_defined then 
            raise (Spi.Duplicate_agent_def $1)
         else ($1, []) 
      }
| AID LPAREN lids RPAREN { 
        let was_defined = Spi.find_spi_name $1 in
          if was_defined then 
            raise (Spi.Duplicate_agent_def $1)       
          else ($1,$3) 
      }

pexp:
| agent { $1 }
| ZERO { Term.atom "zero" }
| outpref { let a,b = $1 in outproc a b (Term.atom "zero") }
| inpref { let a,b = $1 in inproc a b (Term.atom "zero") }
| pexp PAR pexp { par $1 $3}
| outpref DOT pexp { let a,b = $1 in outproc a b $3 }
| inpref DOT pexp { let a,b = $1 in inproc a b $3 }
| nupref DOT pexp { nuproc $1 $3 }
| LBRAK texp EQ texp RBRAK pexp { Term.app (Term.atom "match") [$2;$4;$6]}
| cpref IN pexp { let a,(b,c) = $1 in caseproc a b c $3 }
| lpref IN pexp { let t,(v1,v2) = $1 in letproc t v1 v2 $3 }
| BANG pexp { Term.app (Term.atom "bang") [$2]}
| apexp { $1 }

apexp:
| LPAREN pexp RPAREN { $2 }

agent:
| AID { 
   let was_defined = Spi.find_spi_sig $1 0 in 
   if was_defined then 
      Term.app (Term.atom "def") [agent_atom $1 ; Term.atom "nil"] 
   else
      raise (Spi.Sig_mismatch ($1,0))
  }
| AID LBRAC lids RBRAC { 
   let n = List.length $3 in 
   let cons = Term.binop "cons" in 
   let was_defined = Spi.find_spi_sig $1 n in 
   if was_defined then 
      let args = List.fold_right 
             (fun x t -> cons x t)            
             (List.map (fun x -> qatom x) $3) 
             (Term.atom "nil")
      in 
        Term.app (Term.atom "def") [agent_atom $1 ; args]
   else
      raise (Spi.Sig_mismatch ($1, n))
  }

inpref:
| ID LPAREN ID RPAREN { ($1,$3) }

outpref:
| ID LANGLE texp RANGLE { (qatom $1, $3) }

nupref: 
| NU LPAREN lids RPAREN { $3 }

cpref: 
| CASE texp OF encpat { ($2,$4) } 

lpref:
| LET texp EQ prpat { ($2,$4) }

lids:
| ID { [$1] }
| ID COMMA lids  { $1::$3 }

encpat:
| ENC LPAREN ID COMMA texp RPAREN { ($3,$5) }

prpat:
| LANGLE ID COMMA ID RANGLE { ($2, $4) }

texp: 
| ID  { qatom $1 }
| LANGLE texp COMMA ltexp RANGLE { mkpairs (Term.atom "pr") ($2::$4)  }
| ENC LPAREN texp COMMA texp RPAREN { Term.app (Term.atom "en") [$3;$5] }
| atexp { $1 }

ltexp:
| texp { [$1] }
| texp COMMA ltexp { $1::$3 }

atexp:
| LPAREN texp RPAREN { $2 }

%%



type tag = Proved | Working of bool ref | Disproved | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

let nabla_abstract t =  
  let t = Norm.deep_norm t in
  let l = Term.get_nablas t in 
   List.fold_right (fun i s -> Term.app (Term.atom "nabla") [Term.abstract (Term.nabla i) s]) l t 

let print head table =
  Format.printf
    "Table for %a contains (P=Proved, D=Disproved):@\n"
    Pprint.pp_term head ;
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.printf " [P] %a@\n" Pprint.pp_term t
         | Disproved -> Format.printf " [D] %a@\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let iter_fun table  f = 
  Index.iter !table (fun t tag -> f t !tag)

  
(* AT: add a function to print a table to a file. *)
let fprint fout head table =
  let fmt = (Format.formatter_of_out_channel fout) in 
  Format.fprintf fmt 
    "%% Table for %a contains :@\n"
    Pprint.pp_term head ;
   Index.iter !table 
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.fprintf fmt "proved %a.\n" Pprint.pp_term t
         | Disproved -> Format.fprintf fmt "disproved %a.\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let reset x = x := Index.empty

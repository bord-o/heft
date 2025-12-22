open Kernel
open Result.Syntax
open Derived
open Inductive

let pp_thm th = print_newline @@ print_endline @@ Printing.pretty_print_thm th

let pp_term trm =
  print_newline @@ print_endline @@ Printing.pretty_print_hol_term trm
type nat = Zero | Suc of nat

let rec add_nat m n = match m, n with
    | Zero, n ->  n
    | Suc(m'), n -> Suc (add_nat m' n)


let nat_def = 
    let nat_ty =  TyCon ("nat", []) in
    define_inductive "nat" [] [
      { name = "Zero"; arg_types = [] };
      { name = "Suc"; arg_types = [ nat_ty ] };
    ]

let new_specification name ex_thm =
    let concl_tm = concl ex_thm in
    let exists_var, body = destruct_exists concl_tm in
    let var_type = type_of_var exists_var in
    let* () = new_constant name var_type in
    let new_const = Const (name, var_type) in
    let* defining_property = vsubst [(new_const, exists_var)] body in
    new_axiom defining_property

(* Extract the inductive type being recursed on from branch terms *)
let rec find_inductive_type_in_term = function
    | Const (name, _) ->
        let find_containing_type () =
            Hashtbl.fold (fun type_name def acc ->
                match acc with
                | Some _ -> acc
                | None ->
                    if List.exists (fun (ctor_name, _) -> ctor_name = name) def.constructors
                    then Some (type_name, def)
                    else None
            ) the_inductives None
        in
        find_containing_type ()
    | App (f, arg) ->
        (match find_inductive_type_in_term f with
         | Some result -> Some result
         | None -> find_inductive_type_in_term arg)
    | Lam (_, body) -> find_inductive_type_in_term body
    | _ -> None

let find_recursed_inductive_type branches =
    let rec search = function
        | [] -> Error (InvariantViolation "Could not determine inductive type from branches")
        | branch :: rest ->
            (match find_inductive_type_in_term branch with
             | Some result -> Ok result
             | None -> search rest)
    in
    search branches

(* Define a recursive function on an inductive type *)
let define_recursive_function func_name return_type branches =
    let* (_, inductive_def) = find_recursed_inductive_type branches in

    let type_inst = [(make_vartype "r", return_type)] |> List.to_seq |> Hashtbl.of_seq in
    let* typed_recursion_thm = inst_type type_inst inductive_def.recursion in
    let* instantiated_thm = specs branches typed_recursion_thm in
    new_specification func_name instantiated_thm

let plus_def = 
  let _ = init_types () in
    let nat_ty =  TyCon ("nat", []) in
    let* nat_def = nat_def in
    let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in

    let n = make_var "n"  nat_ty in
    let m' = make_var "m'" nat_ty in
    let r = make_var "r" (make_fun_ty nat_ty nat_ty) in

    let* zero_case = make_lam n n in  (* λn. n *)
    let* suc_case =
        let* r_n = make_app r n in
        let* suc_rn = make_app suc r_n in
        let* lam_n_suc_rn = make_lam n suc_rn in
        let* lam_r = make_lam r lam_n_suc_rn in
        make_lam m' lam_r  (* λm'. λr. λn. Suc (r n) *)
    in

    let return_type = make_fun_ty nat_ty nat_ty in
    define_recursive_function "plus" return_type [zero_case; suc_case]



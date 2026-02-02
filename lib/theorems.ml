open Kernel
open Derived
open Result.Syntax
open Inductive

let p = Var ("P", bool_ty)
let q = Var ("Q", bool_ty)
let r = Var ("R", bool_ty)
let s = Var ("S", bool_ty)
let g = Var ("f", TyCon ("fun", [ bool_ty; bool_ty ]))
let x = Var ("x", bool_ty)
let y = Var ("y", bool_ty)
let z = Var ("z", bool_ty)
let axiom_for_test tm = Result.get_ok (new_axiom tm)

let double_negation_implies_p =
  let thm =
    let neg_neg_p = make_neg (make_neg p) in
    let p = p in
    let* start = assume neg_neg_p in
    let* nelim = not_elim start in
    let* contr = ccontr p nelim in
    disch neg_neg_p contr
  in
  make_exn thm

let forall_symmetry =
  let thm =
    let* x_eq_y = safe_make_eq x y in

    let* xy_th = assume x_eq_y in
    let* yx_th = sym xy_th in
    let* imp = disch x_eq_y yx_th in
    gens [ x; y ] imp
  in
  make_exn thm

let identity =
  let thm =
    let* p_th = assume p in
    disch p p_th
  in
  make_exn thm

let contrapositive =
  let thm =
    let p_imp_q = make_imp p q in

    let* pq_th = assume p_imp_q in
    let* nq_th = assume (make_neg q) in
    let* p_th = assume p in
    let* qmp = mp pq_th p_th in
    let* nnq = not_elim nq_th in
    let* combined = prove_hyp qmp nnq in
    let* np = not_intro p combined in
    let* d1 = disch (make_neg q) np in
    let* d2 = disch p_imp_q d1 in
    Ok d2
  in
  make_exn thm

module Nat = struct
  let nat_ty = TyCon ("nat", [])

  let nat_def =
    define_inductive "nat" []
      [
        { name = "Zero"; arg_types = [] };
        { name = "Suc"; arg_types = [ nat_ty ] };
      ]
    |> Result.get_ok

  let zero = nat_def.constructors |> List.assoc "Zero"
  let suc = nat_def.constructors |> List.assoc "Suc"
  let rec nat_of_int n = if n <= 0 then zero else App (suc, nat_of_int (n - 1))
  let n0 = zero
  let n1 = nat_of_int 1
  let n2 = nat_of_int 2
  let n3 = nat_of_int 3
  let n4 = nat_of_int 4
  let n5 = nat_of_int 5
  let n6 = nat_of_int 6
  let n7 = nat_of_int 7
  let n8 = nat_of_int 8
  let n9 = nat_of_int 9
  let n10 = nat_of_int 10

  let plus_def =
    let d =
      let n = make_var "n" nat_ty in
      let m' = make_var "m'" nat_ty in
      let r = make_var "r" (make_fun_ty nat_ty nat_ty) in
      let* zero_case = make_lam n n in
      (* λn. n *)
      let* suc_case =
        let* r_n = make_app r n in
        let* suc_rn = make_app suc r_n in
        let* lam_n_suc_rn = make_lam n suc_rn in
        let* lam_r = make_lam r lam_n_suc_rn in
        make_lam m' lam_r (* λm'. λr. λn. Suc (r n) *)
      in
      let return_type = make_fun_ty nat_ty nat_ty in
      define_recursive_function "plus" return_type "nat" [ zero_case; suc_case ]
    in
    d |> Result.get_ok

  let plus = make_const "plus" [] |> Result.get_ok

  let make_plus a b =
    let* ab = make_app plus a in
    make_app ab b
end

module ListTheory = struct
  let rec length = fun l -> match l with [] -> 0 | _x :: xs -> 1 + length xs
  let a = make_vartype "a"
  let list_ty = TyCon ("list", [ a ])
  let list_a = TyCon ("list", [ a ])

  let list_def =
    define_inductive "list" [ "a" ]
      [
        { name = "Nil"; arg_types = [] };
        { name = "Cons"; arg_types = [ a; list_a ] };
      ]
    |> Result.get_ok

  let nil = list_def.constructors |> List.assoc "Nil"
  let cons = list_def.constructors |> List.assoc "Cons"

  let length_def =
    let d =
      let x = make_var "x" a in
      let xs = make_var "xs" list_a in
      let r = make_var "r" Nat.nat_ty in

      let nil_case = Nat.n0 in
      (* Cons_case takes: x (head), xs (tail), r (recursive result on tail) *)
      (* So it's λx. λxs. λr. Suc r *)
      let* cons_case =
        let body = App (Nat.suc, r) in
        let* fn_r = make_lam r body in
        let* fn_xs = make_lam xs fn_r in
        make_lam x fn_xs
      in
      let return_type = Nat.nat_ty in
      define_recursive_function "length" return_type "list"
        [ nil_case; cons_case ]
    in
    d
end

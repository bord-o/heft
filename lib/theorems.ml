open Kernel
open Derived
open Result.Syntax

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

module NatTheory = struct
  let prg =
    {|
    vartype a

    inductive nat :=
        | zero : nat
        | suc : nat -> nat

    variable o m n : nat

    def plus over o : nat -> nat -> nat 
        | zero => λn. n
        | suc m => λn. suc (plus m n)
  |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e

  let nat_ty = make_type "nat" [] |> Result.get_ok
  let nat_def = Hashtbl.find the_inductives "nat"
  let zero = make_const "zero" [] |> Result.get_ok
  let suc = make_const "suc" [] |> Result.get_ok
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

  let plus =
    let v = make_const "plus" [] in
    match v with Ok t -> t | Error e -> failwith @@ Printing.print_error e

  let make_plus a b =
    let* ab = make_app plus a in
    make_app ab b
end

module ListTheory = struct
  let a = make_vartype "a"
  let list_ty = TyCon ("list", [ a ])
  let list_a = TyCon ("list", [ a ])

  let prg =
    {|
    vartype a

    inductive list :=
        | nil : list a
        | cons : a -> list a -> list a

    variable l l' xs : list a
    variable x : a

    def length over l : list a -> nat 
        | nil => zero
        | cons x xs =>
            suc (length xs)

    def append over l : list a -> list a -> list a
        | nil => λxs. xs
        | cons x xs =>
            λl'. cons x (append xs l')

    def reverse over l : list a -> list a
        | nil => nil
        | cons x xs => append (reverse xs) (cons x nil)
  |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e

  let list_def = Hashtbl.find the_inductives "list"
  let nil = make_const "nil" [] |> Result.get_ok
  let cons = make_const "cons" [] |> Result.get_ok
  let length = make_const "length" [] |> Result.get_ok
  let append = make_const "append" [] |> Result.get_ok
  let reverse = make_const "reverse" [] |> Result.get_ok
end

module PairTheory = struct
  let prg =
    {|
    vartype a b
    inductive pair := 
        | pair : a -> b -> pair a b

    variable l : a
    variable r : b
    variable p : pair a b

    def fst over p : pair a b -> a
        | pair l r => l

    def snd over p : pair a b -> b
        | pair l r => r

    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (pair x y)) (snd (pair x y)))

  |}

  let _ = Elaborator.goals_from_string prg
  let list_def = Hashtbl.find the_inductives "list"
  let fst = make_const "fst" [] |> Result.get_ok
  let snd = make_const "snd" [] |> Result.get_ok
end

(** Example definitions used in some test proofs *)

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
let t = make_true ()
let f = make_false ()
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

let not_t_eq_f =
  let thm =
    let* t_eq_f = safe_make_eq t f in
    let* assumed = assume t_eq_f in
    let* false_th = eq_mp assumed truth in
    disch t_eq_f false_th
  in
  make_exn thm

let not_f_eq_t =
  let thm =
    let* f_eq_t = safe_make_eq f t in
    let* assumed = assume f_eq_t in
    let* flipped = sym assumed in
    let* false_th = eq_mp flipped truth in
    disch f_eq_t false_th
  in
  make_exn thm

let t_eq_t = make_exn (eq_truth_intro (Result.get_ok (refl t)))

let t_eq_f =
  let thm =
    let* t_eq_f = safe_make_eq t f in
    let* fwd = undisch not_t_eq_f in
    let* f_assumed = assume f in
    let* bwd = contr t_eq_f f_assumed in
    deduct_antisym_rule bwd fwd
  in
  make_exn thm

let f_eq_t =
  let thm =
    let* f_eq_t = safe_make_eq f t in
    let* fwd = undisch not_f_eq_t in
    let* f_assumed = assume f in
    let* bwd = contr f_eq_t f_assumed in
    deduct_antisym_rule bwd fwd
  in
  make_exn thm

let f_eq_f = make_exn (eq_truth_intro (Result.get_ok (refl f)))

let t_imp_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let t_imp_p = make_imp t p in
    let* t_imp_p_assumed = assume t_imp_p in
    let* fwd = mp t_imp_p_assumed truth in
    let* p_assumed = assume p in
    let* bwd = disch t p_assumed in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let f_imp_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let* f_assumed = assume f in
    let* p_from_f = contr p f_assumed in
    let* f_imp_p_thm = disch f p_from_f in
    let* eq_th = eq_truth_intro f_imp_p_thm in
    gen p eq_th
  in
  make_exn thm

let conj_t_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let p_and_t = make_conj p t in
    let* fwd = conj_left (Result.get_ok (assume p_and_t)) in
    let* p_assumed = assume p in
    let* bwd = conj p_assumed truth in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let t_conj_eq =
  let thm =
    let p = Var ("P", bool_ty) in
    let t_and_p = make_conj t p in
    let* fwd = conj_right (Result.get_ok (assume t_and_p)) in
    let* p_assumed = assume p in
    let* bwd = conj truth p_assumed in
    let* eq_th = deduct_antisym_rule bwd fwd in
    gen p eq_th
  in
  make_exn thm

let select_eq =
  let thm =
    let a_ty = TyVar "a" in
    let a = Var ("a", a_ty) in
    let x = Var ("x", a_ty) in
    let* choice = choice_def in
    let* x_eq_a = safe_make_eq x a in
    let* pred = make_lam x x_eq_a in
    let* specced = spec pred choice in
    let* a_eq_a = refl a in
    let* exists_witness = exists_p x x_eq_a a a_eq_a in
    let* applied = mp specced exists_witness in
    let* beta_th = deep_beta (concl applied) in
    let* result = eq_mp beta_th applied in
    gen a result
  in
  make_exn thm

module FunctionTheory = struct
  let prg =
    {|

    vartype a
    vartype b
    vartype c
    variable x a : a
    variable b : b
    variable g : (c -> a)

    def twice : (a -> a) -> a -> a
        | f => λx. f (f x)

    def flip : (a -> b -> c) -> b -> a -> c
        | f => λb. λa. f a b

    def const : a -> b -> a
        | x => λb. x

    def compose : (a -> b) -> (c -> a) -> c -> b 
        | f => λg. λx. f (g x)

  |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e
end

module NatTheory = struct
  let prg =
    {|
    vartype a

    inductive nat :=
        | zero : nat
        | suc : nat -> nat

    variable o m n : nat

    def plus : nat -> nat -> nat 
        | zero => λn. n
        | suc m => λn. suc (plus m n)

    def pred : nat ->  nat
        | zero => zero
        | suc m => m

    def minus' : nat -> nat -> nat
        | zero    => λm. m
        | suc n => λm. pred (minus' n m)

    def minus : nat -> nat -> nat
        | m => (flip minus') m

    def mult : nat -> nat -> nat
        | zero => λn. zero
        | suc n => λm. plus n (mult n m)
    
    def is_zero : nat -> bool
        | zero => T
        | suc n => F 
        
    variable z : a
    variable s : nat -> a

    def nat_match : nat -> a -> (nat -> a) -> a
        | zero => λz. λs. z
        | suc n => λz. λs. s n    

    variable k : nat
    def nat_le : nat -> nat -> bool
        | zero => λn. T
        | suc m => λn. nat_match n F (λk. nat_le m k)

    def sub : nat -> nat -> nat
        | zero => λn. zero
        | suc m => λn. nat_match n (suc m) (λk. sub m k)
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

    def length : list a -> nat 
        | nil => zero
        | cons x xs =>
            suc (length xs)

    def append : list a -> list a -> list a
        | nil => λxs. xs
        | cons x xs =>
            λl'. cons x (append xs l')

    def reverse  : list a -> list a
        | nil => nil
        | cons x xs => append (reverse xs) (cons x nil)

    variable n : nat
    def insert : list nat -> nat -> list nat
        | nil => λn. cons n nil
        | cons x xs => λn. (COND (nat_le x n) (cons x (insert xs n)) (cons n (cons x xs)))

    variable h : nat
    variable t : list nat
    def isort : list nat -> list nat
        | nil => nil
        | cons h t => insert (isort t) h


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

    def fst : pair a b -> a
        | pair l r => l

    def snd : pair a b -> b
        | pair l r => r

    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (pair x y)) (snd (pair x y)))

  |}

  let _ = Elaborator.goals_from_string prg
  let list_def = Hashtbl.find the_inductives "list"
  let fst = make_const "fst" [] |> Result.get_ok
  let snd = make_const "snd" [] |> Result.get_ok
end

module BoolTheory = struct
  let prg = {|
    theorem bool_distinct : neg (eq T F)
  |}

  let _ = Elaborator.goals_from_string prg
end

module CondTheory = struct
  open Tactic

  let cond_true_goal =
    let prg =
      {|
      vartype a
      variable t1 t2 : a
      theorem cond_true : eq (COND T t1 t2) t1
    |}
    in
    ([], List.hd (Elaborator.goals_from_string prg))

  let () =
    let proof =
      with_rule (cond_def |> Result.get_ok) rewrite_tac
      >> beta_tac
      >> with_rule t_eq_t rewrite_tac
      >> with_rule t_eq_f rewrite_tac
      >> with_rule f_imp_eq rewrite_tac
      >> with_rule conj_t_eq rewrite_tac
      >> with_rule t_imp_eq rewrite_tac
      >> with_rule select_eq rewrite_tac
      >> refl_tac
    in
    run_proof ~notrace:true ~name:"cond_true" ~simp:true ~quiet:true
      cond_true_goal proof

  let cond_false_goal =
    let prg =
      {|
      vartype a
      variable t1 t2 : a
      theorem cond_false : eq (COND F t1 t2) t2
    |}
    in
    ([], List.hd (Elaborator.goals_from_string prg))

  let () =
    let proof =
      with_rule (cond_def |> Result.get_ok) rewrite_tac
      >> beta_tac
      >> with_rule f_eq_t rewrite_tac
      >> with_rule f_eq_f rewrite_tac
      >> with_rule f_imp_eq rewrite_tac
      >> with_rule t_conj_eq rewrite_tac
      >> with_rule t_imp_eq rewrite_tac
      >> with_rule select_eq rewrite_tac
      >> refl_tac
    in
    run_proof ~notrace:true ~name:"cond_false" ~simp:true ~quiet:true
      cond_false_goal proof
end

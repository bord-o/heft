(** Example definitions used in some test proofs *)

open Heft
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

module BoolTheory = struct
  let prg =
    {|
    variable a b : bool
    def eqb : bool -> bool -> bool 
        |  a => COND a (λb. COND b T F) (λb. COND b F T)

    def andb : bool -> bool -> bool
        | a => COND a (λb. COND b T F) (λb. COND b F F)
  |}

  let _ = Elaborator.goals_from_string prg
end

module OptionTheory = struct
  [%%inductive type 'a option = None | Some of 'a]

  let prg =
    {|

    vartype a

    vartype b
    variable none_case : b
    variable some_case : a -> b

    def option_match : option a -> b -> (a -> b) -> b
        | None => λnone_case. λsome_case. none_case
        | Some x => λnone_case. λsome_case. some_case x

    variable x y : a
    def default : option a -> a -> a
        | None => λx. x
        | Some y => λx. y
  |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e

  let option_def = Hashtbl.find the_inductives "option"
end

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
  [%%inductive type nat = Zero | Suc of nat]

  let prg =
    {|
    vartype a


    variable o m n : nat

    def plus : nat -> nat -> nat 
        | Zero => λn. n
        | Suc m => λn. Suc (plus m n)

    def pred : nat ->  nat
        | Zero => Zero
        | Suc m => m

    def minus' : nat -> nat -> nat
        | Zero    => λm. m
        | Suc n => λm. pred (minus' n m)

    def minus : nat -> nat -> nat
        | m => (flip minus') m

    def mult : nat -> nat -> nat
        | Zero => λn. Zero
        | Suc n => λm. plus n (mult n m)
    
    def is_zero : nat -> bool
        | Zero => T
        | Suc n => F 
        
    variable z : a
    variable s : nat -> a

    def nat_match : nat -> a -> (nat -> a) -> a
        | Zero => λz. λs. z
        | Suc n => λz. λs. s n    

    variable k : nat
    def nat_le : nat -> nat -> bool
        | Zero => λn. T
        | Suc m => λn. nat_match n F (λk. nat_le m k)

    variable a b r : nat

    def nat_lt : nat -> nat -> bool
        | Zero => λn. nat_match n F (λk. T)
        | Suc m => λn. nat_match n F (λk. nat_lt m k)


    def sub : nat -> nat -> nat
        | Zero => λn. Zero
        | Suc m => λn. nat_match n (Suc m) (λk. sub m k)

    def div_aux : nat -> nat -> nat -> option nat
        | Zero => λa. λb. None
        | Suc n => λa. λb.
            COND (nat_lt a b)
                 (Some Zero)
                 (option_match (div_aux n (sub a b) b)
                    None
                    (λr. Some (Suc r)))

    variable x : nat
    def div : nat -> nat -> nat
        | a => λb.
            option_match (div_aux (Suc a) a b) Zero (λx. x)
  |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e

  let nat_ty = make_type "nat" [] |> Result.get_ok
  let nat_def = Hashtbl.find the_inductives "nat"
  let zero = make_const "Zero" [] |> Result.get_ok
  let suc = make_const "Suc" [] |> Result.get_ok
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

module PairTheory = struct
  [%%inductive type ('a, 'b) pair = Pair of 'a * 'b]

  let prg =
    {|
    vartype a b

    variable l : a
    variable r : b
    variable p : pair a b

    def fst : pair a b -> a
        | Pair l r => l

    def snd : pair a b -> b
        | Pair l r => r

    variable x y : a
    theorem fst_snd_eq: imp (eq x y) (eq (fst (Pair x y)) (snd (Pair x y)))

  |}

  let _ = Elaborator.goals_from_string prg
  let fst = make_const "fst" [] |> Result.get_ok
  let snd = make_const "snd" [] |> Result.get_ok
end

module ListTheory = struct
  let a = make_vartype "a"
  let list_ty = TyCon ("list", [ a ])
  let list_a = TyCon ("list", [ a ])

  [%%inductive type 'a list = Nil | Cons of 'a * 'a list]

  let prg =
    {|
    vartype a

    variable l l' xs : list a
    variable x : a

    def length : list a -> nat 
        | Nil => Zero
        | Cons x xs =>
            Suc (length xs)

    def append : list a -> list a -> list a
        | Nil => λxs. xs
        | Cons x xs =>
            λl'. Cons x (append xs l')

    def reverse  : list a -> list a
        | Nil => Nil
        | Cons x xs => append (reverse xs) (Cons x Nil)

    variable n : nat
    def insert : list nat -> nat -> list nat
        | Nil => λn. Cons n Nil
        | Cons x xs => λn. (COND (nat_le x n) (Cons x (insert xs n)) (Cons n (Cons x xs)))

    variable h : nat
    variable t : list nat
    def isort : list nat -> list nat
        | Nil => Nil
        | Cons h t => insert (isort t) h

    vartype b
    variable nil_case : b
    variable cons_case : a -> list a -> b
    def list_match: list a -> b -> (a -> list a -> b) -> b
        | Nil => λnil_case. λcons_case. nil_case
        | Cons x xs => λnil_case. λcons_case. cons_case x xs

    variable xs' : list nat
    variable x' : nat
    def sorted : list nat -> bool
        | Nil => T 
        | Cons h t => 
            (∧
                (list_match t T (λx'. λxs'. (nat_le h x')))
                (sorted t))

    variable n y' : nat
    variable xs ys ys' zs : list nat

    def merge_aux : nat -> list nat -> list nat -> option (list nat)
      | Zero => λxs. λys. None
      | Suc n => λxs. λys.
        list_match xs
            (Some ys)
            (λh. λt.
                (list_match ys
                    (Some (Cons h t))
                    (λy'. λys'.
                        COND (nat_lt h y')
                            (option_match (merge_aux n t (Cons y' ys'))
                                    (None)
                                    (λzs. Some (Cons h zs)))
                            (option_match (merge_aux n (Cons h t) ys')
                                    (None)
                                    (λzs. Some (Cons y' zs))))))

    def merge : list nat -> list nat -> list nat
        | xs =>
            λys. 
                option_match (merge_aux (Suc (plus (length xs) (length ys))) xs ys)
                    Nil 
                    (λzs. zs)

    def take : nat -> list nat -> list nat
        | Zero => λxs. Nil
        | Suc n => λxs.
            list_match xs
                (Nil)
                (λh. λt. Cons h (take n t))

    def drop : nat -> list nat -> list nat
        | Zero => λxs. xs
        | Suc n => λxs.
            list_match xs
                (Nil)
                (λh. λt. drop n t)
    
    variable half_length n : nat
    variable left right : list nat

    def merge_sort_aux : nat -> list nat -> option (list nat)
        | Zero => λxs. None
        | Suc n => λxs.
            COND (nat_le (length xs) (Suc Zero))
                (Some xs)
                ((λhalf_length.
                    option_match (merge_sort_aux n (take half_length xs))
                        (None)
                        (λleft.
                            option_match (merge_sort_aux n (drop half_length xs))
                                (None)
                                (λright. Some (merge left right))
                        )
                ) (div (length xs) (Suc (Suc Zero))))

    def merge_sort : list nat -> list nat
        | xs => 
            option_match (merge_sort_aux (Suc (length xs)) xs)
                Nil
                (λzs. zs)

    |}

  let _ =
    match Elaborator.elaborate_string prg with
    | Ok v -> v
    | Error e -> failwith @@ Printing.print_error e

  let list_def = Hashtbl.find the_inductives "list"
  let nil = make_const "Nil" [] |> Result.get_ok
  let cons = make_const "Cons" [] |> Result.get_ok
  let length = make_const "length" [] |> Result.get_ok
  let append = make_const "append" [] |> Result.get_ok
  let reverse = make_const "reverse" [] |> Result.get_ok
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

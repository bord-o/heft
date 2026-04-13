open Heft
open Derived
open Kernel
open Tactic
open Synth
open Heft_theories
open Auto

let () = Functions.init ()
let () = Options.init ()
let () = Lists.init ()
let () = Nats.init ()
let () = Conds.init ()
let () = Pairs.init ()

let%expect_test "synth goal setup" =
  let goal =
    make_goal
      [%term
        exists (fun (nil_case : nat) ->
            (g : 'a list -> nat) []
            = nil_case
            ==> ((g : 'a list -> nat) [] = Zero))]
  in

  let proof =
    with_term [%term 0n] exists_tac >> intro_tac >> simp_tac ~with_asms:true
  in

  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∃nil_case. g Nil = nil_case ==> g Nil = Zero

    Proof Complete!
    with fuel: 21
    |}]

let%expect_test "synth goal setup full" =
  let open Nats in
  let open Lists in
  let goal =
    make_goal
      [%term
        exists
          (fun (nil_case : nat) (cons_case : 'a -> 'a list -> nat -> nat) ->
            (g : 'a list -> nat) []
            = nil_case
            ==> (forall (fun (x : 'a) (xs : 'a list) ->
                     (g : 'a list -> nat) (x :: xs)
                     = cons_case x xs ((g : 'a list -> nat) xs))
                ==> ((g : 'a list -> nat) [ (x : 'a) ] = 1n
                    && (g : 'a list -> nat) [ (x : 'a); (y : 'a) ] = 2n)))]
  in

  let a_v = Var ("a", a) in
  let b_v = Var ("b", TyCon ("list", [ a ])) in
  let q_v = Var ("q", nat_ty) in
  let cons_witness =
    Result.get_ok
      (make_lam a_v
         (Result.get_ok
            (make_lam b_v (Result.get_ok (make_lam q_v (App (suc, q_v)))))))
  in
  (* let cons_ty = type_of_term cons_witness |> Result.get_ok in *)
  (* print_endline @@ Printing.pretty_print_hol_type cons_ty; *)

  let proof =
    with_term zero exists_tac
    >> with_term cons_witness exists_tac
    >> intros_tac >> auto_dfs_tac
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    ========================================
    ∃nil_case. ∃cons_case. g Nil = nil_case ==> (∀x. ∀xs. g (Cons x xs) = cons_case x xs (g xs)) ==> g (Cons x Nil) = Suc Zero ∧ g (Cons x (Cons y Nil)) = Suc (Suc Zero)

    Proof Complete!
    with fuel: 84
    |}]

(* ----------------------------------------------------------------------- *)
(* Helpers                                                                  *)
(* ----------------------------------------------------------------------- *)

let rec pp_term = function
  | Var (s, _) -> s
  | Const (s, _) -> s
  | App (f, a) -> "(" ^ pp_term f ^ " " ^ pp_term a ^ ")"
  | Lam (v, b) -> "(λ" ^ pp_term v ^ ". " ^ pp_term b ^ ")"

let print_terms terms =
  if List.length terms = 0 then print_endline "(none)"
  else List.iter (fun t -> print_endline (pp_term t)) terms

let print_count terms = Printf.printf "%d terms\n" (List.length terms)

(* ======================================================================= *)
(* Edge cases                                                               *)
(* ======================================================================= *)

let%expect_test "depth 0 yields nothing" =
  let open Nats in
  enumerate [] nat_ty 0 |> print_terms;
  [%expect {| (none) |}]

(* ======================================================================= *)
(* Nat constructors                                                         *)
(* ======================================================================= *)

let%expect_test "nat depth 1: only Zero" =
  let open Nats in
  enumerate [] nat_ty 1 |> print_terms;
  [%expect {| Zero |}]

let%expect_test "nat depth 2: Zero and Suc Zero" =
  let open Nats in
  enumerate [] nat_ty 2 |> print_terms;
  [%expect {|
    Zero
    (Suc Zero)
  |}]

let%expect_test "nat depth 3: no beta-redexes" =
  let open Nats in
  enumerate [] nat_ty 3 |> print_terms;
  [%expect {|
    Zero
    (Suc Zero)
    (Suc (Suc Zero))
  |}]

(* ======================================================================= *)
(* Variables from context                                                   *)
(* ======================================================================= *)

let%expect_test "context variable returned at depth 1" =
  let open Nats in
  enumerate [ ("n", nat_ty) ] nat_ty 1 |> print_terms;
  [%expect {|
    n
    Zero
  |}]

let%expect_test "wrong type variable not returned" =
  let open Nats in
  enumerate [ ("b", bool_ty) ] nat_ty 1 |> print_terms;
  [%expect {| Zero |}]

let%expect_test "context var plus constructors at depth 2" =
  let open Nats in
  enumerate [ ("n", nat_ty) ] nat_ty 2 |> print_terms;
  [%expect {|
    n
    Zero
    (Suc n)
    (Suc Zero)
  |}]

let%expect_test "two nat vars at depth 1" =
  let open Nats in
  enumerate [ ("x", nat_ty); ("y", nat_ty) ] nat_ty 1 |> print_terms;
  [%expect {|
    x
    y
    Zero
  |}]

(* ======================================================================= *)
(* List constructors                                                        *)
(* ======================================================================= *)

let%expect_test "list nat depth 1: only Nil" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  enumerate [] list_nat 1 |> print_terms;
  [%expect {| Nil |}]

let%expect_test "list nat depth 2" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  enumerate [] list_nat 2 |> print_terms;
  [%expect {|
    Nil
    ((Cons Zero) Nil)
  |}]

let%expect_test "list nat depth 3" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let terms = enumerate [] list_nat 3 in
  print_count terms;
  print_terms terms;
  [%expect
    {|
    5 terms
    Nil
    ((Cons Zero) Nil)
    ((Cons Zero) ((Cons Zero) Nil))
    ((Cons (Suc Zero)) Nil)
    ((Cons (Suc Zero)) ((Cons Zero) Nil))
    |}]

(* ======================================================================= *)
(* Lambda abstractions                                                      *)
(* ======================================================================= *)

let%expect_test "nat -> nat depth 2: identity and const Zero" =
  let open Nats in
  enumerate [] (make_fun_ty nat_ty nat_ty) 2 |> print_terms;
  [%expect {|
    (λn. n)
    (λn. Zero)
  |}]

let%expect_test "nat -> nat depth 3: includes Suc" =
  let open Nats in
  enumerate [] (make_fun_ty nat_ty nat_ty) 3 |> print_terms;
  [%expect
    {|
    (λn. n)
    (λn. Zero)
    (λn. (Suc n))
    (λn. (Suc Zero))
  |}]

let%expect_test "bool -> bool depth 2: only identity" =
  enumerate [] (make_fun_ty bool_ty bool_ty) 2 |> print_terms;
  [%expect {| (λb. b) |}]

(* ======================================================================= *)
(* Extra constants: basic                                                   *)
(* ======================================================================= *)

let%expect_test "bool with T and F as extras" =
  let extras = [ ("T", bool_ty); ("F", bool_ty) ] in
  enumerate ~extra:extras [] bool_ty 1 |> print_terms;
  [%expect {|
    F
    T
  |}]

let%expect_test "pair nat bool depth 2 with T F extras" =
  let open Nats in
  let _ = Lists.list_def in
  let extras = [ ("T", bool_ty); ("F", bool_ty) ] in
  let pair_ty = TyCon ("pair", [ nat_ty; bool_ty ]) in
  enumerate ~extra:extras [] pair_ty 2 |> print_terms;
  [%expect {|
    ((Pair Zero) F)
    ((Pair Zero) T)
    |}]

let%expect_test "pair nat bool depth 3 with T F extras" =
  let open Nats in
  let _ = Lists.list_def in
  let extras = [ ("T", bool_ty); ("F", bool_ty) ] in
  let pair_ty = TyCon ("pair", [ nat_ty; bool_ty ]) in
  let terms = enumerate ~extra:extras [] pair_ty 3 in
  print_count terms;
  print_terms terms;
  [%expect
    {|
    4 terms
    ((Pair Zero) F)
    ((Pair Zero) T)
    ((Pair (Suc Zero)) F)
    ((Pair (Suc Zero)) T)
    |}]

(* ======================================================================= *)
(* Extra constants: curried functions                                       *)
(* ======================================================================= *)

let%expect_test "plus as extra: nat terms at depth 3" =
  let open Nats in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let terms = enumerate ~extra:extras [] nat_ty 3 in
  print_terms terms;
  [%expect
    {|
    Zero
    (Suc Zero)
    (Suc (Suc Zero))
    ((plus Zero) Zero)
    ((plus Zero) (Suc Zero))
    ((plus (Suc Zero)) Zero)
    |}]

let%expect_test "Suc as extra gives same results as constructor" =
  let open Nats in
  let suc_ty = make_fun_ty nat_ty nat_ty in
  let extras = [ ("Suc", suc_ty) ] in
  let terms = enumerate ~extra:extras [] nat_ty 2 in
  print_terms terms;
  [%expect {|
    Zero
    (Suc Zero)
  |}]

(* ======================================================================= *)
(* Extra constants: list functions                                          *)
(* ======================================================================= *)

let%expect_test "append as extra: list nat depth 3 with context" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let append_ty = make_fun_ty list_nat (make_fun_ty list_nat list_nat) in
  let extras = [ ("append", append_ty) ] in
  let ctx = [ ("xs", list_nat) ] in
  let terms = enumerate ~extra:extras ctx list_nat 2 in
  print_terms terms;
  [%expect {|
    xs
    Nil
    ((Cons Zero) xs)
    ((Cons Zero) Nil)
    |}]

let%expect_test "length as extra: nat from list context" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let length_ty = make_fun_ty list_nat nat_ty in
  let extras = [ ("length", length_ty) ] in
  let ctx = [ ("xs", list_nat) ] in
  let terms = enumerate ~extra:extras ctx nat_ty 2 in
  print_terms terms;
  [%expect {|
    Zero
    (Suc Zero)
    (length xs)
    (length Nil)
    |}]

let%expect_test "reverse and append as extras" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let append_ty = make_fun_ty list_nat (make_fun_ty list_nat list_nat) in
  let reverse_ty = make_fun_ty list_nat list_nat in
  let extras = [ ("append", append_ty); ("reverse", reverse_ty) ] in
  let ctx = [ ("xs", list_nat) ] in
  let terms = enumerate ~extra:extras ctx list_nat 2 in
  print_terms terms;
  [%expect
    {|
    xs
    Nil
    (reverse xs)
    (reverse Nil)
    ((Cons Zero) xs)
    ((Cons Zero) Nil)
    |}]

(* ======================================================================= *)
(* Extra constants: partial application as target                           *)
(* ======================================================================= *)

let%expect_test "partial application: plus as nat -> nat" =
  let open Nats in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let fn_ty = make_fun_ty nat_ty nat_ty in
  let terms = enumerate ~extra:extras [] fn_ty 2 in
  print_terms terms;
  [%expect {|
    (plus Zero)
    (λn. n)
    (λn. Zero)
    |}]

(* ======================================================================= *)
(* Higher-order types                                                       *)
(* ======================================================================= *)

let%expect_test "higher order: (nat -> nat) -> nat -> nat depth 3" =
  let open Nats in
  let fn_ty = make_fun_ty nat_ty nat_ty in
  let hof_ty = make_fun_ty fn_ty (make_fun_ty nat_ty nat_ty) in
  let terms = enumerate [] hof_ty 3 in
  print_count terms;
  print_terms terms;
  [%expect
    {|
    3 terms
    (λf. f)
    (λf. (λn. n))
    (λf. (λn. Zero))
    |}]

(* ======================================================================= *)
(* Beta normalization                                                       *)
(* ======================================================================= *)

let%expect_test "no beta-redexes in output at depth 3" =
  let open Nats in
  let terms = enumerate [] nat_ty 3 in
  let has_redex =
    List.exists
      (fun t -> match t with App (Lam _, _) -> true | _ -> false)
      terms
  in
  Printf.printf "contains beta-redex: %b\n" has_redex;
  [%expect {| contains beta-redex: false |}]

let%expect_test "no beta-redexes in list output at depth 3" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let terms = enumerate [] list_nat 3 in
  let rec has_redex = function
    | App (Lam _, _) -> true
    | App (f, a) -> has_redex f || has_redex a
    | Lam (_, b) -> has_redex b
    | _ -> false
  in
  let any_redex = List.exists has_redex terms in
  Printf.printf "contains beta-redex: %b\n" any_redex;
  [%expect {| contains beta-redex: false |}]

(* ======================================================================= *)
(* All generated terms are well-typed                                       *)
(* ======================================================================= *)

let%expect_test "all nat terms well-typed" =
  let open Nats in
  let terms = enumerate [] nat_ty 3 in
  let all_ok =
    List.for_all
      (fun t ->
        match type_of_term t with Ok ty -> ty = nat_ty | Error _ -> false)
      terms
  in
  Printf.printf "all well-typed: %b\n" all_ok;
  [%expect {| all well-typed: true |}]

let%expect_test "all function terms well-typed" =
  let open Nats in
  let fn_ty = make_fun_ty nat_ty nat_ty in
  let terms = enumerate [] fn_ty 3 in
  let all_ok =
    List.for_all
      (fun t ->
        match type_of_term t with Ok ty -> ty = fn_ty | Error _ -> false)
      terms
  in
  Printf.printf "all well-typed: %b\n" all_ok;
  [%expect {| all well-typed: true |}]

let%expect_test "all extra-constant terms well-typed" =
  let open Nats in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let terms = enumerate ~extra:extras [ ("n", nat_ty) ] nat_ty 3 in
  let all_ok =
    List.for_all
      (fun t ->
        match type_of_term t with Ok ty -> ty = nat_ty | Error _ -> false)
      terms
  in
  Printf.printf "all well-typed: %b\n" all_ok;
  [%expect {| all well-typed: true |}]

(* ======================================================================= *)
(* No duplicates                                                            *)
(* ======================================================================= *)

let%expect_test "no duplicates in output" =
  let open Nats in
  let terms = enumerate [] nat_ty 4 in
  let unique = List.sort_uniq compare terms in
  Printf.printf "count: %d, unique: %d\n" (List.length terms)
    (List.length unique);
  [%expect {| count: 4, unique: 4 |}]

(* ======================================================================= *)
(* Growth sanity checks                                                     *)
(* ======================================================================= *)

let%expect_test "nat term counts by depth" =
  let open Nats in
  for d = 0 to 5 do
    let n = List.length (enumerate [] nat_ty d) in
    Printf.printf "depth %d: %d terms\n" d n
  done;
  [%expect
    {|
    depth 0: 0 terms
    depth 1: 1 terms
    depth 2: 2 terms
    depth 3: 3 terms
    depth 4: 4 terms
    depth 5: 5 terms
  |}]

let%expect_test "nat -> nat term counts by depth" =
  let open Nats in
  let fn_ty = make_fun_ty nat_ty nat_ty in
  for d = 0 to 4 do
    let n = List.length (enumerate [] fn_ty d) in
    Printf.printf "depth %d: %d terms\n" d n
  done;
  [%expect
    {|
    depth 0: 0 terms
    depth 1: 0 terms
    depth 2: 2 terms
    depth 3: 4 terms
    depth 4: 6 terms
    |}]

let%expect_test "test cons case" =
  let open Nats in
  let open Lists in
  let cons_case_ty =
    make_fun_ty a (make_fun_ty list_a (make_fun_ty nat_ty nat_ty))
  in
  let extras = [] in
  let terms = enumerate ~extra:extras [] cons_case_ty 5 in
  print_terms terms;
  [%expect
    {|
    (λa. (λl. (λn. n)))
    (λa. (λl. (λn. Zero)))
    (λa. (λl. (λn. (Suc n))))
    (λa. (λl. (λn. (Suc Zero))))
    |}]

let%expect_test "synth goal enumerate" =
  let goal =
    make_goal
      [%term
        exists
          (fun (nil_case : nat) (cons_case : 'a -> 'a list -> nat -> nat) ->
            (g : 'a list -> nat) []
            = nil_case
            ==> (forall (fun (x : 'a) (xs : 'a list) ->
                     (g : 'a list -> nat) (x :: xs)
                     = cons_case x xs ((g : 'a list -> nat) xs))
                ==> ((g : 'a list -> nat) [ (x : 'a) ] = 1n
                    && (g : 'a list -> nat) [ (x : 'a); (y : 'a) ] = 2n)))]
  in

  let proof =
    with_best_first
      (try_ (with_synthetic_term 5 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 5 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λa. λl. λn. Suc n
    success with chosen term: Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g Nil = nil_case ==> (∀x. ∀xs. g (Cons x xs) = cons_case x xs (g xs)) ==> g (Cons x Nil) = Suc Zero ∧ g (Cons x (Cons y Nil)) = Suc (Suc Zero)

    Proof Complete!
    with fuel: 828
    |}]

let%expect_test "synth append" =
  let goal =
    make_goal
      [%term
        exists
          (fun
            (nil_case : 'a list -> 'a list)
            (cons_case : 'a -> 'a list -> 'a list -> 'a list)
          ->
            forall (fun (ys : 'a list) ->
                (g : 'a list -> 'a list -> 'a list) [] ys = nil_case ys)
            ==> (forall (fun (x : 'a) (xs : 'a list) (ys : 'a list) ->
                     (g : 'a list -> 'a list -> 'a list) (x :: xs) ys
                     = cons_case x xs
                         ((g : 'a list -> 'a list -> 'a list) xs ys))
                ==> ((g : 'a list -> 'a list -> 'a list) [] [ (x : 'a) ]
                     = [ (x : 'a) ]
                    && (g : 'a list -> 'a list -> 'a list)
                         [ (x : 'a) ]
                         [ (y : 'a) ]
                       = [ (x : 'a); (y : 'a) ])))]
  in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 5 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λa. λl. λl0. Cons a l0
    success with chosen term: λl. l
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. (∀ys. g Nil ys = nil_case ys) ==> (∀x. ∀xs. ∀ys. g (Cons x xs) ys = cons_case x xs (g xs ys)) ==> g Nil (Cons x Nil) = Cons x Nil ∧ g (Cons x Nil) (Cons y Nil) = Cons x (Cons y Nil)

    Proof Complete!
    with fuel: 1245
    |}]

let%expect_test "synth reverse" =
  let open Lists in
  let _ = list_def in
  let a = make_vartype "a" in
  let list_a = TyCon ("list", [ a ]) in
  let append_ty = make_fun_ty list_a (make_fun_ty list_a list_a) in
  let extra = [ ("append", append_ty) ] in

  let goal =
    make_goal
      [%term
        exists
          (fun
            (nil_case : 'a list)
            (cons_case : 'a -> 'a list -> 'a list -> 'a list)
          ->
            (g : 'a list -> 'a list) []
            = nil_case
            ==> (forall (fun (x : 'a) (xs : 'a list) ->
                     (g : 'a list -> 'a list) (x :: xs)
                     = cons_case x xs ((g : 'a list -> 'a list) xs))
                ==> ((g : 'a list -> 'a list) [ (x : 'a); (y : 'a) ]
                    = [ (y : 'a); (x : 'a) ])))]
  in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra 6 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    success with chosen term: λa. λl. λl0. append l0 (Cons a Nil)
    success with chosen term: Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g Nil = nil_case ==> (∀x. ∀xs. g (Cons x xs) = cons_case x xs (g xs)) ==> g (Cons x (Cons y Nil)) = Cons y (Cons x Nil)

    Proof Complete!
    with fuel: 5821
    |}]

let%expect_test "synth mult" =
  let open Nats in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let goal =
    make_goal
      [%term
        exists (fun (nil_case : nat -> nat) (suc_case : nat -> nat -> nat) ->
            forall (fun (n : nat) ->
                (g : nat -> nat -> nat) Zero n = nil_case n)
            ==> (forall (fun (m : nat) (n : nat) ->
                     (g : nat -> nat -> nat) (Suc m) n
                     = suc_case n ((g : nat -> nat -> nat) m n))
                ==> ((g : nat -> nat -> nat) 0n 2n = 0n
                    && (g : nat -> nat -> nat) 2n 3n = 6n)))]
  in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra:extras 3 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra:extras 4 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: plus
    success with chosen term: λn. Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃suc_case. (∀n. g Zero n = nil_case n) ==> (∀m. ∀n. g (Suc m) n = suc_case n (g m n)) ==> g Zero (Suc (Suc Zero)) = Zero ∧ g (Suc (Suc Zero)) (Suc (Suc (Suc Zero))) = Suc (Suc (Suc (Suc (Suc (Suc Zero)))))

    Proof Complete!
    with fuel: 592
    |}]

let%expect_test "synth sum" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let goal =
    make_goal
      [%term
        exists (fun (nil_case : nat) (cons_case : nat -> nat -> nat) ->
            (g : nat list -> nat) []
            = nil_case
            ==> (forall (fun (x : nat) (xs : nat list) ->
                     (g : nat list -> nat) ((x : nat) :: xs)
                     = cons_case x ((g : nat list -> nat) xs))
                ==> ((g : nat list -> nat) [ 1n; 2n; 3n ] = 6n)))]
  in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra:extras 5 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra:extras 5 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    success with chosen term: plus
    success with chosen term: Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g Nil = nil_case ==> (∀x. ∀xs. g (Cons x xs) = cons_case x (g xs)) ==> g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil))) = Suc (Suc (Suc (Suc (Suc (Suc Zero)))))

    Proof Complete!
    with fuel: 99
    |}]

let nat_ty = Nats.nat_ty
let zero = Nats.zero
let suc = Nats.suc
let n i = Nats.nat_of_int i
let list_nat = TyCon ("list", [ nat_ty ])
let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] Lists.nil)

let cons_nat =
  Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] Lists.cons)

let mk_list elems =
  List.fold_right
    (fun x acc ->
      Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
    elems nil_nat

let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)
let plus_extra = [ ("plus", plus_ty) ]
let append_ty = make_fun_ty list_nat (make_fun_ty list_nat list_nat)
let append_extra = [ ("append", append_ty) ]

(* ======================================================================= *)
(* Test: length                                                             *)
(* ======================================================================= *)

let%expect_test "synth length via make_synthesis_goal" =
  let func_type = make_fun_ty list_nat nat_ty in
  let test_cases =
    [ ([ mk_list [ n 1 ] ], n 1); ([ mk_list [ n 1; n 2 ] ], n 2) ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 5 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 5 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λn. λn0. Suc n0
    success with chosen term: Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Suc Zero) Nil) = Suc Zero ∧ g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) Nil)) = Suc (Suc Zero)

    Proof Complete!
    with fuel: 698
    |}]

(* ======================================================================= *)
(* Test: sum                                                                *)
(* ======================================================================= *)

let%expect_test "synth sum via make_synthesis_goal" =
  let func_type = make_fun_ty list_nat nat_ty in
  let test_cases = [ ([ mk_list [ n 1; n 2; n 3 ] ], n 6) ] in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_
         (with_synthetic_term ~extra:plus_extra 5 (with_info_trace exists_tac))
      >> try_
           (with_synthetic_term ~extra:plus_extra 5
              (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    success with chosen term: plus
    success with chosen term: Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil))) = Suc (Suc (Suc (Suc (Suc (Suc Zero)))))

    Proof Complete!
    with fuel: 99
    |}]

(* ======================================================================= *)
(* Test: append                                                             *)
(* ======================================================================= *)

let%expect_test "synth append via make_synthesis_goal" =
  let func_type = make_fun_ty list_nat (make_fun_ty list_nat list_nat) in
  let test_cases =
    [ ([ mk_list [ n 1 ]; mk_list [ n 2 ] ], mk_list [ n 1; n 2 ]) ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 6 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      refl_tac
    success with chosen term: λn. λl. λl0. Cons n l0
    success with chosen term: λl. l
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. (∀y0. g Nil y0 = Nil_case y0) ==> (∀c0. ∀c1. ∀y0. g (Cons c0 c1) y0 = Cons_case c0 y0 (g c1 y0)) ==> g (Cons (Suc Zero) Nil) (Cons (Suc (Suc Zero)) Nil) = Cons (Suc Zero) (Cons (Suc (Suc Zero)) Nil)

    Proof Complete!
    with fuel: 559
    |}]

(* ======================================================================= *)
(* Test: mult                                                               *)
(* ======================================================================= *)

let%expect_test "synth mult via make_synthesis_goal" =
  let func_type = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let test_cases = [ ([ n 0; n 2 ], n 0); ([ n 2; n 3 ], n 6) ] in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_
         (with_synthetic_term ~extra:plus_extra 3 (with_info_trace exists_tac))
      >> try_
           (with_synthetic_term ~extra:plus_extra 5
              (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: plus
    success with chosen term: λn. Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Zero_case. ∃Suc_case. (∀y0. g Zero y0 = Zero_case y0) ==> (∀c0. ∀y0. g (Suc c0) y0 = Suc_case y0 (g c0 y0)) ==> g Zero (Suc (Suc Zero)) = Zero ∧ g (Suc (Suc Zero)) (Suc (Suc (Suc Zero))) = Suc (Suc (Suc (Suc (Suc (Suc Zero)))))

    Proof Complete!
    with fuel: 592
    |}]

(* ======================================================================= *)
(* Test: reverse                                                            *)
(* ======================================================================= *)

let%expect_test "synth reverse via make_synthesis_goal" =
  let func_type = make_fun_ty list_nat list_nat in
  let test_cases = [ ([ mk_list [ n 1; n 2 ] ], mk_list [ n 2; n 1 ]) ] in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_
         (with_synthetic_term ~extra:append_extra 3
            (with_info_trace exists_tac))
      >> try_
           (with_synthetic_term ~extra:append_extra 6
              (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      refl_tac
    success with chosen term: λn. λl. append l (Cons n Nil)
    success with chosen term: Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) Nil)) = Cons (Suc (Suc Zero)) (Cons (Suc Zero) Nil)

    Proof Complete!
    with fuel: 4095
    |}]

let%expect_test "synth stutter via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil) in
  let cons_nat =
    Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)
  in
  let mk_list elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
      elems nil_nat
  in
  let func_type = make_fun_ty list_nat list_nat in
  let test_cases =
    [
      ([ mk_list [ n 1; n 2; n 3 ] ], mk_list [ n 1; n 1; n 2; n 2; n 3; n 3 ]);
    ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 6 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      refl_tac
    success with chosen term: λn. λl. Cons n (Cons n l)
    success with chosen term: Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil))) = Cons (Suc Zero) (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) (Cons (Suc (Suc (Suc Zero))) Nil)))))

    Proof Complete!
    with fuel: 1096
    |}]

let%expect_test "synth map via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil) in
  let cons_nat =
    Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)
  in
  let mk_list elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
      elems nil_nat
  in
  let f_ty = make_fun_ty nat_ty nat_ty in
  let func_type = make_fun_ty list_nat (make_fun_ty f_ty list_nat) in
  let suc_const = Result.get_ok (make_const "Suc" []) in
  let test_cases =
    [
      ([ mk_list [ n 1; n 2; n 3 ]; suc_const ], mk_list [ n 2; n 3; n 4 ]);
      ( [ mk_list [ n 1; n 2; n 3 ]; make_app plus (n 2) |> Result.get_ok ],
        mk_list [ n 3; n 4; n 5 ] );
    ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 6 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λn. λf. λl. Cons (f n) l
    success with chosen term: λf. Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. (∀y0. g Nil y0 = Nil_case y0) ==> (∀c0. ∀c1. ∀y0. g (Cons c0 c1) y0 = Cons_case c0 y0 (g c1 y0)) ==> g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil))) Suc = Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) (Cons (Suc (Suc (Suc (Suc Zero)))) Nil)) ∧ g (Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil))) (plus (Suc (Suc Zero))) = Cons (Suc (Suc (Suc Zero))) (Cons (Suc (Suc (Suc (Suc Zero)))) (Cons (Suc (Suc (Suc (Suc (Suc Zero))))) Nil))

    Proof Complete!
    with fuel: 1336
    |}]

let%expect_test "synth replicate via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil) in
  let cons_nat =
    Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)
  in
  let mk_list elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
      elems nil_nat
  in
  let func_type = make_fun_ty nat_ty (make_fun_ty nat_ty list_nat) in
  let test_cases = [ ([ n 3; n 5 ], mk_list [ n 5; n 5; n 5 ]) ] in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term 2 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term 4 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      refl_tac
    success with chosen term: λn. λl. Cons n l
    success with chosen term: λn. Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Zero_case. ∃Suc_case. (∀y0. g Zero y0 = Zero_case y0) ==> (∀c0. ∀y0. g (Suc c0) y0 = Suc_case y0 (g c0 y0)) ==> g (Suc (Suc (Suc Zero))) (Suc (Suc (Suc (Suc (Suc Zero))))) = Cons (Suc (Suc (Suc (Suc (Suc Zero))))) (Cons (Suc (Suc (Suc (Suc (Suc Zero))))) (Cons (Suc (Suc (Suc (Suc (Suc Zero))))) Nil))

    Proof Complete!
    with fuel: 385
    |}]

(* let%expect_test "synth fib_helper via make_synthesis_goal" = *)
(*   let open Nats in *)
(*   let pair_nat_nat = TyCon ("pair", [ nat_ty; nat_ty ]) in *)
(*   let pair_const = *)
(*     Result.get_ok *)
(*       (type_inst *)
(*          [ (make_vartype "a", nat_ty); (make_vartype "b", nat_ty) ] *)
(*          (Result.get_ok (make_const "pair" []))) *)
(*   in *)
(*   let mk_pair a b = *)
(*     Result.get_ok (make_app (Result.get_ok (make_app pair_const a)) b) *)
(*   in *)
(*   let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in *)
(*   let fst_ty = make_fun_ty pair_nat_nat nat_ty in *)
(*   let snd_ty = make_fun_ty pair_nat_nat nat_ty in *)
(*   let pair_ty = make_fun_ty nat_ty (make_fun_ty nat_ty pair_nat_nat) in *)
(*   let extras = *)
(*     [ ("plus", plus_ty); ("fst", fst_ty); ("snd", snd_ty); ("pair", pair_ty) ] *)
(*   in *)
(*   let func_type = make_fun_ty nat_ty pair_nat_nat in *)
(*   let test_cases = *)
(*     [ *)
(*       ([ n 0 ], mk_pair (n 0) (n 1)); *)
(*       ([ n 1 ], mk_pair (n 1) (n 1)); *)
(*       (* ([ n 5 ], mk_pair (n 5) (n 8)); *) *)
(*     ] *)
(*   in *)
(*   let goal_tm = make_synthesis_goal ~func_type ~test_cases in *)
(*   let goal = ([], goal_tm) in *)
(*   let proof = *)
(*     with_best_first *)
(*       (try_ *)
(*          (with_info_trace *)
(*             (with_synthetic_term ~extra:extras 3 (with_info_trace exists_tac))) *)
(*       >> try_ *)
(*            (with_info_trace *)
(*               (with_synthetic_term ~extra:extras 7 (with_info_trace exists_tac))) *)
(*       >> intros_tac >> auto_dfs_tac) *)
(*   in *)
(*   run_proof goal proof; *)
(*   [%expect {| |}] *)

let%expect_test "synth list_sum_pairs via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let pair_nat_nat = TyCon ("pair", [ nat_ty; nat_ty ]) in
  let list_pair = TyCon ("list", [ pair_nat_nat ]) in
  let nil_lp =
    Result.get_ok (type_inst [ (make_vartype "a", pair_nat_nat) ] nil)
  in
  let cons_lp =
    Result.get_ok (type_inst [ (make_vartype "a", pair_nat_nat) ] cons)
  in
  let pair_const =
    Result.get_ok
      (type_inst
         [ (make_vartype "a", nat_ty); (make_vartype "b", nat_ty) ]
         (Result.get_ok (make_const "Pair" [])))
  in
  let mk_pair a b =
    Result.get_ok (make_app (Result.get_ok (make_app pair_const a)) b)
  in
  let mk_list_pair elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_lp x)) acc))
      elems nil_lp
  in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let fst_ty = make_fun_ty pair_nat_nat nat_ty in
  let snd_ty = make_fun_ty pair_nat_nat nat_ty in
  let extras = [ ("plus", plus_ty); ("fst", fst_ty); ("snd", snd_ty) ] in
  let func_type = make_fun_ty list_pair nat_ty in
  let test_cases =
    [
      (* (1,2) + (3,4) = 10 *)
      ([ mk_list_pair [ mk_pair (n 1) (n 2); mk_pair (n 3) (n 4) ] ], n 10);
      (* (5,0) = 5 *)
      ([ mk_list_pair [ mk_pair (n 5) (n 0) ] ], n 5);
    ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra:extras 3 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra:extras 6 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λp. plus (plus (fst p) (snd p))
    success with chosen term: Zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Pair (Suc Zero) (Suc (Suc Zero))) (Cons (Pair (Suc (Suc (Suc Zero))) (Suc (Suc (Suc (Suc Zero))))) Nil)) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))) ∧ g (Cons (Pair (Suc (Suc (Suc (Suc (Suc Zero))))) Zero) Nil) = Suc (Suc (Suc (Suc (Suc Zero))))

    Proof Complete!
    with fuel: 30569
    |}]

let%expect_test "synth insert via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil) in
  let cons_nat =
    Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)
  in
  let mk_list elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
      elems nil_nat
  in
  let bool_ty = Kernel.bool_ty in
  let cond_ty =
    make_fun_ty bool_ty (make_fun_ty list_nat (make_fun_ty list_nat list_nat))
  in
  let nat_le_ty = make_fun_ty nat_ty (make_fun_ty nat_ty bool_ty) in
  let extras = [ ("COND", cond_ty); ("nat_le", nat_le_ty) ] in
  (* insert : list nat -> nat -> list nat, recurse on list, carry nat *)
  let func_type = make_fun_ty list_nat (make_fun_ty nat_ty list_nat) in
  let test_cases =
    [
      (* insert [] 3 = [3] *)
      ([ mk_list []; n 3 ], mk_list [ n 3 ]);
      (* insert [1,3,5] 2 = [1,2,3,5] *)
      ([ mk_list [ n 1; n 3; n 5 ]; n 2 ], mk_list [ n 1; n 2; n 3; n 5 ]);
    ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let _goal = ([], goal_tm) in
  let _proof =
    with_best_first
      (try_ (with_synthetic_term ~extra:extras 6 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra:extras 8 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  ();
  (* run_proof goal proof; *)
  [%expect {| |}]

let%expect_test "synth isort via make_synthesis_goal" =
  let open Nats in
  let open Lists in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let nil_nat = Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] nil) in
  let cons_nat =
    Result.get_ok (type_inst [ (make_vartype "a", nat_ty) ] cons)
  in
  let mk_list elems =
    List.fold_right
      (fun x acc ->
        Result.get_ok (make_app (Result.get_ok (make_app cons_nat x)) acc))
      elems nil_nat
  in
  let insert_ty = make_fun_ty list_nat (make_fun_ty nat_ty list_nat) in
  let extras = [ ("insert", insert_ty) ] in
  let func_type = make_fun_ty list_nat list_nat in
  let test_cases =
    [
      ([ mk_list [ n 3; n 1; n 2 ] ], mk_list [ n 1; n 2; n 3 ]);
      ([ mk_list [] ], mk_list []);
    ]
  in
  let goal_tm = make_synthesis_goal ~func_type ~test_cases in
  let goal = ([], goal_tm) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra:extras 4 (with_info_trace exists_tac))
      >> try_ (with_synthetic_term ~extra:extras 5 (with_info_trace exists_tac))
      >> intros_tac >> auto_dfs_tac)
  in
  run_proof goal proof;
  [%expect
    {|
    Proof:
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      rewrite_tac >>
      beta_tac >>
      rewrite_tac >>
      conj_tac >>
      refl_tac >>
      refl_tac
    success with chosen term: λn. λl. insert l n
    success with chosen term: Nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃Nil_case. ∃Cons_case. g Nil = Nil_case ==> (∀c0. ∀c1. g (Cons c0 c1) = Cons_case c0 (g c1)) ==> g (Cons (Suc (Suc (Suc Zero))) (Cons (Suc Zero) (Cons (Suc (Suc Zero)) Nil))) = Cons (Suc Zero) (Cons (Suc (Suc Zero)) (Cons (Suc (Suc (Suc Zero))) Nil)) ∧ g Nil = Nil

    Proof Complete!
    with fuel: 11848
    |}]

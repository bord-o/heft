open Heft
open Kernel
open Tactic
open Synth

let%expect_test "synth goal setup" =
  let open Theories.NatTheory in
  let prg =
    {|
    vartype a 
    variable nil_case: nat
    variable g : list a -> nat

    theorem synthesize_length:
        (exists λnil_case.
            (imp
                (eq (g nil) (nil_case))
                (eq (g nil) (zero))
            )
        )

  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in

  let proof =
    with_arbitrary_term zero exists_tac >> intro_tac >> simp_tac ~with_asms:true
  in

  run_proof goal proof;
  [%expect
    {|
    ========================================
    ∃nil_case. g nil = nil_case ==> g nil = zero

    Proof Complete!
    with fuel: 21
    |}]

let%expect_test "synth goal setup full" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let prg =
    {|
    vartype a 
    variable nil_case : nat
    variable cons_case : a -> list a -> nat -> nat
    variable g : list a -> nat
    variable x : a
    variable y : a
    variable xs : list a
    theorem synthesize_length:
        (exists (λnil_case.
            (exists (λcons_case.
                (imp (eq (g nil) nil_case)
                (imp (forall (λx. (forall (λxs. (eq (g (cons x xs)) (cons_case x xs (g xs)))))))
                    (conj 
                        (eq (g (cons x nil)) (suc zero))
                        (eq (g (cons x (cons y nil))) (suc (suc zero))))
                ))
            ))
        ))
  |}
  in

  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in

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
    with_arbitrary_term zero exists_tac
    >> with_arbitrary_term cons_witness exists_tac
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
    ∃nil_case. ∃cons_case. g nil = nil_case ==> (∀x. ∀xs. g (cons x xs) = cons_case x xs (g xs)) ==> g (cons x nil) = suc zero ∧ g (cons x (cons y nil)) = suc (suc zero)

    Proof Complete!
    with fuel: 81
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
  let open Theories.NatTheory in
  enumerate [] nat_ty 0 |> print_terms;
  [%expect {| (none) |}]

(* ======================================================================= *)
(* Nat constructors                                                         *)
(* ======================================================================= *)

let%expect_test "nat depth 1: only zero" =
  let open Theories.NatTheory in
  enumerate [] nat_ty 1 |> print_terms;
  [%expect {| zero |}]

let%expect_test "nat depth 2: zero and suc zero" =
  let open Theories.NatTheory in
  enumerate [] nat_ty 2 |> print_terms;
  [%expect {|
    zero
    (suc zero)
  |}]

let%expect_test "nat depth 3: no beta-redexes" =
  let open Theories.NatTheory in
  enumerate [] nat_ty 3 |> print_terms;
  [%expect {|
    zero
    (suc zero)
    (suc (suc zero))
  |}]

(* ======================================================================= *)
(* Variables from context                                                   *)
(* ======================================================================= *)

let%expect_test "context variable returned at depth 1" =
  let open Theories.NatTheory in
  enumerate [ ("n", nat_ty) ] nat_ty 1 |> print_terms;
  [%expect {|
    n
    zero
  |}]

let%expect_test "wrong type variable not returned" =
  let open Theories.NatTheory in
  enumerate [ ("b", bool_ty) ] nat_ty 1 |> print_terms;
  [%expect {| zero |}]

let%expect_test "context var plus constructors at depth 2" =
  let open Theories.NatTheory in
  enumerate [ ("n", nat_ty) ] nat_ty 2 |> print_terms;
  [%expect {|
    n
    zero
    (suc n)
    (suc zero)
  |}]

let%expect_test "two nat vars at depth 1" =
  let open Theories.NatTheory in
  enumerate [ ("x", nat_ty); ("y", nat_ty) ] nat_ty 1 |> print_terms;
  [%expect {|
    x
    y
    zero
  |}]

(* ======================================================================= *)
(* List constructors                                                        *)
(* ======================================================================= *)

let%expect_test "list nat depth 1: only nil" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  enumerate [] list_nat 1 |> print_terms;
  [%expect {| nil |}]

let%expect_test "list nat depth 2" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  enumerate [] list_nat 2 |> print_terms;
  [%expect {|
    nil
    ((cons zero) nil)
  |}]

let%expect_test "list nat depth 3" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let terms = enumerate [] list_nat 3 in
  print_count terms;
  print_terms terms;
  [%expect
    {|
    5 terms
    nil
    ((cons zero) nil)
    ((cons zero) ((cons zero) nil))
    ((cons (suc zero)) nil)
    ((cons (suc zero)) ((cons zero) nil))
    |}]

(* ======================================================================= *)
(* Lambda abstractions                                                      *)
(* ======================================================================= *)

let%expect_test "nat -> nat depth 2: identity and const zero" =
  let open Theories.NatTheory in
  enumerate [] (make_fun_ty nat_ty nat_ty) 2 |> print_terms;
  [%expect {|
    (λn. n)
    (λn. zero)
  |}]

let%expect_test "nat -> nat depth 3: includes suc" =
  let open Theories.NatTheory in
  enumerate [] (make_fun_ty nat_ty nat_ty) 3 |> print_terms;
  [%expect
    {|
    (λn. n)
    (λn. zero)
    (λn. (suc n))
    (λn. (suc zero))
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
  let open Theories.NatTheory in
  let open Theories.PairTheory in
  let _ = list_def in
  let extras = [ ("T", bool_ty); ("F", bool_ty) ] in
  let pair_ty = TyCon ("pair", [ nat_ty; bool_ty ]) in
  enumerate ~extra:extras [] pair_ty 2 |> print_terms;
  [%expect {|
    ((pair zero) F)
    ((pair zero) T)
  |}]

let%expect_test "pair nat bool depth 3 with T F extras" =
  let open Theories.NatTheory in
  let open Theories.PairTheory in
  let _ = list_def in
  let extras = [ ("T", bool_ty); ("F", bool_ty) ] in
  let pair_ty = TyCon ("pair", [ nat_ty; bool_ty ]) in
  let terms = enumerate ~extra:extras [] pair_ty 3 in
  print_count terms;
  print_terms terms;
  [%expect
    {|
    4 terms
    ((pair zero) F)
    ((pair zero) T)
    ((pair (suc zero)) F)
    ((pair (suc zero)) T)
  |}]

(* ======================================================================= *)
(* Extra constants: curried functions                                       *)
(* ======================================================================= *)

let%expect_test "plus as extra: nat terms at depth 3" =
  let open Theories.NatTheory in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let terms = enumerate ~extra:extras [] nat_ty 3 in
  print_terms terms;
  [%expect
    {|
    zero
    (suc zero)
    (suc (suc zero))
    ((plus zero) zero)
    ((plus zero) (suc zero))
    ((plus (suc zero)) zero)
    |}]

let%expect_test "suc as extra gives same results as constructor" =
  let open Theories.NatTheory in
  let suc_ty = make_fun_ty nat_ty nat_ty in
  let extras = [ ("suc", suc_ty) ] in
  let terms = enumerate ~extra:extras [] nat_ty 2 in
  print_terms terms;
  [%expect {|
    zero
    (suc zero)
  |}]

(* ======================================================================= *)
(* Extra constants: list functions                                          *)
(* ======================================================================= *)

let%expect_test "append as extra: list nat depth 3 with context" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let append_ty = make_fun_ty list_nat (make_fun_ty list_nat list_nat) in
  let extras = [ ("append", append_ty) ] in
  let ctx = [ ("xs", list_nat) ] in
  let terms = enumerate ~extra:extras ctx list_nat 2 in
  print_terms terms;
  [%expect {|
    xs
    nil
    ((cons zero) xs)
    ((cons zero) nil)
    |}]

let%expect_test "length as extra: nat from list context" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let list_nat = TyCon ("list", [ nat_ty ]) in
  let length_ty = make_fun_ty list_nat nat_ty in
  let extras = [ ("length", length_ty) ] in
  let ctx = [ ("xs", list_nat) ] in
  let terms = enumerate ~extra:extras ctx nat_ty 2 in
  print_terms terms;
  [%expect {|
    zero
    (length xs)
    (length nil)
    (suc zero)
  |}]

let%expect_test "reverse and append as extras" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
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
    nil
    (reverse xs)
    (reverse nil)
    ((cons zero) xs)
    ((cons zero) nil)
    |}]

(* ======================================================================= *)
(* Extra constants: partial application as target                           *)
(* ======================================================================= *)

let%expect_test "partial application: plus as nat -> nat" =
  let open Theories.NatTheory in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let fn_ty = make_fun_ty nat_ty nat_ty in
  let terms = enumerate ~extra:extras [] fn_ty 2 in
  print_terms terms;
  [%expect {|
    (plus zero)
    (λn. n)
    (λn. zero)
    |}]

(* ======================================================================= *)
(* Higher-order types                                                       *)
(* ======================================================================= *)

let%expect_test "higher order: (nat -> nat) -> nat -> nat depth 3" =
  let open Theories.NatTheory in
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
    (λf. (λn. zero))
    |}]

(* ======================================================================= *)
(* Beta normalization                                                       *)
(* ======================================================================= *)

let%expect_test "no beta-redexes in output at depth 3" =
  let open Theories.NatTheory in
  let terms = enumerate [] nat_ty 3 in
  let has_redex =
    List.exists
      (fun t -> match t with App (Lam _, _) -> true | _ -> false)
      terms
  in
  Printf.printf "contains beta-redex: %b\n" has_redex;
  [%expect {| contains beta-redex: false |}]

let%expect_test "no beta-redexes in list output at depth 3" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
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
  let open Theories.NatTheory in
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
  let open Theories.NatTheory in
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
  let open Theories.NatTheory in
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
  let open Theories.NatTheory in
  let terms = enumerate [] nat_ty 4 in
  let unique = List.sort_uniq compare terms in
  Printf.printf "count: %d, unique: %d\n" (List.length terms)
    (List.length unique);
  [%expect {| count: 4, unique: 4 |}]

(* ======================================================================= *)
(* Growth sanity checks                                                     *)
(* ======================================================================= *)

let%expect_test "nat term counts by depth" =
  let open Theories.NatTheory in
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
  let open Theories.NatTheory in
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
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let cons_case_ty =
    make_fun_ty a (make_fun_ty list_a (make_fun_ty nat_ty nat_ty))
  in
  let extras = [] in
  let terms = enumerate ~extra:extras [] cons_case_ty 5 in
  print_terms terms;
  [%expect
    {|
    (λa. (λl. (λn. n)))
    (λa. (λl. (λn. zero)))
    (λa. (λl. (λn. (suc n))))
    (λa. (λl. (λn. (suc zero))))
    |}]

let%expect_test "synth goal enumerate" =
  (* let open Theories.NatTheory in *)
  let prg =
    {|
    vartype a 
    variable nil_case : nat
    variable cons_case : a -> list a -> nat -> nat
    variable g : list a -> nat
    variable x : a
    variable y : a
    variable xs : list a
    theorem synthesize_length:
        (exists (λnil_case.
            (exists (λcons_case.
                (imp (eq (g nil) nil_case)
                (imp (forall (λx. (forall (λxs. (eq (g (cons x xs)) (cons_case x xs (g xs)))))))
                    (conj 
                        (eq (g (cons x nil)) (suc zero))
                        (eq (g (cons x (cons y nil))) (suc (suc zero))))
                ))
            ))
        ))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in

  (* let cons_case_ty = *)
  (*   make_fun_ty a (make_fun_ty list_a (make_fun_ty nat_ty nat_ty)) *)
  (* in *)
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
    success with chosen term: λa. λl. λn. suc n
    success with chosen term: zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g nil = nil_case ==> (∀x. ∀xs. g (cons x xs) = cons_case x xs (g xs)) ==> g (cons x nil) = suc zero ∧ g (cons x (cons y nil)) = suc (suc zero)

    Proof Complete!
    with fuel: 299
    |}]

let%expect_test "synth append" =
  let prg =
    {|
    vartype a
    variable nil_case : list a -> list a
    variable cons_case : a -> list a -> list a -> list a
    variable g : list a -> list a -> list a
    variable x : a
    variable y : a
    variable xs : list a
    variable ys : list a
    theorem synthesize_append:
        (exists (λnil_case.
            (exists (λcons_case.
                (imp (forall (λys. (eq (g nil ys) (nil_case ys))))
                (imp (forall (λx. (forall (λxs. (forall (λys. (eq (g (cons x xs) ys) (cons_case x xs (g xs ys)))))))))
                    (conj
                        (eq (g nil (cons x nil)) (cons x nil))
                        (eq (g (cons x nil) (cons y nil)) (cons x (cons y nil)))
                    )
                ))
            ))
        ))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
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
    success with chosen term: λa. λl. λl0. cons a l0
    success with chosen term: λl. l
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. (∀ys. g nil ys = nil_case ys) ==> (∀x. ∀xs. ∀ys. g (cons x xs) ys = cons_case x xs (g xs ys)) ==> g nil (cons x nil) = cons x nil ∧ g (cons x nil) (cons y nil) = cons x (cons y nil)

    Proof Complete!
    with fuel: 464
    |}]

let%expect_test "synth reverse" =
  let open Theories.ListTheory in
  let _ = list_def in
  let a = make_vartype "a" in
  let list_a = TyCon ("list", [ a ]) in
  let append_ty = make_fun_ty list_a (make_fun_ty list_a list_a) in
  let extra = [ ("append", append_ty) ] in

  let prg =
    {|
    vartype a
    variable nil_case : list a
    variable cons_case : a -> list a -> list a -> list a
    variable g : list a -> list a
    variable x : a
    variable y : a
    variable xs : list a
    theorem synthesize_reverse:
        exists λnil_case.
            exists λcons_case.
                imp
                    (eq (g nil) nil_case)
                    (imp
                        (forall λx. forall λxs.
                            eq (g (cons x xs)) (cons_case x xs (g xs)))
                        (eq
                            (g (cons x (cons y nil)))
                            (cons y (cons x nil))))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
  let proof =
    with_best_first
      (try_ (with_synthetic_term ~extra 6 (with_info_trace exists_tac))
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
    success with chosen term: λa. λl. λl0. append l0 (cons a nil)
    success with chosen term: nil
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g nil = nil_case ==> (∀x. ∀xs. g (cons x xs) = cons_case x xs (g xs)) ==> g (cons x (cons y nil)) = cons y (cons x nil)

    Proof Complete!
    with fuel: 551
    |}]

let%expect_test "synth mult" =
  let open Theories.NatTheory in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let prg =
    {|
    variable nil_case : nat -> nat
    variable suc_case : nat -> nat -> nat
    variable g : nat -> nat -> nat
    variable m : nat
    variable n : nat
    theorem synthesize_mult:
        exists λnil_case.
            exists λsuc_case.
                imp
                    (forall λn. eq (g zero n) (nil_case n))
                    (imp
                        (forall λm. forall λn.
                            eq (g (suc m) n) (suc_case n (g m n)))
                        (conj
                            (eq (g zero (suc (suc zero))) zero)
                            (eq
                                (g (suc (suc zero)) (suc (suc (suc zero))))
                                (suc (suc (suc (suc (suc (suc zero)))))))))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
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
    success with chosen term: λn. zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃suc_case. (∀n. g zero n = nil_case n) ==> (∀m. ∀n. g (suc m) n = suc_case n (g m n)) ==> g zero (suc (suc zero)) = zero ∧ g (suc (suc zero)) (suc (suc (suc zero))) = suc (suc (suc (suc (suc (suc zero)))))

    Proof Complete!
    with fuel: 5414
    |}]

let%expect_test "synth sum" =
  let open Theories.NatTheory in
  let open Theories.ListTheory in
  let _ = list_def in
  let plus_ty = make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty) in
  let extras = [ ("plus", plus_ty) ] in
  let prg =
    {|
    variable nil_case : nat
    variable cons_case : nat -> nat -> nat
    variable g : list nat -> nat
    variable x : nat
    variable xs : list nat
    theorem synthesize_sum:
        exists λnil_case.
            exists λcons_case.
                imp
                    (eq (g nil) nil_case)
                    (imp
                        (forall λx. forall λxs.
                            eq (g (cons x xs)) (cons_case x (g xs)))
                        (eq
                            (g (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))))
                            (suc (suc (suc (suc (suc (suc zero))))))))
  |}
  in
  let goal = ([], List.hd (Elaborator.goals_from_string prg)) in
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
    success with chosen term: λn. λn0. plus n n0
    success with chosen term: zero
    Proof:
      exists_tac >>
      exists_tac >>
      intro_tac >>
      intro_tac >>
      auto_dfs_tac
    ========================================
    ∃nil_case. ∃cons_case. g nil = nil_case ==> (∀x. ∀xs. g (cons x xs) = cons_case x (g xs)) ==> g (cons (suc zero) (cons (suc (suc zero)) (cons (suc (suc (suc zero))) nil))) = suc (suc (suc (suc (suc (suc zero)))))

    Proof Complete!
    with fuel: 670
    |}]

open Holinone
open Elaborator
open Parse
open Printing


let%expect_test "elab" =
  let prg =
    {|
    (type mynat ()
      (Zmy)
      (Smy (mynat)))

    (def mnat_id (-> mynat mynat)
        (fn (n mynat) (n)))

    (fun mnat_id2 (-> mynat mynat)
        ((Zmy) Zmy)
        (((Smy n)) (Smy n)))

    (fun mnat_plus (-> mynat (-> mynat mynat))
        ((Zmy n) Zmy)
        (((Smy m) n) (Smy (mnat_plus m n))))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  (the_inductives
  |> Hashtbl.iter @@ fun k (v : inductive_def) ->
     print_endline k;
     print_thm v.recursion;
     print_thm v.induction);
  (the_term_constants
  |> Hashtbl.iter @@ fun k (v : hol_type) ->
     print_endline k;
     print_endline @@ Printing.pretty_print_hol_type v);
  (!the_definitions |> List.iter @@ fun t -> print_thm t);
  (!the_axioms |> List.iter @@ fun t -> print_thm t);
  [%expect
    {|
    mynat
    ========================================
    ∀Zmy_case. ∀Smy_case. ∃g. g Zmy = Zmy_case ∧ (∀x0. g (Smy x0) = Smy_case x0 (g x0))

    ========================================
    ∀P. P Zmy ==> (∀n0. P n0 ==> P (Smy n0)) ==> ∀x. P x

    Zmy
    mynat
    mnat_id
    (mynat -> mynat)
    \/
    (bool -> (bool -> bool))
    ~
    (bool -> bool)
    mnat_plus
    (mynat -> (mynat -> mynat))
    !
    ((a -> bool) -> bool)
    =
    (A -> (A -> bool))
    /\
    (bool -> (bool -> bool))
    T
    bool
    F
    bool
    mnat_id2
    (mynat -> mynat)
    Smy
    (mynat -> mynat)
    ?
    ((a -> bool) -> bool)
    ==>
    (bool -> (bool -> bool))
    ========================================
    mnat_id = (λn. n)

    ========================================
    \/ = (λp. λq. ∀r. (p ==> r) ==> (q ==> r) ==> r)

    ========================================
    ? = (λP. ¬(∀x. ¬(P x)))

    ========================================
    ~ = (λp. p ==> F)

    ========================================
    F = (∀p. p)

    ========================================
    ==> = (λp. λq. p ∧ q = p)

    ========================================
    /\ = (λp. λq. (λf. f p q) = (λf. f T T))

    ========================================
    ! = (λP. P = (λx. T))

    ========================================
    T = (λp. p) = (λp. p)

    ========================================
    mnat_plus Zmy = (λn. Zmy) ∧ (∀x0. mnat_plus (Smy x0) = (λn. Smy (mnat_plus x0 n)))

    ========================================
    mnat_id2 Zmy = Zmy ∧ (∀x0. mnat_id2 (Smy x0) = Smy x0)

    ========================================
    ∀x0. ∀y0. Smy x0 = Smy y0 ==> x0 = y0

    ========================================
    ∀y0. ¬Zmy = Smy y0

    ========================================
    ∀Zmy_case. ∀Smy_case. ∃g. g Zmy = Zmy_case ∧ (∀x0. g (Smy x0) = Smy_case x0 (g x0))

    ========================================
    ∀P. P Zmy ==> (∀n0. P n0 ==> P (Smy n0)) ==> ∀x. P x

    ========================================
    ∀P. (∃x. P x) ==> P (@ (λx. P x))

    ========================================
    ∀p. p ∨ ¬p
    |}]

let%expect_test "elab2" =
  let prg =
    {|

  (type mnat ()
    (Zm)
    (Sm (mnat)))
  (type list ('a)
    (Nil)
    (Cons ('a (list 'a))))
  (type option ('a)
    (None)
    (Some ('a)))
  (fun length (-> (list 'a) mnat)
    ( (Nil) Zm)
    ( ((Cons x xs)) (Sm (length xs))))
  (fun head (-> (list 'a) (option 'a))
    ( (Nil) None)
    ( ((Cons x xs)) (Some x)))
  |}
  in
  let ast = parse_string prg in
  let tast = Tast.check_program ast in
  let () = Elab.elab_program tast in
  let length_def = Hashtbl.find the_specifications "length" in
  let head_def = Hashtbl.find the_specifications "head" in
  print_thm length_def;
  print_thm head_def;
  [%expect
    {|
    ========================================
    length Nil = Zm ∧ (∀x0. ∀x1. length (Cons x0 x1) = Sm (length x1))

    ========================================
    head Nil = None ∧ (∀x0. ∀x1. head (Cons x0 x1) = Some x0)
    |}]

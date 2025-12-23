open Elaborator
open Ast
open Inductive
open Kernel

let pp_tydef t = print_endline @@ show_type_def t

let%expect_test "elaborate_simple_type_def" =
  let test_prog =
    {|

type nat where
    | Zero 
    | Succ of nat 
    
    |}
  in
  let ast = elaborate (Parser_driver.parse_string test_prog) in
  (ast
  |> List.iter @@ fun d ->
     match d with
     | TypeDef t ->
         let _ = hol_of_type_def t in
         the_inductives |> Hashtbl.to_seq
         |> Seq.iter @@ fun (a, b) ->
            if t.name = a then (
              Derived.pp_thm b.induction;
              Derived.pp_thm b.recursion;
              List.iter Derived.pp_thm b.injective;
              List.iter Derived.pp_thm b.distinct)
            else ()
     | Def _ -> print_endline "def"
     | Fun _ -> print_endline "fun"
     | Theorem _ -> print_endline "thm");
  [%expect
    {|
    ========================================
    ∀P. P Zero ==> (∀n0. P n0 ==> P (Suc n0)) ==> ∀x. P x

    ========================================
    ∀Zero_case. ∀Suc_case. ∃g. g Zero = Zero_case ∧ (∀x0. g (Suc x0) = Suc_case x0 (g x0))

    ========================================
    ∀x0. ∀y0. Suc x0 = Suc y0 ==> x0 = y0

    ========================================
    ∀y0. ¬Zero = Suc y0
    |}]

let%expect_test "elaborate_poly_type_def" =
  let test_prog =
    {|

type 'a list where
    | Nil 
    | Cons of 'a ('a list)
    
    |}
  in
  let ast = elaborate (Parser_driver.parse_string test_prog) in
  (ast
  |> List.iter @@ fun d ->
     match d with
     | TypeDef t ->
         let _ = hol_of_type_def t in
         the_inductives |> Hashtbl.to_seq
         |> Seq.iter @@ fun (a, b) ->
            if t.name = a then (
              Derived.pp_thm b.induction;
              Derived.pp_thm b.recursion;
              List.iter Derived.pp_thm b.injective;
              List.iter Derived.pp_thm b.distinct)
            else ()
     | Def _ -> print_endline "def"
     | Fun _ -> print_endline "fun"
     | Theorem _ -> print_endline "thm");
  [%expect {|
    ========================================
    ∀P. P Nil ==> (∀n0. ∀n1. P n1 ==> P (Cons n0 n1)) ==> ∀x. P x

    ========================================
    ∀Nil_case. ∀Cons_case. ∃g. g Nil = Nil_case ∧ (∀x0. ∀x1. g (Cons x0 x1) = Cons_case x0 x1 (g x1))

    ========================================
    ∀x0. ∀x1. ∀y0. ∀y1. Cons x0 x1 = Cons y0 y1 ==> x0 = y0 ∧ x1 = y1

    ========================================
    ∀y0. ∀y1. ¬Nil = Cons y0 y1
    |}]

let%expect_test "elaborate_poly_multi_type_def" =
  let test_prog =
    {|

type 'a 'b pair where
    | Pair of 'a 'b
    
    |}
  in
  let ast = elaborate (Parser_driver.parse_string test_prog) in
  (ast
  |> List.iter @@ fun d ->
     match d with
     | TypeDef t ->
         let _ = hol_of_type_def t in
         the_inductives |> Hashtbl.to_seq
         |> Seq.iter @@ fun (a, b) ->
            if t.name = a then (
              Derived.pp_thm b.induction;
              Derived.pp_thm b.recursion;
              List.iter Derived.pp_thm b.injective;
              List.iter Derived.pp_thm b.distinct)
            else ()
     | Def _ -> print_endline "def"
     | Fun _ -> print_endline "fun"
     | Theorem _ -> print_endline "thm");
  [%expect {|
    |}]

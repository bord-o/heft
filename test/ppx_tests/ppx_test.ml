open Heft
open Kernel
open Derived

let%expect_test "variable with type annotation" =
  let (t : term) = [%term (test : nat list)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| test:(nat list) |}]

let%expect_test "constant" =
  let (t : term) = [%term Zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| Zero:nat |}]

let%expect_test "application: Suc Zero" =
  let (t : term) = [%term Suc Zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| Suc:(nat -> nat) Zero:nat |}]

let%expect_test "nested application: plus Zero Zero" =
  let (t : term) = [%term plus Zero Zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| plus:(nat -> (nat -> nat)) Zero:nat Zero:nat |}]

let%expect_test "application with variable: Suc (n : nat)" =
  let (t : term) = [%term Suc (n : nat)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| Suc:(nat -> nat) n:nat |}]

let%expect_test "lambda: fun (x : nat) -> x" =
  let (t : term) = [%term fun (x : nat) -> (x : nat)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| λx:nat. x:nat |}]

let%expect_test "forall with equality" =
  let (t : term) = [%term forall (fun (x : nat) -> (x : nat) = (x : nat))] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. x = x |}]

let%expect_test "equality: (x : nat) = (y : nat)" =
  let (t : term) = [%term (x : nat) = (y : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| x = y |}]

let%expect_test "forall with equality" =
  let (t : term) =
    [%term forall (fun (n : nat) -> plus Zero (n : nat) = (n : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. plus Zero n = n |}]

let%expect_test "negation" =
  let (t : term) = [%term not (x : bool)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ¬x |}]

let%expect_test "conjunction" =
  let (t : term) = [%term (x : bool) && (y : bool)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| x ∧ y |}]

let%expect_test "disjunction" =
  let (t : term) = [%term (x : bool) || (y : bool)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| x ∨ y |}]

let%expect_test "implication" =
  let (t : term) = [%term (x : bool) ==> (y : bool)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| x ==> y |}]

(* === Application edge cases === *)

let%expect_test "three-argument application" =
  let (t : term) = [%term nat_lt (n : nat) (m : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| nat_lt n m |}]

let%expect_test "nested application in argument position" =
  let (t : term) = [%term Suc (Suc Zero)] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 2 |}]

let%expect_test "deeply nested Suc" =
  let (t : term) = [%term Suc (Suc (Suc Zero))] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 3 |}]

let%expect_test "application of constant to variable" =
  let (t : term) = [%term plus (n : nat) (m : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus n m |}]

let%expect_test "application mixing constants and variables" =
  let (t : term) = [%term plus (Suc (n : nat)) Zero] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus (Suc n) Zero |}]

(* === Lambda edge cases === *)

let%expect_test "lambda with application body" =
  let (t : term) = [%term fun (x : nat) -> Suc (x : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. Suc x |}]

let%expect_test "lambda with arrow type parameter" =
  let (t : term) = [%term fun (f : nat -> nat) -> (f : nat -> nat)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| λf:(nat -> nat). f:(nat -> nat) |}]

let%expect_test "multivariable lambda" =
  let (t : term) =
    [%term fun (a : nat) -> fun (b : nat) -> plus (a : nat) (b : nat)]
  in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| λa:nat. λb:nat. plus:(nat -> (nat -> nat)) a:nat b:nat |}]

(* === Quantifier edge cases === *)

let%expect_test "exists" =
  let (t : term) = [%term exists (fun (x : nat) -> (x : nat) = Zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃x. x = Zero |}]

let%expect_test "nested forall" =
  let (t : term) =
    [%term
      forall (fun (x : nat) -> forall (fun (y : nat) -> (x : nat) = (y : nat)))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. ∀y. x = y |}]

let%expect_test "forall with implication body" =
  let (t : term) =
    [%term forall (fun (p : bool) -> (p : bool) ==> (p : bool))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀p. p ==> p |}]

let%expect_test "forall with complex body" =
  let (t : term) =
    [%term
      forall (fun (n : nat) ->
          forall (fun (m : nat) ->
              plus (n : nat) (m : nat) = plus (m : nat) (n : nat)))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus n m = plus m n |}]

(* === Connective edge cases === *)

(* Note: OCaml parses `not x && y` as `(not x) && y` since application
   binds tighter than &&. To negate a conjunction, the user would need
   a different encoding. This test captures the actual parse behavior. *)
let%expect_test "not and conjunction precedence" =
  let (t : term) = [%term not ((x : bool) && (y : bool))] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ¬x ∧ y |}]

let%expect_test "conjunction with equality" =
  let (t : term) = [%term (x : nat) = (y : nat) && (y : nat) = (x : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| x = y ∧ y = x |}]

let%expect_test "disjunction with negation" =
  let (t : term) = [%term (p : bool) || not (p : bool)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| p ∨ ¬p |}]

let%expect_test "implication chain" =
  let (t : term) = [%term (p : bool) ==> ((q : bool) ==> (p : bool))] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| p ==> q ==> p |}]

(* === Type edge cases === *)

let%expect_test "type variable" =
  let (t : term) = [%term (x : 'a)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| x:a |}]

let%expect_test "arrow type variable" =
  let (t : term) = [%term (f : 'a -> 'b)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| f:(a -> b) |}]

let%expect_test "nested parameterized type" =
  let (t : term) = [%term (xs : nat list list)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| xs:((nat list) list) |}]

(* === Equality edge cases === *)

let%expect_test "equality of applications" =
  let (t : term) = [%term Suc (n : nat) = Suc (m : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| Suc n = Suc m |}]

let%expect_test "equality of Zero" =
  let (t : term) = [%term Zero = Zero] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| Zero = Zero |}]

(* === Realistic theorem-like terms === *)

let%expect_test "induction-style: base case statement" =
  let (t : term) = [%term plus Zero (n : nat) = (n : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus Zero n = n |}]

let%expect_test "induction-style: step case statement" =
  let (t : term) =
    [%term plus (Suc (n : nat)) (m : nat) = Suc (plus (n : nat) (m : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus (Suc n) m = Suc (plus n m) |}]

let%expect_test "full universally quantified theorem" =
  let (t : term) =
    [%term
      forall (fun (n : nat) ->
          forall (fun (m : nat) ->
              plus (Suc (n : nat)) (m : nat) = Suc (plus (n : nat) (m : nat))))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus (Suc n) m = Suc (plus n m) |}]

let%expect_test "exists with application" =
  let (t : term) = [%term exists (fun (n : nat) -> Suc (n : nat) = Zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃n. Suc n = Zero |}]

let%expect_test "mixed quantifiers" =
  let (t : term) =
    [%term
      forall (fun (p : bool) ->
          exists (fun (q : bool) -> (p : bool) ==> (q : bool)))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀p. ∃q. p ==> q |}]

(* === true/false === *)

let%expect_test "true" =
  let (t : term) = [%term true] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| T |}]

let%expect_test "false" =
  let (t : term) = [%term false] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| F |}]

let%expect_test "forall with true body" =
  let (t : term) = [%term forall (fun (a : nat) -> true)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀a. T |}]

let%expect_test "negation of false" =
  let (t : term) = [%term not false] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ¬F |}]

let%expect_test "true implies false" =
  let (t : term) = [%term true ==> false] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| T ==> F |}]

(* === Multi-param lambda === *)

let%expect_test "multi-param lambda" =
  let (t : term) =
    [%term fun (x : nat) (y : nat) -> plus (x : nat) (y : nat)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. λy. plus x y |}]

let%expect_test "three-param lambda" =
  let (t : term) =
    [%term
      fun (a : bool) (b : bool) (c : bool) ->
        ((a : bool) && (b : bool)) || (c : bool)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λa. λb. λc. a ∧ b ∨ c |}]

(* === Multi-param forall === *)

let%expect_test "multi-param forall" =
  let (t : term) =
    [%term
      forall (fun (n : nat) (m : nat) ->
          plus (n : nat) (m : nat) = plus (m : nat) (n : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus n m = plus m n |}]

let%expect_test "three-param forall" =
  let (t : term) =
    [%term
      forall (fun (a : nat) (b : nat) (c : nat) ->
          plus (a : nat) (plus (b : nat) (c : nat))
          = plus (plus (a : nat) (b : nat)) (c : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀a. ∀b. ∀c. plus a (plus b c) = plus (plus a b) c |}]

(* === Multi-param exists === *)

let%expect_test "multi-param exists" =
  let (t : term) =
    [%term exists (fun (x : nat) (y : nat) -> (x : nat) = (y : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃x. ∃y. x = y |}]

(* === Nat literals === *)

let%expect_test "0n" =
  let (t : term) = [%term 0n] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 0 |}]

let%expect_test "3n" =
  let (t : term) = [%term 3n] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 3 |}]

let%expect_test "nat literal in application" =
  let (t : term) = [%term plus 2n 3n] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| plus 2 3 |}]

let%expect_test "nat literal in equality" =
  let (t : term) = [%term Suc 2n = 3n] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 3 = 3 |}]

let%expect_test "nat literal in forall" =
  let (t : term) =
    [%term forall (fun (n : nat) -> plus (n : nat) 0n = (n : nat))]
  in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| ∀n. plus n 0 = n |}]

(* === Binder-scoped variables (no repeated annotations) === *)

let%expect_test "forall: bare variables from binder" =
  let (t : term) = [%term forall (fun (n : nat) -> plus Zero n = n)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. plus Zero n = n |}]

let%expect_test "forall: multi-param bare variables" =
  let (t : term) =
    [%term
      forall (fun (x : nat) (y : nat) (z : nat) ->
          plus x (plus y z) = plus (plus x y) z)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. ∀y. ∀z. plus x (plus y z) = plus (plus x y) z |}]

let%expect_test "exists: bare variable from binder" =
  let (t : term) = [%term exists (fun (x : nat) -> Suc x = Zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃x. Suc x = Zero |}]

let%expect_test "lambda: bare variable from binder" =
  let (t : term) = [%term fun (x : nat) -> Suc x] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. Suc x |}]

let%expect_test "lambda: multi-param bare variables" =
  let (t : term) = [%term fun (x : nat) (y : nat) -> plus x y] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. λy. plus x y |}]

let%expect_test "nested quantifiers: inner uses outer binder" =
  let (t : term) =
    [%term forall (fun (x : nat) -> exists (fun (y : nat) -> x = y))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. ∃y. x = y |}]

let%expect_test "realistic: plus_Suc theorem" =
  let (t : term) =
    [%term forall (fun (n : nat) (m : nat) -> plus (Suc n) m = Suc (plus n m))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus (Suc n) m = Suc (plus n m) |}]

let%expect_test "realistic: plus_comm" =
  let (t : term) =
    [%term forall (fun (n : nat) (m : nat) -> plus n m = plus m n)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus n m = plus m n |}]

(* === if/then/else === *)

let%expect_test "if/then/else" =
  let (t : term) = [%term if (b : bool) then (x : nat) else (y : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| COND b x y |}]

let%expect_test "if/then/else with binder scoping" =
  let (t : term) =
    [%term
      forall (fun (b : bool) (x : nat) (y : nat) ->
          (if b then x else y) = if not b then y else x)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀b. ∀x. ∀y. COND b x y = COND ¬b y x |}]

(* === Polymorphic instantiation === *)

let%expect_test "polymorphic constant applied to monomorphic arg" =
  let (t : term) = [%term Cons ((x : nat), Nil)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| Cons:(nat -> ((nat list) -> (nat list))) x:nat Nil:(nat list) |}]

let%expect_test "equality with polymorphic Nil instantiates both sides" =
  let (t : term) = [%term Nil = Cons ((x : nat), Nil)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect
    {| Nil:(nat list) = Cons:(nat -> ((nat list) -> (nat list))) x:nat Nil:(nat list) |}]

let%expect_test "polymorphic equality: both sides same type after instantiation"
    =
  let (t : term) =
    [%term forall (fun (xs : nat list) -> length xs = length xs)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀xs. length xs = length xs |}]

let%expect_test "polymorphic app in forall with binder scoping" =
  let (t : term) =
    [%term
      forall (fun (x : nat) (xs : nat list) ->
          length (Cons (x, xs)) = Suc (length xs))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. ∀xs. length (Cons x xs) = Suc (length xs) |}]

(* === [%%inductive] === *)

[%%inductive
type color =
  | Red
  | Green
  | Blue]

let%expect_test "inductive: color constructors" =
  let r = Printing.unwrap_term (make_const "Red" []) in
  let g = Printing.unwrap_term (make_const "Green" []) in
  let b = Printing.unwrap_term (make_const "Blue" []) in
  print_endline (Printing.pretty_print_hol_term r);
  print_endline (Printing.pretty_print_hol_term g);
  print_endline (Printing.pretty_print_hol_term b);
  [%expect {|
    Red
    Green
    Blue |}]

let%expect_test "inductive: color in [%%term]" =
  let t = [%term Red] in
  print_endline (Printing.pretty_print_hol_term t);
  [%expect {| Red |}]

let color_def = Hashtbl.find the_inductives "color"

let%expect_test "inductive: color type" =
  print_endline (show_hol_type color_def.ty);
  [%expect {| (TyCon ("color", [])) |}]

let%expect_test "inductive: color induction" =
  print_endline (Printing.pretty_print_thm color_def.induction);
  [%expect {|
    ========================================
    ∀P. P Red ==> P Green ==> P Blue ==> ∀x. P x
    |}]

let%expect_test "inductive: color recursion" =
  print_endline (Printing.pretty_print_thm color_def.recursion);
  [%expect {|
    ========================================
    ∀Red_case. ∀Green_case. ∀Blue_case. ∃g. g Red = Red_case ∧ g Green = Green_case ∧ g Blue = Blue_case
    |}]

let%expect_test "inductive: color distinctness" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    color_def.distinct;
  [%expect {|
    ========================================
    Green = Blue = F
    ========================================
    Red = Blue = F
    ========================================
    Red = Green = F
    |}]

let%expect_test "inductive: color injectivity (none expected)" =
  print_endline (string_of_int (List.length color_def.injective));
  [%expect {| 0 |}]

let%expect_test "inductive: color exhaustiveness" =
  print_endline (Printing.pretty_print_thm color_def.exhaustiveness);
  [%expect {|
    ========================================
    ∀x. x = Red ∨ x = Green ∨ x = Blue
    |}]

let%expect_test "inductive: match_color defined" =
  print_endline (Printing.pretty_print_thm color_def.match_function);
  [%expect {|
    ========================================
    match_color Red = (λh0. λh1. λh2. h0) ∧ match_color Green = (λh0. λh1. λh2. h1) ∧ match_color Blue = (λh0. λh1. λh2. h2)
    |}]

let%expect_test "inductive: match_color type" =
  let cm = Printing.unwrap_term (make_const "match_color" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true cm);
  [%expect {| match_color:(color -> (r -> (r -> (r -> r)))) |}]

[%%inductive
type 'a tree =
  | Leaf
  | Node of 'a * 'a tree * 'a tree]

let%expect_test "inductive: tree constructors" =
  let leaf = Printing.unwrap_term (make_const "Leaf" []) in
  let node = Printing.unwrap_term (make_const "Node" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true leaf);
  print_endline (Printing.pretty_print_hol_term ~with_type:true node);
  [%expect {|
    Leaf:(a tree)
    Node:(a -> ((a tree) -> ((a tree) -> (a tree)))) |}]

let tree_def = Hashtbl.find the_inductives "tree"

let%expect_test "inductive: tree type" =
  print_endline (show_hol_type tree_def.ty);
  [%expect {| (TyCon ("tree", [(TyVar "a")])) |}]

let%expect_test "inductive: tree induction" =
  print_endline (Printing.pretty_print_thm tree_def.induction);
  [%expect {|
    ========================================
    ∀P. P Leaf ==> (∀n0. ∀n1. ∀n2. P n1 ==> P n2 ==> P (Node n0 n1 n2)) ==> ∀x. P x
    |}]

let%expect_test "inductive: tree recursion" =
  print_endline (Printing.pretty_print_thm tree_def.recursion);
  [%expect {|
    ========================================
    ∀Leaf_case. ∀Node_case. ∃g. g Leaf = Leaf_case ∧ (∀x0. ∀x1. ∀x2. g (Node x0 x1 x2) = Node_case x0 x1 x2 (g x1) (g x2))
    |}]

let%expect_test "inductive: tree distinctness" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    tree_def.distinct;
  [%expect {|
    ========================================
    ∀y0. ∀y1. ∀y2. Leaf = Node y0 y1 y2 = F
    |}]

let%expect_test "inductive: tree injectivity" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    tree_def.injective;
  [%expect {|
    ========================================
    ∀x0. ∀x1. ∀x2. ∀y0. ∀y1. ∀y2. Node x0 x1 x2 = Node y0 y1 y2 ==> x0 = y0 ∧ x1 = y1 ∧ x2 = y2
    |}]

let%expect_test "inductive: tree exhaustiveness" =
  print_endline (Printing.pretty_print_thm tree_def.exhaustiveness);
  [%expect {|
    ========================================
    ∀x. x = Leaf ∨ (∃a0. ∃a1. ∃a2. x = Node a0 a1 a2)
    |}]

let%expect_test "inductive: match_tree theorem" =
  print_endline (Printing.pretty_print_thm tree_def.match_function);
  [%expect {|
    ========================================
    match_tree Leaf = (λh0. λh1. h0) ∧ (∀x0. ∀x1. ∀x2. match_tree (Node x0 x1 x2) = (λh0. λh1. h1 x0 x1 x2))
    |}]

let%expect_test "inductive: match_tree type" =
  let tm = Printing.unwrap_term (make_const "match_tree" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true tm);
  [%expect {| match_tree:((a tree) -> (r -> ((a -> ((a tree) -> ((a tree) -> r))) -> r))) |}]

let%expect_test "inductive: tree in [%%term]" =
  let t = [%term Node (1n, Leaf, Leaf)] in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| Node 1 Leaf Leaf |}]

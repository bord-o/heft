open Heft
open Kernel
open Derived
open Tactic

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

(* === Choice operator === *)

let%expect_test "choose" =
  let (t : term) = [%term choose (fun (x : nat) -> (x : nat) = Zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| @x. x = Zero |}]

let%expect_test "multi-param choose" =
  let (t : term) =
    [%term choose (fun (x : nat) (y : nat) -> (x : nat) = (y : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| @x. @y. x = y |}]

let%expect_test "choose: bare variable from binder" =
  let (t : term) = [%term choose (fun (x : nat) -> Suc x = Zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| @x. Suc x = Zero |}]

let%expect_test "choose with type annotation" =
  let (t : term) = [%term choose (fun (x : nat) -> (x : nat) = Zero)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| @x:nat. x:nat = Zero:nat |}]

let%expect_test "choose in forall" =
  let (t : term) =
    [%term
      forall (fun (n : nat) -> choose (fun (m : nat) -> plus n m = n) = Zero)]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. (@m. plus n m = n) = Zero |}]

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

(* === List syntax === *)

let%expect_test "empty list" =
  let (t : term) = [%term []] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| Nil |}]

let%expect_test "list literal" =
  let (t : term) = [%term [ 1n; 2n; 3n ]] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| [1, 2, 3] |}]

let%expect_test "cons operator" =
  let (t : term) = [%term (x : nat) :: (xs : nat list)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| Cons x xs |}]

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

[%%inductive type color = Red | Green | Blue]

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
  [%expect
    {|
    ========================================
    ∀P. P Red ==> P Green ==> P Blue ==> ∀x. P x
    |}]

let%expect_test "inductive: color recursion" =
  print_endline (Printing.pretty_print_thm color_def.recursion);
  [%expect
    {|
    ========================================
    ∀Red_case. ∀Green_case. ∀Blue_case. ∃g. g Red = Red_case ∧ g Green = Green_case ∧ g Blue = Blue_case
    |}]

let%expect_test "inductive: color distinctness" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    color_def.distinct;
  [%expect
    {|
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
  [%expect
    {|
    ========================================
    ∀x. x = Red ∨ x = Green ∨ x = Blue
    |}]

let%expect_test "inductive: match_color defined" =
  print_endline (Printing.pretty_print_thm color_def.match_function);
  [%expect
    {|
    ========================================
    match_color Red = (λh0. λh1. λh2. h0) ∧ match_color Green = (λh0. λh1. λh2. h1) ∧ match_color Blue = (λh0. λh1. λh2. h2)
    |}]

let%expect_test "inductive: match_color type" =
  let cm = Printing.unwrap_term (make_const "match_color" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true cm);
  [%expect {| match_color:(color -> (r -> (r -> (r -> r)))) |}]

[%%inductive type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree]

let%expect_test "inductive: tree constructors" =
  let leaf = Printing.unwrap_term (make_const "Leaf" []) in
  let node = Printing.unwrap_term (make_const "Node" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true leaf);
  print_endline (Printing.pretty_print_hol_term ~with_type:true node);
  [%expect
    {|
    Leaf:(a tree)
    Node:(a -> ((a tree) -> ((a tree) -> (a tree)))) |}]

let tree_def = Hashtbl.find the_inductives "tree"

let%expect_test "inductive: tree type" =
  print_endline (show_hol_type tree_def.ty);
  [%expect {| (TyCon ("tree", [(TyVar "a")])) |}]

let%expect_test "inductive: tree induction" =
  print_endline (Printing.pretty_print_thm tree_def.induction);
  [%expect
    {|
    ========================================
    ∀P. P Leaf ==> (∀n0. ∀n1. ∀n2. P n1 ==> P n2 ==> P (Node n0 n1 n2)) ==> ∀x. P x
    |}]

let%expect_test "inductive: tree recursion" =
  print_endline (Printing.pretty_print_thm tree_def.recursion);
  [%expect
    {|
    ========================================
    ∀Leaf_case. ∀Node_case. ∃g. g Leaf = Leaf_case ∧ (∀x0. ∀x1. ∀x2. g (Node x0 x1 x2) = Node_case x0 x1 x2 (g x1) (g x2))
    |}]

let%expect_test "inductive: tree distinctness" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    tree_def.distinct;
  [%expect
    {|
    ========================================
    ∀y0. ∀y1. ∀y2. Leaf = Node y0 y1 y2 = F
    |}]

let%expect_test "inductive: tree injectivity" =
  List.iter
    (fun thm -> print_endline (Printing.pretty_print_thm thm))
    tree_def.injective;
  [%expect
    {|
    ========================================
    ∀x0. ∀x1. ∀x2. ∀y0. ∀y1. ∀y2. Node x0 x1 x2 = Node y0 y1 y2 ==> x0 = y0 ∧ x1 = y1 ∧ x2 = y2
    |}]

let%expect_test "inductive: tree exhaustiveness" =
  print_endline (Printing.pretty_print_thm tree_def.exhaustiveness);
  [%expect
    {|
    ========================================
    ∀x. x = Leaf ∨ (∃a0. ∃a1. ∃a2. x = Node a0 a1 a2)
    |}]

let%expect_test "inductive: match_tree theorem" =
  print_endline (Printing.pretty_print_thm tree_def.match_function);
  [%expect
    {|
    ========================================
    match_tree Leaf = (λh0. λh1. h0) ∧ (∀x0. ∀x1. ∀x2. match_tree (Node x0 x1 x2) = (λh0. λh1. h1 x0 x1 x2))
    |}]

let%expect_test "inductive: match_tree type" =
  let tm = Printing.unwrap_term (make_const "match_tree" []) in
  print_endline (Printing.pretty_print_hol_term ~with_type:true tm);
  [%expect
    {| match_tree:((a tree) -> (r -> ((a -> ((a tree) -> ((a tree) -> r))) -> r))) |}]

let%expect_test "inductive: tree in [%%term]" =
  let t = [%term Node (1n, Leaf, Leaf)] in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| Node 1 Leaf Leaf |}]

(* === match expressions === *)

let%expect_test "match: nullary constructors only (color)" =
  let t =
    [%term match (x : color) with Red -> 0n | Green -> 1n | Blue -> 2n]
  in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| match_color x 0 1 2 |}]

let%expect_test "match: constructor with args (nat)" =
  let t = [%term fun (n : nat) -> match n with Zero -> Zero | Suc n' -> n'] in
  print_endline (Printing.pretty_print_hol_term t);
  [%expect {| λn. match_nat n Zero (λn'. n') |}]

let%expect_test "match: multi-arg constructor (tree)" =
  let t =
    [%term
      fun (t : nat tree) -> match t with Leaf -> 0n | Node (v, l, r) -> v]
  in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| λt. match_tree t 0 (λv. λl. λr. v) |}]

let%expect_test "match: scoped variable from lambda" =
  let t =
    [%term
      fun (n : nat) (m : nat) -> match n with Zero -> m | Suc n' -> plus n' m]
  in
  print_endline (Printing.pretty_print_hol_term t);
  [%expect {| λn. λm. match_nat n m (λn'. plus n' m) |}]

let%expect_test "match: annotated scrutinee" =
  let t =
    [%term match (x : color) with Red -> true | Green -> false | Blue -> true]
  in
  print_endline (Printing.pretty_print_hol_term t);
  [%expect {| match_color x T F T |}]

let%expect_test "match: list with multi-arg constructor" =
  let t =
    [%term
      fun (xs : nat list) -> match xs with Nil -> 0n | Cons (x, rest) -> x]
  in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| λxs. match_list xs 0 (λx. λrest. x) |}]

let%expect_test "match: wildcard pattern" =
  let t =
    [%term
      fun (xs : nat list) -> match xs with Nil -> 0n | Cons (_, rest) -> 1n]
  in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| λxs. match_list xs 0 (λ_wild_852. λrest. 1) |}]

let%expect_test "match: nested match in body" =
  let t =
    [%term
      fun (n : nat) ->
        match n with
        | Zero -> 0n
        | Suc n' -> ( match (n' : nat) with Zero -> 1n | Suc _ -> 2n)]
  in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| λn. match_nat n 0 (λn'. match_nat n' 1 (λ_wild_882. 2)) |}]

(* === let%def === *)

let%def double (n : nat) : nat = plus n n

let%expect_test "def: double defined" =
  print_endline (Printing.pretty_print_thm double);
  [%expect
    {|
    ========================================
    double = (λn. plus n n)
    |}]

let%expect_test "def: double usable in term" =
  let t = [%term double 3n] in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| double 3 |}]

let%def const_fn (x : nat) (y : nat) : nat = x

let%expect_test "def: multi-param definition" =
  print_endline (Printing.pretty_print_thm const_fn);
  [%expect
    {|
    ========================================
    const_fn = (λx. λy. x)
    |}]

let%def apply_color (c : color) (r : nat) (g : nat) (b : nat) : nat =
  match c with Red -> r | Green -> g | Blue -> b

let%expect_test "def: definition with match body" =
  print_endline (Printing.pretty_print_thm apply_color);
  [%expect
    {|
    ========================================
    apply_color = (λc. λr. λg. λb. match_color c r g b)
    |}]

let%def my_zero : nat = Zero

let%expect_test "def: constant (no params)" =
  print_endline (Printing.pretty_print_thm my_zero);
  [%expect
    {|
    ========================================
    my_zero = Zero
    |}]

let%def my_true : bool = true

let%expect_test "def: boolean constant" =
  print_endline (Printing.pretty_print_thm my_true);
  [%expect
    {|
    ========================================
    my_true = T
    |}]

let%def my_pair : nat = plus (Suc Zero) (Suc Zero)

let%expect_test "def: constant with application body" =
  print_endline (Printing.pretty_print_thm my_pair);
  [%expect
    {|
    ========================================
    my_pair = plus (Suc Zero) (Suc Zero)
    |}]

let%def my_id : nat -> nat = fun (x : nat) -> x

let%expect_test "def: constant with lambda body" =
  print_endline (Printing.pretty_print_thm my_id);
  [%expect
    {|
    ========================================
    my_id = (λx. x)
    |}]

(* === Primrec definitions === *)

let%primrec my_plus (n : nat) (m : nat) : nat =
  match n with Zero -> m | Suc n' -> Suc (my_plus n' m)

let%expect_test "primrec: my_plus defined" =
  print_endline (Printing.pretty_print_thm my_plus);
  [%expect
    {|
    ========================================
    my_plus Zero = (λm. m) ∧ (∀x0. my_plus (Suc x0) = (λm. Suc (my_plus x0 m)))
    |}]

let%expect_test "primrec: my_plus usable in term" =
  let t = [%term my_plus 2n 3n] in
  print_endline (Printing.pretty_print_hol_term ~pretty:true t);
  [%expect {| my_plus 2 3 |}]

(* Non-recursive primrec: case analysis on color *)
let%primrec color_to_nat (c : color) : nat =
  match c with Red -> Zero | Green -> Suc Zero | Blue -> Suc (Suc Zero)

let%expect_test "primrec: color_to_nat (non-recursive)" =
  print_endline (Printing.pretty_print_thm color_to_nat);
  [%expect
    {|
    ========================================
    color_to_nat Red = Zero ∧ color_to_nat Green = Suc Zero ∧ color_to_nat Blue = Suc (Suc Zero)
    |}]

(* Tree size: polymorphic type with recursion *)
let%primrec tree_size (t : nat tree) : nat =
  match t with
  | Leaf -> Zero
  | Node (_, l, r) -> Suc (my_plus (tree_size l) (tree_size r))

let%expect_test "primrec: tree_size (polymorphic, recursive)" =
  print_endline (Printing.pretty_print_thm tree_size);
  [%expect
    {|
    ========================================
    tree_size Leaf = Zero ∧ (∀x0. ∀x1. ∀x2. tree_size (Node x0 x1 x2) = Suc (my_plus (tree_size x1) (tree_size x2)))
    |}]

(* === let%thm tests === *)

let%thm thm_plus_x_zero (x : nat) = plus x Zero = x

and proof =
  begin
    induct >> simp >> gen >> intro >> simp
  end
  [@quiet]

let%expect_test "let%thm with proof and quiet" =
  ignore thm_plus_x_zero;
  [%expect {||}]

let%thm thm_goal_only (n : nat) = plus n Zero = n

let%expect_test "let%thm goal only" =
  let asms, concl = thm_goal_only in
  assert (asms = []);
  Printf.printf "%s\n" (Printing.pretty_print_hol_term concl);
  [%expect {| ∀n. plus n Zero = n |}]

let%thm thm_multi_arg (x : nat) (y : nat) = plus x y = plus y x

and proof =
  begin
    with_term [%term (x : nat)] induct >> intros >> simp >> intros >> simp
  end
  [@quiet]

let%expect_test "let%thm multi-arg" =
  ignore thm_multi_arg;
  [%expect {||}]

let%thm thm_no_params = plus 2n 3n = 5n

and proof =
  begin
    simp
  end
  [@quiet]

let%expect_test "let%thm no params" =
  ignore thm_no_params;
  [%expect {||}]

let%thm thm_poly (xs : 'a list) = length xs = length xs

and proof =
  begin
    gen >> refl
  end
  [@quiet]

let%expect_test "let%thm polymorphic" =
  ignore thm_poly;
  [%expect {||}]

let%thm _unsaved (n : nat) = plus n Zero = n

and proof =
  begin
    induct >> simp >> gen >> intro >> simp
  end
  [@quiet]

let%expect_test "let%thm underscore-prefixed name (no ~name to run_proof)" =
  ignore _unsaved;
  [%expect {||}]

let%expect_test "let%thm inside expect_test" =
  let%thm local_thm (n : nat) = plus n Zero = n
  and proof =
    begin
      induct >> simp >> gen >> intro >> simp
    end
    [@quiet]
  in
  let _, concl = local_thm in
  Printf.printf "%s\n" (Printing.pretty_print_hol_term concl);
  [%expect {| ∀n. plus n Zero = n |}]

let%expect_test "let%thm with notrace inside expect_test" =
  let%thm _notrace_thm (x : nat) = plus x Zero = x
  and proof =
    begin
      induct >> simp >> gen >> intro >> simp
    end
    [@notrace]
  in
  ignore _notrace_thm;
  [%expect
    {|
    ========================================
    ∀x. plus x Zero = x

    Proof Complete!
    with fuel: 34
    |}]

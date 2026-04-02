open Heft
open Kernel
open Derived

let%expect_test "variable with type annotation" =
  let (t : term) = [%term (test : nat list)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| test:(nat list) |}]

let%expect_test "constant" =
  let (t : term) = [%term zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| zero:nat |}]

let%expect_test "application: suc zero" =
  let (t : term) = [%term suc zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| suc:(nat -> nat) zero:nat |}]

let%expect_test "nested application: plus zero zero" =
  let (t : term) = [%term plus zero zero] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| plus:(nat -> (nat -> nat)) zero:nat zero:nat |}]

let%expect_test "application with variable: suc (n : nat)" =
  let (t : term) = [%term suc (n : nat)] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| suc:(nat -> nat) n:nat |}]

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
    [%term forall (fun (n : nat) -> plus zero (n : nat) = (n : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. plus zero n = n |}]

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
  let (t : term) = [%term suc (suc zero)] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 2 |}]

let%expect_test "deeply nested suc" =
  let (t : term) = [%term suc (suc (suc zero))] in
  let s = Printing.pretty_print_hol_term ~pretty:true t in
  print_endline s;
  [%expect {| 3 |}]

let%expect_test "application of constant to variable" =
  let (t : term) = [%term plus (n : nat) (m : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus n m |}]

let%expect_test "application mixing constants and variables" =
  let (t : term) = [%term plus (suc (n : nat)) zero] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus (suc n) zero |}]

(* === Lambda edge cases === *)

let%expect_test "lambda with application body" =
  let (t : term) = [%term fun (x : nat) -> suc (x : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. suc x |}]

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
  let (t : term) = [%term exists (fun (x : nat) -> (x : nat) = zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃x. x = zero |}]

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
  let (t : term) = [%term suc (n : nat) = suc (m : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| suc n = suc m |}]

let%expect_test "equality of zero" =
  let (t : term) = [%term zero = zero] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| zero = zero |}]

(* === Realistic theorem-like terms === *)

let%expect_test "induction-style: base case statement" =
  let (t : term) = [%term plus zero (n : nat) = (n : nat)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus zero n = n |}]

let%expect_test "induction-style: step case statement" =
  let (t : term) =
    [%term plus (suc (n : nat)) (m : nat) = suc (plus (n : nat) (m : nat))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| plus (suc n) m = suc (plus n m) |}]

let%expect_test "full universally quantified theorem" =
  let (t : term) =
    [%term
      forall (fun (n : nat) ->
          forall (fun (m : nat) ->
              plus (suc (n : nat)) (m : nat) = suc (plus (n : nat) (m : nat))))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus (suc n) m = suc (plus n m) |}]

let%expect_test "exists with application" =
  let (t : term) = [%term exists (fun (n : nat) -> suc (n : nat) = zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃n. suc n = zero |}]

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
  let (t : term) = [%term suc 2n = 3n] in
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
  let (t : term) = [%term forall (fun (n : nat) -> plus zero n = n)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. plus zero n = n |}]

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
  let (t : term) = [%term exists (fun (x : nat) -> suc x = zero)] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∃x. suc x = zero |}]

let%expect_test "lambda: bare variable from binder" =
  let (t : term) = [%term fun (x : nat) -> suc x] in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| λx. suc x |}]

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

let%expect_test "realistic: plus_suc theorem" =
  let (t : term) =
    [%term forall (fun (n : nat) (m : nat) -> plus (suc n) m = suc (plus n m))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀n. ∀m. plus (suc n) m = suc (plus n m) |}]

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
  let (t : term) = [%term cons (x : nat) nil] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect {| cons:(nat -> ((nat list) -> (nat list))) x:nat nil:(nat list) |}]

let%expect_test "equality with polymorphic nil instantiates both sides" =
  let (t : term) = [%term nil = cons (x : nat) nil] in
  let s = Printing.pretty_print_hol_term ~with_type:true t in
  print_endline s;
  [%expect
    {| nil:(nat list) = cons:(nat -> ((nat list) -> (nat list))) x:nat nil:(nat list) |}]

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
          length (cons x xs) = suc (length xs))]
  in
  let s = Printing.pretty_print_hol_term t in
  print_endline s;
  [%expect {| ∀x. ∀xs. length (cons x xs) = suc (length xs) |}]

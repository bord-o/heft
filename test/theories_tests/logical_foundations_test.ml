open Heft
open Kernel
open Tactic
open Derived
open Auto

[%%inductive
type day =
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday]

let%def next_working_day (day : day) : day =
  match day with
  | Monday -> Tuesday
  | Tuesday -> Wednesday
  | Wednesday -> Thursday
  | Thursday -> Friday
  | Friday -> Monday
  | Saturday -> Monday
  | Sunday -> Monday

[%%inductive type mybool = True | False]

let%def negb' (b : mybool) : mybool =
  match b with True -> False | False -> True

let%def andb' (a : mybool) (b : mybool) : mybool =
  match a with True -> b | False -> False

let%def orb' (a : mybool) (b : mybool) : mybool =
  match a with True -> True | False -> b

let%def nandb' (a : mybool) (b : mybool) : mybool =
  match a with True -> negb' b | False -> True

let%def andthreeb (a : mybool) (b : mybool) (c : mybool) : mybool =
  match a with True -> andb' b c | False -> False

[%%inductive type rgb = Red | Green | Blue]
[%%inductive type color = Black | White | Primary of rgb]

let%def monochrome (c : color) : mybool =
  match c with Black -> True | White -> True | Primary p -> False

let%def isredprimary (rgb : rgb) : mybool =
  match rgb with Red -> True | Green -> False | Blue -> False

let%def isred (c : color) : mybool =
  match c with Black -> False | White -> False | Primary p -> isredprimary p

[%%inductive type bit = B1 | B0]

let%def bisone (b : bit) : mybool = match b with B1 -> True | B0 -> False
let%def biszero (b : bit) : mybool = match b with B1 -> False | B0 -> True

[%%inductive type nybble = Bits of bit * bit * bit * bit]

let%def all_zero (n : nybble) : mybool =
  match n with
  | Bits (m, n, o, p) ->
      andb' (biszero m) (andb' (biszero n) (andb' (biszero o) (biszero p)))

let compute_day_test = [%term next_working_day Friday = Monday]

let compute_two_days =
  [%term next_working_day (next_working_day Friday) = Tuesday]

let test_orb'1 = [%term orb' True False = True]
let test_orb'2 = [%term orb' False False = False]
let test_orb'3 = [%term orb' False True = True]
let test_orb'4 = [%term orb' True True = True]
let test_orb'5 = [%term orb' (orb' False False) True = True]
let test_nandb'1 = [%term nandb' True False = True]
let test_nandb'2 = [%term nandb' False False = True]
let test_nandb'3 = [%term nandb' False True = True]
let test_nandb'4 = [%term nandb' True True = False]
let test_andthreeb1 = [%term andthreeb True True True = True]
let test_andthreeb2 = [%term andthreeb False True True = False]
let test_andthreeb3 = [%term andthreeb True False True = False]
let test_andthreeb4 = [%term andthreeb True True False = False]
let all_zero_test1 = [%term all_zero (Bits (B1, B0, B1, B0)) = False]
let all_zero_test2 = [%term all_zero (Bits (B0, B0, B0, B0)) = True]

let plus_id_example =
  [%term forall (fun (m : nat) (n : nat) -> m = n ==> (plus m m = plus n n))]

let andb'_comm =
  [%term forall (fun (b : mybool) (c : mybool) -> andb' b c = andb' c b)]

let andb'_true_elim2 =
  [%term
    forall (fun (b : mybool) (c : mybool) -> andb' b c = True ==> (c = True))]

let%expect_test "basics" =
  run_proof (make_goal all_zero_test1) simp;
  run_proof (make_goal all_zero_test2) simp;
  run_proof (make_goal compute_day_test) simp;
  run_proof (make_goal compute_two_days) simp;
  run_proof (make_goal test_orb'1) simp;
  run_proof (make_goal test_orb'2) simp;
  run_proof (make_goal test_orb'3) simp;
  run_proof (make_goal test_orb'4) simp;
  run_proof (make_goal test_orb'5) simp;
  run_proof (make_goal test_nandb'1) simp;
  run_proof (make_goal test_nandb'2) simp;
  run_proof (make_goal test_nandb'3) simp;
  run_proof (make_goal test_nandb'4) simp;
  run_proof (make_goal test_andthreeb1) simp;
  run_proof (make_goal test_andthreeb2) simp;
  run_proof (make_goal test_andthreeb3) simp;
  run_proof (make_goal test_andthreeb4) simp;

  run_proof (make_goal plus_id_example) auto_dfs;
  run_proof (make_goal andb'_comm) (induct >>> (induct >>> simp));
  run_proof
    (make_goal andb'_true_elim2)
    (induct >>> (induct >>> (intros >>> try_ refl >> simp_asm ~with_asms:false)));
  (* TODO: conditionals *)
  [%expect
    {|
    ========================================
    all_zero (Bits B1 B0 B1 B0) = False

    Proof Complete!
    with fuel: 115
    ========================================
    all_zero (Bits B0 B0 B0 B0) = True

    Proof Complete!
    with fuel: 115
    ========================================
    next_working_day Friday = Monday

    Proof Complete!
    with fuel: 31
    ========================================
    next_working_day (next_working_day Friday) = Tuesday

    Proof Complete!
    with fuel: 48
    ========================================
    orb' True False = True

    Proof Complete!
    with fuel: 31
    ========================================
    orb' False False = False

    Proof Complete!
    with fuel: 31
    ========================================
    orb' False True = True

    Proof Complete!
    with fuel: 31
    ========================================
    orb' True True = True

    Proof Complete!
    with fuel: 31
    ========================================
    orb' (orb' False False) True = True

    Proof Complete!
    with fuel: 48
    ========================================
    nandb' True False = True

    Proof Complete!
    with fuel: 41
    ========================================
    nandb' False False = True

    Proof Complete!
    with fuel: 41
    ========================================
    nandb' False True = True

    Proof Complete!
    with fuel: 41
    ========================================
    nandb' True True = False

    Proof Complete!
    with fuel: 41
    ========================================
    andthreeb True True True = True

    Proof Complete!
    with fuel: 41
    ========================================
    andthreeb False True True = False

    Proof Complete!
    with fuel: 41
    ========================================
    andthreeb True False True = False

    Proof Complete!
    with fuel: 41
    ========================================
    andthreeb True True False = False

    Proof Complete!
    with fuel: 41
    Proof:
      gen >>
      gen >>
      intro >>
      rewrite >>
      rewrite >>
      refl
    ========================================
    ∀m. ∀n. m = n ==> plus m m = plus n n

    Proof Complete!
    with fuel: 45
    ========================================
    ∀x. ∀c. andb' x c = andb' c x

    Proof Complete!
    with fuel: 188
    ========================================
    ∀x. ∀c. andb' x c = True ==> c = True

    Proof Complete!
    with fuel: 102
    |}]

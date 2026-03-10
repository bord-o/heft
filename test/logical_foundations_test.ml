open Heft
open Tactic

let goals_of_string prg =
  let goals = Elaborator.named_goals_from_string prg in
  fun name -> ([], List.assoc name goals)

let%expect_test "basics" =
  let prg =
    {|
  inductive day :=
      | monday : day
      | tuesday : day
      | wednesday : day
      | thursday : day
      | friday : day
      | saturday : day
      | sunday : day

  def next_working_day : day -> day
      | monday => tuesday
      | tuesday => wednesday
      | wednesday => thursday
      | thursday => friday
      | friday => monday
      | saturday => monday
      | sunday => monday

  theorem compute_day_test :
      eq (next_working_day friday) monday
      theorem compute_two_days :
      eq (next_working_day (next_working_day friday)) tuesday

    inductive mybool :=
        | true : mybool
        | false : mybool

    variable b : mybool

    def negb : mybool -> mybool
        | true => false
        | false => true

    def andb : mybool -> mybool -> mybool
        | true => λb. b
        | false => λb. false

    def orb : mybool -> mybool -> mybool
        | true => λb. true
        | false => λb. b

    theorem test_orb1 :  eq (orb true false) true
    theorem test_orb2 :  eq (orb false false) false
    theorem test_orb3 :  eq (orb false true) true
    theorem test_orb4 :  eq (orb true true) true
    theorem test_orb5 :
        eq
            (orb
                (orb false false)
                (true))
            true
            variable b : mybool

    def nandb : mybool -> mybool -> mybool
      | true => λb. negb b
      | false => λb. true

    theorem test_nandb1 : eq (nandb true false) true
    theorem test_nandb2 : eq (nandb false false) true
    theorem test_nandb3 : eq (nandb false true) true
    theorem test_nandb4 : eq (nandb true true) false
    variable a : mybool
    def andthreeb : mybool -> mybool -> mybool -> mybool
      | true => andb
      | false =>λa. λb. false

    theorem test_andthreeb1 : eq (andthreeb true true true) true
    theorem test_andthreeb2 : eq (andthreeb false true true) false
    theorem test_andthreeb3 : eq (andthreeb true false true) false
    theorem test_andthreeb4 : eq (andthreeb true true false) false

    inductive rgb :=
      | red : rgb
      | blue : rgb
      | green : rgb

    inductive color :=
      | black : color
      | white : color
      | primary : rgb -> color

    variable p : rgb
    def monochrome : color -> mybool
      | black => true
      | white => true
      | primary p => false
    
    def isredprimary : rgb -> mybool
      | red => true
      | green => false
      | blue => false

    def isred : color -> mybool
      | black => false
      | white => false
      | primary p => isredprimary p

    inductive bit :=
      | b1 : bit
      | b0 : bit

    def bisone : bit -> mybool 
      | b1 => true 
      | b0 => false
    def biszero : bit -> mybool 
      | b1 => false
      | b0 => true


    inductive nybble :=
      | bits : bit -> bit -> bit -> bit -> nybble

    variable m n o p : bit
    def all_zero : nybble -> mybool
      | bits m n o p => 
        andb (biszero m) (andb (biszero n) (andb (biszero o) (biszero p)))
    theorem all_zero_test1 :  eq (all_zero (bits b1 b0 b1 b0)) false
    theorem all_zero_test2 :  eq (all_zero (bits b0 b0 b0 b0)) true

    variable c d : nat
    theorem plus_id_example : 
        imp (eq c d) (
            eq 
                (plus c c)
                (plus d d))
      |}
  in
  let goal = goals_of_string prg in
  run_proof (goal "all_zero_test1") simp_tac;
  run_proof (goal "all_zero_test2") simp_tac;
  run_proof (goal "compute_day_test") simp_tac;
  run_proof (goal "compute_two_days") simp_tac;
  run_proof (goal "test_orb1") simp_tac;
  run_proof (goal "test_orb2") simp_tac;
  run_proof (goal "test_orb3") simp_tac;
  run_proof (goal "test_orb4") simp_tac;
  run_proof (goal "test_orb5") simp_tac;
  run_proof (goal "test_nandb1") simp_tac;
  run_proof (goal "test_nandb2") simp_tac;
  run_proof (goal "test_nandb3") simp_tac;
  run_proof (goal "test_nandb4") simp_tac;
  run_proof (goal "test_andthreeb1") simp_tac;
  run_proof (goal "test_andthreeb2") simp_tac;
  run_proof (goal "test_andthreeb3") simp_tac;
  run_proof (goal "test_andthreeb4") simp_tac;

  let prg =
    {|
    variable m n o : nat
    theorem plus_id_example : 
        imp (eq m n) (
            eq 
                (plus m m)
                (plus n n))

    theorem plus_id_exercise : 
        imp 
            (eq n m)
            (imp
                (eq m o)
                (eq (plus n m) (plus m o)))

    variable b c : mybool
    theorem andb_comm :
        forall λb. 
            (forall λc.
                (eq (andb b c) (andb c b))
            )

    theorem andb_true_elim2 :
        forall λb. 
            (forall λc.
                (imp (eq (andb b c) true) (eq c true))
            )
     |}
  in
  let goal = goals_of_string prg in
  run_proof (goal "plus_id_example") auto_dfs_tac;
  run_proof (goal "plus_id_exercise") auto_dfs_tac;
  run_proof (goal "andb_comm") (induct_tac >>> (induct_tac >>> simp_tac));
  run_proof (goal "andb_true_elim2")
    (induct_tac
    >>> (induct_tac
        >>> (intros_tac >>> try_ refl_tac >> simp_asm_tac ~with_asms:false)));
  (* TODO: conditionals *)
  [%expect
    {|
    ========================================
    all_zero (bits b1 b0 b1 b0) = false

    Proof Complete!
    with fuel: 54
    ========================================
    all_zero (bits b0 b0 b0 b0) = true

    Proof Complete!
    with fuel: 54
    ========================================
    next_working_day friday = monday

    Proof Complete!
    with fuel: 12
    ========================================
    next_working_day (next_working_day friday) = tuesday

    Proof Complete!
    with fuel: 17
    ========================================
    orb true false = true

    Proof Complete!
    with fuel: 19
    ========================================
    orb false false = false

    Proof Complete!
    with fuel: 19
    ========================================
    orb false true = true

    Proof Complete!
    with fuel: 19
    ========================================
    orb true true = true

    Proof Complete!
    with fuel: 19
    ========================================
    orb (orb false false) true = true

    Proof Complete!
    with fuel: 31
    ========================================
    nandb true false = true

    Proof Complete!
    with fuel: 24
    ========================================
    nandb false false = true

    Proof Complete!
    with fuel: 19
    ========================================
    nandb false true = true

    Proof Complete!
    with fuel: 19
    ========================================
    nandb true true = false

    Proof Complete!
    with fuel: 24
    ========================================
    andthreeb true true true = true

    Proof Complete!
    with fuel: 24
    ========================================
    andthreeb false true true = false

    Proof Complete!
    with fuel: 19
    ========================================
    andthreeb true false true = false

    Proof Complete!
    with fuel: 24
    ========================================
    andthreeb true true false = false

    Proof Complete!
    with fuel: 24
    Proof:
      intro_tac >>
      rewrite_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    m = n ==> plus m m = plus n n

    Proof Complete!
    with fuel: 26
    Proof:
      intro_tac >>
      rewrite_tac >>
      intro_tac >>
      rewrite_tac >>
      rewrite_tac >>
      rewrite_tac >>
      refl_tac
    ========================================
    n = m ==> m = o ==> plus n m = plus m o

    Proof Complete!
    with fuel: 52
    ========================================
    ∀x. ∀c. andb x c = andb c x

    Proof Complete!
    with fuel: 120
    ========================================
    ∀x. ∀c. andb x c = true ==> c = true

    Proof Complete!
    with fuel: 78
    |}]

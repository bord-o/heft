open Heft
open Tactic

let goal_of_string ?(asms = []) prg name =
  let _, g = Elaborator.named_goal_from_string prg name |> Result.get_ok in
  (asms, g)

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

  |}
  in
  let goal = goal_of_string prg "compute_day_test" in
  run_proof goal simp_tac;

  let prg =
    {|
  theorem compute_two_days :
      eq (next_working_day (next_working_day friday)) tuesday
    
  |}
  in
  let goal = goal_of_string prg "compute_two_days" in
  run_proof goal simp_tac;

  let prg =
    {|
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
  |}
  in
  let goal = goal_of_string prg "test_orb1" in
  run_proof goal simp_tac;

  let prg =
    {|
    theorem test_orb2 :  eq (orb false false) false 
    theorem test_orb3 :  eq (orb false true) true 
    theorem test_orb4 :  eq (orb true true) true 
    theorem test_orb5 : 
        eq 
            (orb 
                (orb false false)
                (true))
            true 
  |}
  in
  let goal = goal_of_string prg "test_orb2" in
  run_proof goal simp_tac;
  let goal = goal_of_string prg "test_orb3" in
  run_proof goal simp_tac;
  let goal = goal_of_string prg "test_orb4" in
  run_proof goal simp_tac;
  let goal = goal_of_string prg "test_orb5" in
  run_proof goal simp_tac;

  (* TODO: conditionals *)
  ();
  [%expect
    {|
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
    |}]

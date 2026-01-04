
open Kernel
open Derived
open Tactic

    (* let nat_def = *)
    (*   let nat_ty = TyCon ("nat", []) in *)
    (*   define_inductive "nat" [] *)
    (*     [ *)
    (*       { name = "Zero"; arg_types = [] }; *)
    (*       { name = "Suc"; arg_types = [ nat_ty ] }; *)
    (*     ] in *)
    (**)
    (* let plus_def = *)
    (*   let _ = init_types () in *)
    (*   let nat_ty = TyCon ("nat", []) in *)
    (*   let* nat_def = nat_def in *)
    (*   let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in *)
    (*   let z = nat_def.constructors |> List.assoc_opt "Zero" |> Option.get in *)
    (*   print_endline @@ show_term z; *)
    (**)
    (*   let n = make_var "n" nat_ty in *)
    (*   let m' = make_var "m'" nat_ty in *)
    (*   let r = make_var "r" (make_fun_ty nat_ty nat_ty) in *)
    (**)
    (*   let* zero_case = make_lam n n in *)
    (*   (* λn. n *) *)
    (*   let* suc_case = *)
    (*     let* r_n = make_app r n in *)
    (*     let* suc_rn = make_app suc r_n in *)
    (*     let* lam_n_suc_rn = make_lam n suc_rn in *)
    (*     let* lam_r = make_lam r lam_n_suc_rn in *)
    (*     make_lam m' lam_r (* λm'. λr. λn. Suc (r n) *) *)
    (*   in *)
    (**)
    (*   let return_type = make_fun_ty nat_ty nat_ty in *)
    (*   define_recursive_function "plus" return_type "nat" [ zero_case; suc_case ] in *)
let%expect_test "basic" = 
    let a = make_var "A" bool_ty in
    let b = make_var "B" bool_ty in
    let goal = make_conj a b in

    let next_tactic = next_tactic_of_list [conj_tac; assumption_tac; assumption_tac] in
    (match prove ([b], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      Destruct succeeded
      goal not in assumptions
      Proof Failed
      A
      |}]

let%expect_test "basic2" = 
    let a = make_var "A" bool_ty in
    let goal = safe_make_eq a a |> Result.get_ok in

    let next_tactic = next_tactic_of_list [refl_tac] in
    (match prove ([], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      destruct success
      refl success
      Proof Complete!
      ========================================
      A = A
      |}]

let%expect_test "basic3" = 
    let a = make_var "A" bool_ty in
    let goal = make_imp a a  in

    let next_tactic = next_tactic_of_list [intro_tac; assumption_tac] in
    (match prove ([], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      destruct success
      Found matching assumption
      Assumption succeeded
      disch success
      Proof Complete!
      ========================================
      A ==> A
      |}]

let%expect_test "basic4" = 
    let a = make_var "A" bool_ty in
    let b = make_var "B" bool_ty in

    let goal = make_disj a b  in

    let next_tactic = next_tactic_of_list [left_tac; assumption_tac] in
    (match prove ([a], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      Found matching assumption
      Assumption succeeded
      disj_left success
      Proof Complete!
      A
      ========================================
      A ∨ B
      |}]

let%expect_test "basic4" = 
    let a = make_var "A" bool_ty in
    let b = make_var "B" bool_ty in

    let goal = make_disj a b  in

    let next_tactic = next_tactic_of_list [right_tac; assumption_tac] in
    (match prove ([a], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      goal not in assumptions
      Proof Failed
      B
      |}]


let%expect_test "basic5" = 
    let a = make_var "A" bool_ty in
    let b = make_var "B" bool_ty in
    let c = make_var "C" bool_ty in

    let imp_ab = make_imp a b in
    let imp_abc = make_imp (make_imp c a) b in

    let goal = b  in

    let next_tactic = next_tactic_of_list [with_term_size_ranking apply_tac; assumption_tac] in
    (match prove ([imp_abc; imp_ab;  a], goal) next_tactic with
        Complete thm -> print_endline "Proof Complete!"; Printing.print_thm thm
        | Incomplete (_asms, g)-> 
                print_endline "Proof Failed"; 
                Printing.print_term g
    );

    [%expect {|
      |}]

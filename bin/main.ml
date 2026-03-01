open Heft
open Kernel
open Tactic

let () =
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
  let t = Sys.time () in
  let _ = run_proof goal proof in
  Printf.printf "execution time: %fs\n" (Sys.time () -. t)

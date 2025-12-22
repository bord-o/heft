# OneHOL

## Roadmap

**Essential Reading (in order):**

1. Harrison, *Handbook of Practical Logic and Automated Reasoning* — chapters 1-6, then chapter on HOL
2. Taha & Sheard, "MetaML and multi-stage programming with explicit annotations" (1997)
3. HOL Light source code — `fusion.ml` (the kernel)

**Secondary (when relevant):**

4. Davies & Pfenning, "A modal analysis of staged computation" (2001) — theoretical foundations for reflection typing
5. Harrison, "Towards Self-verification of HOL Light" (2006)

---

## Heuristics for Usability
- Visibility of system status
- Match between system and real proofs
- User control and freedom
- consistency
- error prevention
- recognition > recall
- flexibility and efficiency of use
- aesthetic and minimal design
- error recovery
- documentation

## TODOs
new_type_definition : string -> term -> thm -> hol_type * thm * thm
  (* Creates new type from subset of existing type *)
  (* Returns: (new_type, abs_fn, rep_fn) and theorems about them *)

new_recursive_definition : term -> thm
  (* Defines recursive function via well-founded recursion *)
  let%expect_test "test inductive nats" =
  let () = clear_env () in
  let _ = init_types () in
  let thm =
        let nat_ty =  TyCon ("nat", []) in
        let* nat_def = nat_def in
        let suc = nat_def.constructors |> List.assoc_opt "Suc" |> Option.get in

        let n = make_var "n"  nat_ty in
        let m = make_var "m" nat_ty in
        let m' = make_var "m'" nat_ty in
        let r = make_var "r" (make_fun_ty nat_ty nat_ty) in

        let* zero_case = make_lam n n in  (* λn. n *)
        let* suc_case =
            let* r_n = make_app r n in
            let* suc_rn = make_app suc r_n in
            let* lam_n_suc_rn = make_lam n suc_rn in
            let* lam_r = make_lam r lam_n_suc_rn in
            make_lam m' lam_r  (* λm'. λr. λn. Suc (r n) *)
        in
        let* typed_nat_def = inst_type ([(make_vartype "r", make_fun_ty nat_ty nat_ty)] |> List.to_seq |> Hashtbl.of_seq) nat_def.recursion in
        let* specced = specs [zero_case; suc_case] typed_nat_def in
        (* print_endline @@ pretty_print_thm ~with_type:true specced; *)
        let plus = make_var "plus" (make_fun_ty nat_ty (make_fun_ty nat_ty nat_ty)) in
        let* def = new_specification "plus" specced in
        Ok def 

  in

  print_thm_result thm;
  [%expect {|
    |}]


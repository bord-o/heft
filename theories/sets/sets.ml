open Heft
open Kernel
open Derived
open Tactic
open Auto

let () = print_endline "initializing theory sets"

(* Definitions *)
[%%inductive type 'a set = Set of ('a -> bool)]

let%def mem (x : 'a) (s : 'a set) : bool = match s with Set p -> p x
let%def empty_set : 'a set = Set (fun (x : 'a) -> false)
let%def univ_set : 'a set = Set (fun (x : 'a) -> true)

let%def union (s1 : 'a set) (s2 : 'a set) : 'a set =
  Set (fun (x : 'a) -> mem x s1 || mem x s2)

let%def inter (s1 : 'a set) (s2 : 'a set) : 'a set =
  Set (fun (x : 'a) -> mem x s1 && mem x s2)

let%def subset (s1 : 'a set) (s2 : 'a set) : bool =
  forall (fun (x : 'a) -> mem x s1 ==> mem x s2)

let%def diff (s1 : 'a set) (s2 : 'a set) : 'a set =
  Set (fun (x : 'a) -> mem x s1 && not (mem x s2))

let%def singleton (a : 'a) : 'a set = Set (fun (x : 'a) -> x = a)

(** Theorems *)

let%thm mem_empty (x : 'a) = not (mem x empty_set)

and proof =
  begin
    intros >> simp >> neg_intro >> assumption
  end
  [@quiet] [@simp]

let%thm mem_union (x : 'a) (s1 : 'a set) (s2 : 'a set) =
  mem x (union s1 s2) = (mem x s1 || mem x s2)

and proof =
  begin
    intros >> simp
  end
  [@quiet] [@simp]

let%thm mem_inter (x : 'a) (s1 : 'a set) (s2 : 'a set) =
  mem x (inter s1 s2) = (mem x s1 && mem x s2)

and proof =
  begin
    intros >> simp
  end
  [@quiet] [@simp]

let%thm set_inj (f : 'a -> bool) (g : 'a -> bool) = f = g ==> (Set f = Set g)

and proof =
  begin
    intros >> simp
  end
  [@simp] [@quiet]

let%thm disj_comm (a : bool) (b : bool) = (a || b) = (b || a)

and proof =
  begin
    intros >> eq_iff >> elim_disj_asm >> right >> assumption >> left
    >> assumption >> elim_disj_asm >> right >> assumption >> left >> assumption
  end
  [@quiet]

let%thm conj_comm (a : bool) (b : bool) = (a && b) = (b && a)

and proof =
  begin
    intros >> eq_iff >> elim_conj_asm >> conj >>> try_ assumption
    >> elim_conj_asm >> conj >>> try_ assumption
  end
  [@quiet]

let%thm union_comm (s1 : 'a set) (s2 : 'a set) = union s1 s2 = union s2 s1

and proof =
  begin
    intros >> simp
    >> with_term [%term (s1 : 'a set)] destruct
    >> elim_exists_asm >> simp
    >> with_term [%term (s2 : 'a set)] destruct
    >> elim_exists_asm >> simp
    >> with_proven [ "set_inj" ] apply
    >> fun_ext
    >> with_proven [ "disj_comm" ] rewrite
    >> refl
  end
  [@quiet]

let%thm inter_comm (s1 : 'a set) (s2 : 'a set) = inter s1 s2 = inter s2 s1

and proof =
  begin
    intros >> simp
    >> with_term [%term (s1 : 'a set)] destruct
    >> elim_exists_asm >> simp
    >> with_term [%term (s2 : 'a set)] destruct
    >> elim_exists_asm >> simp
    >> with_proven [ "set_inj" ] apply
    >> fun_ext
    >> with_proven [ "conj_comm" ] rewrite
    >> refl
  end
  [@quiet]

let%thm subset_refl (s : 'a set) = subset s s

and proof =
  begin
    intros >> simp
    >> with_term [%term (s : 'a set)] destruct
    >> elim_exists_asm >> simp >> intros >> assumption
  end
  [@quiet]

let apply_asm_to_asm ~asm_thm ~asm_to =
  with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))

let%thm subset_trans (s1 : 'a set) (s2 : 'a set) (s3 : 'a set) =
  subset s1 s2 ==> (subset s2 s3 ==> subset s1 s3)

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct
    >> with_term [%term (s2 : 'a set)] destruct
    >> with_term [%term (s3 : 'a set)] destruct
    >> with_repeat elim_exists_asm
    >> simp >> intros >> simp_asm
    >> apply_asm_to_asm ~asm_thm:0 ~asm_to:2
    >> apply_asm_to_asm ~asm_thm:2 ~asm_to:0
    >> assumption
  end
  [@quiet]

let%thm union_empty (s : 'a set) = union s empty_set = s

and proof =
  begin
    with_term [%term (s : 'a set)] induct
    >> intros >> simp
    >> with_proven [ "set_inj" ] apply
    >> fun_ext >> eq_iff >> left >> assumption >> elim_disj_asm >> assumption
    >> false_elim
  end
  [@quiet]

let%thm inter_univ (s : 'a set) = inter s univ_set = s

and proof =
  begin
    intros
    >> with_term [%term (s : 'a set)] destruct
    >> elim_exists_asm >> simp
    >> with_proven [ "set_inj" ] apply
    >> fun_ext >> eq_iff >> conj >> assumption >> truth >> elim_conj_asm
    >> assumption
  end
  [@quiet]

let%thm mem_singleton (x : 'a) (a : 'a) = mem x (singleton a) = (x = a)

and proof =
  begin
    intros >> simp
  end
  [@quiet] [@simp]

let%thm mem_diff (x : 'a) (s1 : 'a set) (s2 : 'a set) =
  mem x (diff s1 s2) = (mem x s1 && not (mem x s2))

and proof =
  begin
    intros >> simp
  end
  [@quiet] [@simp]

let%thm subset_antisym (s1 : 'a set) (s2 : 'a set) =
  subset s1 s2 ==> (subset s2 s1 ==> (s1 = s2))

and proof =
  begin
    intros @: [ "hsubset1"; "hsubset2" ]
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp_all >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "ha0'"; "ha0" ]
    >> (apply_at "hsubset2" ~target:"ha0'" >> assumption)
    >> (apply_at "hsubset1" ~target:"ha0" >> assumption)
  end
  [@quiet]

let%thm mem_subset (x : 'a) (s1 : 'a set) (s2 : 'a set) =
  mem x s1 ==> (subset s1 s2 ==> mem x s2)

and proof =
  begin
    intros @: [ "hsubset"; "hmem" ]
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp_all
    >> apply_at "hmem" ~target:"hsubset"
    >> assumption
  end
  [@quiet]

let%thm subset_union_l (s1 : 'a set) (s2 : 'a set) = subset s1 (union s1 s2)

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp_all >> intros >> left >> assumption
  end
  [@quiet]

let%thm subset_union_r (s1 : 'a set) (s2 : 'a set) = subset s2 (union s1 s2)

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp >> intros >> right >> assumption
  end
  [@quiet]

let%thm inter_subset_l (s1 : 'a set) (s2 : 'a set) = subset (inter s1 s2) s1

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp >> intros >> elim_conj_asm >> assumption
  end
  [@quiet]

let%thm inter_subset_r (s1 : 'a set) (s2 : 'a set) = subset (inter s1 s2) s2

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp >> intros >> elim_conj_asm >> assumption
  end
  [@quiet]

let%thm union_assoc (s1 : 'a set) (s2 : 'a set) (s3 : 'a set) =
  union s1 (union s2 s3) = union (union s1 s2) s3

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "hleft"; "hright" ]
    >> with_no_automation_trace
         (with_best_first (pick [ elim_disj_asm; or_; assumption ]))
    >> with_no_automation_trace
         (with_best_first (pick [ elim_disj_asm; or_; assumption ]))
  end
  [@quiet]

let%thm inter_assoc (s1 : 'a set) (s2 : 'a set) (s3 : 'a set) =
  inter s1 (inter s2 s3) = inter (inter s1 s2) s3

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> with_term [%term (s3 : 'a set)] destruct_elim @: [ "hs3" ]
    >> simp >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "hleft"; "hright" ]
    >> with_no_automation_trace
         (with_best_first (pick [ elim_conj_asm; conj; assumption ]))
    >> with_no_automation_trace
         (with_best_first (pick [ elim_conj_asm; conj; assumption ]))
  end
  [@quiet]

let%thm diff_subset (s1 : 'a set) (s2 : 'a set) = subset (diff s1 s2) s1

and proof =
  begin
    intros
    >> with_term [%term (s1 : 'a set)] destruct_elim @: [ "hs1" ]
    >> with_term [%term (s2 : 'a set)] destruct_elim @: [ "hs2" ]
    >> simp >> intros >> elim_conj_asm >> assumption
  end
  [@quiet]

let%thm diff_self (s : 'a set) = diff s s = empty_set

and proof =
  begin
    intros
    >> with_term [%term (s : 'a set)] destruct_elim @: [ "hs" ]
    >> simp >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "hleft"; "hright" ]
    >> false_elim >> elim_conj_asm >> neg_elim
  end
  [@quiet]

let%thm mem_univ (x : 'a) = mem x univ_set = true

and proof =
  begin
    intros >> simp
  end
  [@quiet] [@simp]

let%thm empty_subset (s : 'a set) = subset empty_set s

and proof =
  begin
    intros >> simp >> intros >> false_elim
  end
  [@quiet]

let%thm diff_empty (s : 'a set) = diff s empty_set = s

and proof =
  begin
    intros
    >> with_term [%term (s : 'a set)] destruct_elim
    >> simp >> apply_at "set_inj" >> fun_ext >> eq_iff
    >> with_no_automation_trace auto_dfs
    >> with_no_automation_trace auto_dfs
  end
  [@quiet]

let%thm union_inter_distrib (s : 'a set) (t : 'a set) (u : 'a set) =
  union s (inter t u) = inter (union s t) (union s u)

and proof =
  begin
    intros
    >> with_term [%term (s : 'a set)] destruct_elim
    >> with_term [%term (t : 'a set)] destruct_elim
    >> with_term [%term (u : 'a set)] destruct_elim
    >> simp >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "hleft"; "hright" ]
    >> with_no_automation_trace
         (with_best_first
            (pick [ elim_conj_asm; conj; assumption; elim_disj_asm; or_ ]))
    >> with_no_automation_trace
         (with_best_first
            (pick [ elim_conj_asm; conj; assumption; elim_disj_asm; or_ ]))
  end
  [@quiet]

let%thm inter_union_distrib (s : 'a set) (t : 'a set) (u : 'a set) =
  inter s (union t u) = union (inter s t) (inter s u)

and proof =
  begin
    intros
    >> with_term [%term (s : 'a set)] destruct_elim
    >> with_term [%term (t : 'a set)] destruct_elim
    >> with_term [%term (u : 'a set)] destruct_elim
    >> simp >> apply_at "set_inj" >> fun_ext
    >> eq_iff @: [ "hleft"; "hright" ]
    >> with_no_automation_trace
         (with_best_first
            (pick [ elim_conj_asm; conj; assumption; elim_disj_asm; or_ ]))
    >> with_no_automation_trace
         (with_best_first
            (pick [ elim_conj_asm; conj; assumption; elim_disj_asm; or_ ]))
  end
  [@quiet]

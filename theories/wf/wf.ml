open Heft
open Kernel
open Derived
open Tactic

(* [@@@warning "-26-27-32-33"] *)

(* ∀P. (∀n. (∀m. m < n ==> P m) ==> P n) ==> ∀n. P n *)
let%thm nat_induct_strong (p : nat -> bool) =
  forall (fun (n : nat) -> forall (fun (m : nat) -> nat_lt m n ==> p m) ==> p n)
  ==> forall (fun (n : nat) -> p n)

and proof =
  begin
    intros_tac @: [ "hstrong" ]
    >> with_term
         [%term
           forall (fun (n : nat) (m : nat) ->
               nat_lt m n ==> (p : nat -> bool) m)]
         assert_tac
       @: [ "hweak" ]
    >> induct_tac >> intros_tac >> simp_asm_tac >> false_elim_tac
    >> intros_tac @: [ "hIH"; "hlt" ]
    >> with_term [%term nat_lt (m : nat) (Suc (n0 : nat))] cases_tac
       @: [ "htrue"; "hfalse" ]
    >> rewrite_at_tac "lt_Suc_or_eq" ~target:"hlt"
    >> elim_disj_asm_tac @: [ "hlt_mn"; "heq_mn" ]
    >> apply_at_tac "hIH" ~target:"hlt_mn"
    >> assumption_tac >> rewrite_at_tac "heq_mn" >> apply_at_tac "hstrong"
    >> assumption_tac
    >> rewrite_at_tac "hfalse" ~target:"hlt"
    >> false_elim_tac
    (* TODO make apply handle nested quantification better*)
    >> with_named_asm_term "hweak" (spec_asm_tac [%term (n : nat)])
       @: [ "hweak'" ]
    >> with_named_asm_term "hstrong" (spec_asm_tac [%term (n : nat)])
       @: [ "hstrong'" ]
    >> apply_at_tac "hstrong'" ~target:"hweak'"
    >> assumption_tac
  end
  (* [@trace] *)
  [@quiet]

let%def wf (r : 'a -> 'a -> bool) : bool =
  forall (fun (p : 'a -> bool) ->
      forall (fun (x : 'a) -> forall (fun (y : 'a) -> r y x ==> p y) ==> p x)
      ==> forall (fun (x : 'a) -> p x))

let%thm wf_num = wf nat_lt

and proof =
  begin
    rewrite_at_tac "wf" >> beta_tac
    >> with_proven [ "nat_induct_strong" ] exact_tac
  end
  [@quiet]

let%thm wf_measure_gen (r : 'b -> 'b -> bool) (m : 'a -> 'b) =
  wf r ==> wf (fun (x : 'a) (y : 'a) -> r (m x) (m y))

and proof =
  begin
    rewrite_at_tac "wf" >> beta_tac >> rewrite_at_tac "wf" >> beta_tac
    >> intros_tac @: [ "hwflam"; "hwfr" ]
    >> with_named_asm_term "hwflam"
         (spec_asm_tac
            [%term
              fun (b : 'b) ->
                forall (fun (a : 'a) ->
                    (m : 'a -> 'b) a = b ==> (p : 'a -> bool) a)])
       @: [ "hwfspec" ]
    >> with_named_asm_term "hwfspec" assert_premise_tac @: [ "hprem" ]
    >> intros_tac @: [ "hall"; "heq" ]
    >> with_named_asm_term "hwfr" (spec_asm_tac [%term (a : 'a)])
       @: [ "hwfr_a" ]
    >> apply_at_tac "hwfr_a" >> intros_tac @: [ "hr" ]
    >> rewrite_at_tac "heq" ~target:"hr"
    >> apply_at_tac "hall" ~target:"hr" @: [ "hall'" ]
    >> apply_at_tac "hall'" >> refl_tac
    >> apply_at_tac "hwfspec" ~target:"hprem" @: [ "hall'" ]
    >> with_named_asm_term "hall'"
         (spec_asm_tac [%term (m : 'a -> 'b) (x : 'a)])
       @: [ "hfinal" ]
    >> apply_at_tac "hfinal" >> refl_tac
  end
  [@quiet]

let%def measure (m : 'a -> nat) : 'a -> 'a -> bool =
 fun (x : 'a) (y : 'a) -> nat_lt (m x) (m y)

(* let () = Printing.print_thm measure  *)

let%thm wf_measure (m : 'a -> nat) = wf (measure m)

and proof =
  begin
    rewrite_at_tac "measure" >> beta_tac >> gen_tac
    >> apply_at_tac "wf_measure_gen"
    >> with_proven [ "wf_num" ] exact_tac
  end
  [@quiet]

let%def wf_rec_cong (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b) : bool =
  forall (fun (f : 'a -> 'b) (g : 'a -> 'b) (x : 'a) ->
      forall (fun (z : 'a) -> r z x ==> (f z = g z)) ==> (h f x = h g x))

let%def wf_rec_rel (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b) (x : 'a)
    (v : 'b) : bool =
  forall (fun (s : 'a -> 'b -> bool) ->
      forall (fun (a : 'a) (b : 'b) (g : 'a -> 'b) ->
          forall (fun (y : 'a) -> r y a ==> s y (g y)) ==> (b = h g a ==> s a b))
      ==> s x v)

let%thm wf_rec_rel_intro (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b)
    (a : 'a) (g : 'a -> 'b) =
  forall (fun (y : 'a) -> r y a ==> wf_rec_rel r h y (g y))
  ==> wf_rec_rel r h a (h g a)

and proof =
  begin
    intros_tac @: [ "hall" ] >> simp_tac >> intros_tac @: [ "himp" ]
    >> with_specialized ~name:"himp"
         ~specs:
           [
             [%term (a : 'a)];
             [%term (h : ('a -> 'b) -> 'a -> 'b) (g : 'a -> 'b) (a : 'a)];
             [%term (g : 'a -> 'b)];
           ]
         apply_tac
    >> intros_tac @! "hrya"
    >> apply_at_tac "hall" ~target:"hrya" @! "hwfgy"
    >> rewrite_at_tac "wf_rec_rel" ~target:"hwfgy"
    >> with_named_asm_term "hwfgy" simp_asm_tac
    >> apply_at_tac "hwfgy"
    >> with_assumptions (with_first exact_tac)
    >> refl_tac
  end
  [@quiet]

let%thm wf_not_sym (r : 'a -> 'a -> bool) =
  wf r ==> forall (fun (a : 'a) (x : 'a) -> r a x ==> not (r x a))

and proof =
  begin
    noop_tac >> gen_tac >> intro_tac @! "hIH" >> simp_asm_tac
    >> spec_asm_tac
         [%term
           fun (a : 'a) ->
             forall (fun (x : 'a) ->
                 (r : 'a -> 'a -> bool) (a : 'a) x
                 ==> not ((r : 'a -> 'a -> bool) x (a : 'a)))]
       @! "hContraSpec"
    >> apply_at_tac "hContraSpec"
    >> intros_tac @: [ "hprem"; "hrxx" ]
    >> neg_intro_tac @! "hneg"
    >> with_named_asm_term "hprem" (spec_asm_tac [%term (x' : 'a)]) @! "hprem'"
    >> apply_at_tac "hprem'" ~target:"hneg" @! "hprem_disch"
    >> apply_at_tac "hprem_disch" ~target:"hneg" @! "hprem_disch'"
    >> neg_elim_tac
  end
  [@quiet]

let%thm wf_irrefl (r : 'a -> 'a -> bool) =
  wf r ==> forall (fun (x : 'a) -> not (r x x))

and proof =
  begin
    noop_tac >> gen_tac >> intro_tac @! "hIH" >> simp_asm_tac
    >> spec_asm_tac
         [%term fun (x : 'a) -> not ((r : 'a -> 'a -> bool) (x : 'a) (x : 'a))]
       @! "hContraSpec"
    >> apply_at_tac "hContraSpec" >> intros_tac @: [ "hprem" ]
    >> neg_intro_tac @! "hneg"
    >> apply_at_tac "hprem" ~target:"hneg"
    >> neg_elim_tac
  end
  [@quiet]

(* Harrison's version, the trivial counterexample of the set { x, y } *)
(* let%thm wf_not_sym' (r : 'a -> 'a -> bool) = *)
(*   wf r ==> forall (fun (x : 'a) (y : 'a) -> not (r x y && r y x)) *)
(* and proof = *)
(*   begin *)
(*     noop_tac >> gen_tac >> intro_tac @! "hIH" >> simp_asm_tac >> gen_tac *)
(*     >> gen_tac *)
(*     >> spec_asm_tac [%term fun (z : 'a) -> z = (x : 'a) || z = (y : 'a)] *)
(*        @! "hContraSpec" *)
(*     >> neg_intro_tac *)
(*     >> elim_conj_asm_tac @: [ "hleft"; "hright" ] *)
(*   end *)

let%thm wf_rec_rel_elim (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b)
    (x : 'a) (v : 'b) =
  wf_rec_rel r h x v
  ==> exists (fun (g : 'a -> 'b) ->
      forall (fun (y : 'a) -> r y x ==> wf_rec_rel r h y (g y)) && v = h g x)

and proof =
  begin
    intros_tac @! "hwf" >> simp_asm_tac
    >> spec_asm_tac
         [%term
           fun (a : 'a) (b : 'b) ->
             exists (fun (g : 'a -> 'b) ->
                 forall (fun (y : 'a) ->
                     (r : 'a -> 'a -> bool) y a
                     ==> wf_rec_rel
                           (r : 'a -> 'a -> bool)
                           (h : ('a -> 'b) -> 'a -> 'b)
                           y (g y))
                 && b = (h : ('a -> 'b) -> 'a -> 'b) g a)]
       @! "hwfSpec"
    >> apply_at_tac "hwfSpec"
    >> intros_tac @: [ "hallPrem"; "heqPrem" ]
    >> with_term [%term (g : 'a -> 'b)] exists_tac
    >> conj_tac >> intros_tac @: [ "hrya" ]
    >> apply_at_tac "hallPrem" ~target:"hrya"
    >> elim_exists_asm_tac @! "hgElim"
    >> elim_conj_asm_tac @: [ "heqg"; "hallrel" ]
    >> rewrite_at_tac "heqg"
    >> apply_at_tac "wf_rec_rel_intro"
    >> intros_tac @: [ "hryy" ]
    >> apply_at_tac "hallrel" ~target:"hryy"
    >> assumption_tac >> assumption_tac
  end
  [@quiet]

let%thm wf_rec_rel_functional (r : 'a -> 'a -> bool)
    (h : ('a -> 'b) -> 'a -> 'b) (x : 'a) (v : 'b) (v' : 'b) =
  wf r
  ==> (wf_rec_cong r h
      ==> (wf_rec_rel r h x v ==> (wf_rec_rel r h x v' ==> (v = v'))))

and proof =
  begin
    with_repeat gen_tac >> intro_tac @! "hwf" >> intro_tac @! "hcong"
    >> simp_asm_tac ~exclude:[ "wf_rec_cong"; "wf_rec_rel" ]
    >> spec_asm_tac
         [%term
           fun (x : 'a) ->
             forall (fun (v : 'b) (v' : 'b) ->
                 wf_rec_rel
                   (r : 'a -> 'a -> bool)
                   (h : ('a -> 'b) -> 'a -> 'b)
                   x v
                 ==> (wf_rec_rel
                        (r : 'a -> 'a -> bool)
                        (h : ('a -> 'b) -> 'a -> 'b)
                        x v'
                     ==> (v = v')))]
       @! "hwf'"
    >> generalize_tac [%term (v' : 'b)]
    >> generalize_tac [%term (v : 'b)]
    >> generalize_tac [%term (x : 'a)]
    >> apply_at_tac "hwf'"
    >> intros_tac @: [ "hIH"; "hRxv"; "hRxv'" ]
    >> (apply_at_tac "wf_rec_rel_elim" ~target:"hRxv'"
       >> elim_exists_asm_tac >> elim_conj_asm_tac)
       @: [ ""; ""; "hRxv'Eq"; "hRxv'Elim" ]
    >> (apply_at_tac "wf_rec_rel_elim" ~target:"hRxv"
       >> elim_exists_asm_tac >> elim_conj_asm_tac)
       @: [ ""; ""; "hRxvEq"; "hRxvElim" ]
    >> rewrite_at_tac "hRxvEq" >> rewrite_at_tac "hRxv'Eq"
    >> rewrite_at_tac "wf_rec_cong" ~target:"hcong"
    >> beta_asm_tac >> apply_at_tac "hcong" >> intros_tac @! "hrzx"
    (* TODO: allow discharging multiple premises in one tactic to avoid intermediate names*)
    >> apply_at_tac "hRxvElim" ~target:"hrzx" @! "hRzGz"
    >> apply_at_tac "hRxv'Elim" ~target:"hrzx" @! "hRzG'z"
    >> apply_at_tac "hIH" ~target:"hrzx" @! "hIHprem"
    >> apply_at_tac "hIHprem" ~target:"hRzGz" @! "hIHprem'"
    >> apply_at_tac "hIHprem'" ~target:"hRzG'z"
    >> assumption_tac
  end
  [@quiet]

let%thm wf_rec_rel_total (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b)
    (x : 'a) =
  wf r ==> exists (fun (v : 'b) -> wf_rec_rel r h x v)

and proof =
  begin
    noop_tac >> with_repeat gen_tac >> intro_tac @! "hwf" >> simp_asm_tac
    >> spec_asm_tac
         [%term
           fun (x : 'a) ->
             exists (fun (v : 'b) ->
                 wf_rec_rel
                   (r : 'a -> 'a -> bool)
                   (h : ('a -> 'b) -> 'a -> 'b)
                   x v)]
       @! "hIH"
    >> generalize_tac [%term (x : 'a)]
    >> apply_at_tac "hIH" >> intros_tac @! "hprem"
    >> with_term
         [%term
           (h : ('a -> 'b) -> 'a -> 'b)
             (fun (y : 'a) ->
               choose (fun (x : 'b) ->
                   wf_rec_rel
                     (r : 'a -> 'a -> bool)
                     (h : ('a -> 'b) -> 'a -> 'b)
                     y x))
             (x : 'a)]
         exists_tac
    >> apply_at_tac "wf_rec_rel_intro"
    >> intros_tac @! "hryx"
    >> apply_at_tac "hprem" ~target:"hryx" @! "hwfExists"
    >> beta_tac
    >> apply_at_tac "axiom_of_choice" ~target:"hwfExists" @! "hwfChosen"
    >> with_assumptions (with_first exact_tac)
  end
  [@quiet]

let%thm wf_rec (r : 'a -> 'a -> bool) (h : ('a -> 'b) -> 'a -> 'b) =
  wf r
  ==> (wf_rec_cong r h
      ==> exists (fun (f : 'a -> 'b) -> forall (fun (x : 'a) -> f x = h f x)))

and proof =
  begin
    noop_tac
    >> intros_tac @: [ "hwf"; "hcong" ]
    >> apply_at_tac "wf_rec_rel_functional" ~target:"hwf" @! "hfunctional1"
    >> apply_at_tac "hfunctional1" ~target:"hcong" @! "hfunctional2"
    >> with_term
         [%term
           fun (x : 'a) ->
             choose (fun (v : 'b) ->
                 wf_rec_rel
                   (r : 'a -> 'a -> bool)
                   (h : ('a -> 'b) -> 'a -> 'b)
                   x v)]
         exists_tac
    >> intros_tac
    >> apply_at_tac "wf_rec_rel_total" ~target:"hwf" @! "hRxv"
    >> spec_asm_tac [%term (h : ('a -> 'b) -> 'a -> 'b)] @! "hall1"
    >> spec_asm_tac [%term (x : 'a)] @! "hwfExists"
    >> apply_at_tac "axiom_of_choice" ~target:"hwfExists" @! "hwfChosen"
    >> apply_at_tac "wf_rec_rel_elim" ~target:"hwfChosen" @! "hwfElim"
    >> (elim_exists_asm_tac >> elim_conj_asm_tac) @: [ ""; "heq"; "hallR" ]
    >> rewrite_at_tac "heq"
    >> rewrite_at_tac "wf_rec_cong" ~target:"hcong"
    >> beta_asm_tac
    >> spec_asm_tac [%term (g : 'a -> 'b)] @! "h1"
    >> spec_asm_tac
         [%term
           fun (x : 'a) ->
             choose (fun (v : 'b) ->
                 wf_rec_rel
                   (r : 'a -> 'a -> bool)
                   (h : ('a -> 'b) -> 'a -> 'b)
                   x v)]
       @! "h2"
    >> spec_asm_tac [%term (x : 'a)] @! "hcongSpec"
    >> apply_at_tac "hcongSpec" >> intros_tac @! "hrzx"
    >> apply_at_tac "hallR" ~target:"hrzx" @! "hRzx"
    >> with_named_asm_term "hall1" (spec_asm_tac [%term (z : 'a)])
       @! "hrzExists"
    >> apply_at_tac "axiom_of_choice" ~target:"hrzExists" @! "hrzChosen"
    >> with_named_asm_term "hfunctional2" (spec_asm_tac [%term (z : 'a)])
       @! "hfunc_z"
    >> with_named_asm_term "hfunc_z"
         (spec_asm_tac [%term (g : 'a -> 'b) (z : 'a)])
       @! "hfunc_gz"
    >> with_named_asm_term "hfunc_gz"
         (spec_asm_tac
            [%term
              choose (fun (_u : 'b) ->
                  wf_rec_rel
                    (r : 'a -> 'a -> bool)
                    (h : ('a -> 'b) -> 'a -> 'b)
                    (z : 'a)
                    _u)])
       @! "hfunc_full"
    >> apply_at_tac "hfunc_full" ~target:"hRzx" @! "hfunc_almost"
    >> apply_at_tac "hfunc_almost" ~target:"hrzChosen"
    >> with_assumptions (with_first exact_tac)
  end
  [@quiet]

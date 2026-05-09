[@@@warning "-26-27-32-33"]
(* (* [@@@ocamlformat "disable"] *) *)

open Heft
open Tactic
open Auto

let () =
  print_newline ();
  print_newline ()

(* Using nat instead of string for vname *)
[%%inductive type aexp = N of nat | V of nat | Plus of aexp * aexp]

(* Val : nat *)
(* State : nat -> nat *)
let%def update (f : nat -> nat) (a : nat) (b : nat) : nat =
 fun (n : nat) -> if n = a then b else f n

let%primrec aval (e : aexp) (s : nat -> nat) : nat =
  match e with
  | N n -> n
  | V x -> s x
  | Plus (a1, a2) -> plus (aval a1 s) (aval a2 s)

let%primrec asimp_const (e : aexp) : aexp =
  match e with
  | N n -> N n
  | V x -> V x
  | Plus (a1, a2) -> (
      match (asimp_const a1 : aexp) with
      | N n1 -> (
          match (asimp_const a2 : aexp) with
          | N n2 -> N (plus n1 n2)
          | V x -> Plus (N n1, V x)
          | Plus (a, b) -> Plus (N n1, Plus (a, b)))
      | V x -> (
          match (asimp_const a2 : aexp) with
          | N n2 -> Plus (V x, N n2)
          | V y -> Plus (V x, V y)
          | Plus (a, b) -> Plus (V x, Plus (a, b)))
      | Plus (a, b) -> (
          match (asimp_const a2 : aexp) with
          | N n2 -> Plus (Plus (a, b), N n2)
          | V y -> Plus (Plus (a, b), V y)
          | Plus (c, d) -> Plus (Plus (a, b), Plus (c, d))))

let auto =
  with_no_automation_trace
    (with_dfs'
       (pick
          [
            simp;
            gen;
            intro;
            truth;
            assumption;
            neg_intro;
            elim_disj_asm;
            conj;
            elim_conj_asm;
            elim_exists_asm;
            false_elim;
            with_assumptions (with_first_term apply_asm);
            simp_asm;
          ]))

let%thm _asimp_const_correct (a : aexp) (s : nat -> nat) =
  aval (asimp_const a) s = aval a s

and proof =
  begin
    induct @>> try_ auto (* first two cases are trivial*)
    >> intros
    >> with_term [%term asimp_const (n0 : aexp)] destruct
       (* Nine cases from the definitions inner matches *)
       @>> with_term [%term asimp_const (n1 : aexp)] destruct
       @>> with_repeat auto
  end
  [@quiet]

let%def aplus (l : aexp) (r : aexp) : aexp =
  match l with
  | N i1 -> (
      match r with
      | N i2 -> N (plus i1 i2)
      | V x1 -> if i1 = 0n then V x1 else Plus (N i1, V x1)
      | Plus (l2, r2) ->
          if i1 = 0n then Plus (l2, r2) else Plus (N i1, Plus (l2, r2)))
  | V x -> (
      match r with
      | N i3 -> if i3 = 0n then V x else Plus (V x, N i3)
      | V x2 -> Plus (V x, V x2)
      | Plus (l3, r3) -> Plus (V x, Plus (l3, r3)))
  | Plus (l1, r1) -> (
      match r with
      | N i3 -> if i3 = 0n then Plus (l1, r1) else Plus (Plus (l1, r1), N i3)
      | V x2 -> Plus (Plus (l1, r1), V x2)
      | Plus (l3, r3) -> Plus (Plus (l1, r1), Plus (l3, r3)))

let auto =
  with_no_automation_trace
    (with_dfs'
       (pick
          [
            simp;
            gen;
            intro;
            truth;
            assumption;
            neg_intro;
            elim_disj_asm;
            conj;
            elim_conj_asm;
            elim_exists_asm;
            eq_true_elim_asm;
            false_elim;
            with_assumptions (with_first_term apply_asm);
            simp_asm;
            cond;
          ]))

let%thm aval_plus (a1 : aexp) (a2 : aexp) (s : nat -> nat) =
  aval (aplus a1 a2) s = plus (aval a1 s) (aval a2 s)

and proof =
  begin
    intros
    >> with_term [%term (a1 : aexp)] destruct
       @>> with_term [%term (a2 : aexp)] destruct
       @>> with_repeat auto
  end
  [@quiet]

let%primrec asimp (e : aexp) : aexp =
  match e with
  | N n -> N n
  | V x -> V x
  | Plus (a1, a2) -> aplus (asimp a1) (asimp a2)

let%thm asimp_correct (e : aexp) (s : nat -> nat) = aval (asimp e) s = aval e s

and proof =
  begin
    induct @>> intros @>> try_ simp
    >> with_term [%term asimp (n0 : aexp)] destruct
       @>> with_term [%term asimp (n1 : aexp)] destruct
       @>> with_repeat auto
  end
  [@quiet]

let%primrec optimal (e : aexp) : bool =
  match e with
  | N n -> true
  | V x -> true
  | Plus (l, r) -> (
      match (l : aexp) with
      | N n -> (
          match (r : aexp) with
          | N n -> false
          | V x -> true
          | Plus (l1, r1) -> optimal r)
      | V x -> optimal r
      | Plus (l1, r1) -> optimal l && optimal r)

let%thm asimp_optimal (e : aexp) = optimal (asimp_const e)

and proof =
  begin
    induct @>> intros @>> try_ simp
    >> with_term [%term asimp_const (n0 : aexp)] destruct
       @>> with_term [%term asimp_const (n1 : aexp)] destruct
       @>> with_repeat auto
  end
  [@quiet]

(* TODO: this is starting to get really annoying without proper pattern matching support *)
(* let%primrec full_asimp (e : aexp) : aexp =  *)
(*     match e with *)
(*     | N n -> N n *)
(*     | V x -> V x *)
(*     | Plus (l, r) -> *)
let auto =
  with_no_automation_trace
    (with_dfs'
       (pick
          [
            simp;
            gen;
            intro;
            truth;
            assumption;
            neg_intro;
            elim_disj_asm;
            conj;
            elim_conj_asm;
            elim_exists_asm;
            eq_true_elim_asm;
            false_elim;
            or_;
            with_assumptions (with_first_term apply_asm);
            with_assumptions apply;
            simp_asm;
            cond;
            discriminate;
          ]))

let%primrec in_ (l : 'a list) (x : 'a) : bool =
  match l with [] -> false | x' :: l' -> x' = x || in_ l' x

let%primrec all (l : 'a list) (p : 'a -> bool) : bool =
  match l with [] -> true | x' :: l' -> p x' && all l' p

let%thm all_in (l : 'a list) (p : 'a -> bool) =
  forall (fun (x : 'a) -> in_ l x ==> p x) ==> all l p
  && all l p ==> forall (fun (x : 'a) -> in_ l x ==> p x)

and proof =
  begin
    induct >>= [ auto; intros @>> spec_asm [%term (p : 'a -> bool)] >> auto ]
  end
(* [@quiet] *)

let%primrec hd_error (l : 'a list) : 'a option =
  match l with [] -> None | x :: xs -> Some x

(* ∀l a. hd_error l = Some a -> l <> Nil*)
let%thm coq_paper (l : 'a list) (a : 'a) = hd_error l = Some a ==> not (l = Nil)

and proof =
  auto
  (* [@trace] *)
  [@quiet]

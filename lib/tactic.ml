open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax
open Rewrite

type goal = term list * term [@@deriving show]
type level = Debug | Info | Warn | Error | Proof
type proof_state = Incomplete of goal | Complete of thm [@@deriving show]
type tactic = goal -> thm
type tactic_combinator = tactic -> tactic
type priority = Safe | Unsafe of int

type _ rankable =
  | Priority : (tactic * priority * goal) list -> (tactic * goal) rankable
  | Term : term list -> term rankable
  | Goal : goal list -> goal rankable
  | Tactic : tactic list -> tactic rankable
  | Unknown : 'a list -> 'a rankable

type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
  | Goal : goal list -> goal choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable

exception Out_of_fuel

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Rank : 'a rankable -> 'a list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Burn : int -> unit Effect.t
  | Rules : unit -> thm list Effect.t

let as_ranked_list : type a. a rankable -> a list = function
  | Priority l -> List.map (fun (tac, _pri, g) -> (tac, g)) l
  | Term ts -> ts
  | Goal gs -> gs
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let as_chosen_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Theorem thms -> thms
  | Goal gs -> gs
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let fail () = perform Fail
let burn n = perform (Burn n)
let trace_dbg a = perform (Trace (Debug, a))
let trace_info a = perform (Trace (Info, a))
let trace_error a = perform (Trace (Error, a))
let trace_proof a = perform (Trace (Proof, a))

let return_thm ?(from = "unknown") = function
  | Ok thm ->
      perform (Trace (Proof, from));
      thm
  | Error e ->
      trace_error @@ print_error e;
      fail ()

let choose_goals gs = perform (Choose (Goal gs))
let choose_terms gs = perform (Choose (Term gs))
let choose_theorems gs = perform (Choose (Theorem gs))
let choose_tactics gs = perform (Choose (Tactic gs))
let choose_unknowns gs = perform (Choose (Unknown gs))
let rank_terms ts = perform (Rank (Term ts))

let rec choose_subgoals acc = function
  | [] -> List.rev acc
  | goals ->
      (goals
      |> List.iteri @@ fun idx g ->
         trace_info (string_of_int idx ^ ": " ^ pretty_print_hol_term (snd g));
         ());
      let chosen = perform @@ Choose (Goal goals) in

      let thm = perform (Subgoal chosen) in
      let rest = List.filter (( <> ) chosen) goals in
      choose_subgoals ((chosen, thm) :: acc) rest

let wrap_all = List.map

let left_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  let thm =
    let* l = side_of_op "\\/" Left concl in
    let* r = side_of_op "\\/" Right concl in
    let l_thm = perform (Subgoal (asms, l)) in
    let t = disj_left r l_thm in
    trace_dbg "disj_left success";
    t
  in
  return_thm ~from:"left_tac" thm

let right_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  let thm =
    let* l = side_of_op "\\/" Left concl in
    let* r = side_of_op "\\/" Right concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm ~from:"right_tac" thm

let or_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  let tac = choose_tactics [ left_tac; right_tac ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or_tac" thm

let apply_asm_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  (* Find implications in the asms that match the conclusion *)
  let matching =
    asms
    |> List.filter_map (fun asm ->
        match destruct_imp asm with
        | Ok (prem, conc) when conc = concl -> Some (asm, prem)
        | _ -> None)
  in

  let choices = rank_terms (List.map fst matching) in
  let chosen = choose_terms choices in
  let h = matching |> List.assoc chosen in

  let thm =
    let* assumed = assume chosen in
    trace_dbg "assume chosen h success";
    let sub_thm = perform (Subgoal (asms, h)) in
    let thm = mp assumed sub_thm in
    trace_dbg "mp success";
    thm
  in
  return_thm ~from:"apply_asm_tac" thm

(* Apply a theorem, strips foralls, matches conclusion against goal *)
let apply_thm_tac : tactic =
 fun (asms, conc) ->
  burn 3;
  let lemmas = perform (Rules ()) in
  let chosen_thm = choose_theorems lemmas in

  let rec strip_foralls_acc thm vars =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let thm' = Derived.spec var thm in
        match thm' with
        | Ok thm' -> strip_foralls_acc thm' (var :: vars)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] in

  let thm =
    match destruct_imp (concl stripped_thm) with
    | Ok (_prem, thm_conc) -> (
        match Rewrite.match_term thm_conc conc with
        | Some env ->
            let all_vars_bound =
              List.for_all
                (fun v ->
                  let v_typed = Rewrite.term_type_subst env.type_sub v in
                  List.exists
                    (fun (pat, _) -> alphaorder pat v_typed = 0)
                    env.term_sub)
                quant_vars
            in
            if not all_vars_bound then fail ();

            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            let* fully_inst = inst term_sub_flipped type_inst in

            let* inst_prem, _ = destruct_imp (concl fully_inst) in
            let sub_thm = perform (Subgoal (asms, inst_prem)) in
            mp fully_inst sub_thm
        | None -> fail ())
    | Error _ -> (
        match Rewrite.match_term (concl stripped_thm) conc with
        | Some env ->
            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            inst term_sub_flipped type_inst
        | None -> fail ())
  in
  return_thm ~from:"apply_thm_tac" thm

(* Apply a theorem to an assumption, producing a new assumption.
   If theorem is P ==> Q and assumption is P, replaces with Q. *)
let apply_thm_asm_tac : tactic =
 fun (asms, conc) ->
  burn 3;
  let lemmas = perform (Rules ()) in
  let chosen_thm = choose_theorems lemmas in
  let chosen_asm = choose_terms asms in

  let rec strip_foralls_acc thm vars =
    match destruct_forall (concl thm) with
    | Ok (var, _body) -> (
        let thm' = Derived.spec var thm in
        match thm' with
        | Ok thm' -> strip_foralls_acc thm' (var :: vars)
        | Error _ -> (thm, List.rev vars))
    | Error _ -> (thm, List.rev vars)
  in
  let stripped_thm, quant_vars = strip_foralls_acc chosen_thm [] in

  let thm =
    match destruct_imp (concl stripped_thm) with
    | Ok (prem, _thm_conc) -> (
        match Rewrite.match_term prem chosen_asm with
        | Some env ->
            let all_vars_bound =
              List.for_all
                (fun v ->
                  let v_typed = Rewrite.term_type_subst env.type_sub v in
                  List.exists
                    (fun (pat, _) -> alphaorder pat v_typed = 0)
                    env.term_sub)
                quant_vars
            in
            if not all_vars_bound then fail ();

            let* type_inst = inst_type env.type_sub stripped_thm in
            let term_sub_flipped =
              List.map (fun (v, t) -> (t, v)) env.term_sub
            in
            let* fully_inst = inst term_sub_flipped type_inst in

            let* _, new_asm = destruct_imp (concl fully_inst) in

            let asms' = new_asm :: List.filter (( <> ) chosen_asm) asms in
            let sub_thm = perform (Subgoal (asms', conc)) in

            let* asm_thm = assume chosen_asm in
            let* new_asm_thm = mp fully_inst asm_thm in
            prove_hyp new_asm_thm sub_thm
        | None -> fail ())
    | Error _ -> fail ()
  in
  return_thm ~from:"apply_thm_asm_tac" thm

let apply_neg_asm_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  let false_tm = make_false () in
  if concl <> false_tm then fail ()
  else
    let negs = List.filter is_neg asms in
    if List.is_empty negs then fail ()
    else
      let thm =
        let chosen = choose_terms negs in
        let* p = term_of_negation chosen in
        if List.mem p asms then fail ()
        else
          let* neg_thm = assume chosen in
          let* elim = not_elim neg_thm in
          let sub_thm = perform (Subgoal (asms, p)) in
          prove_hyp sub_thm elim
      in
      return_thm ~from:"apply_neg_asm_tac" thm

let assume_tac : tactic =
 fun (_asms, conc) -> return_thm ~from:"assume_tac" @@ assume conc

let sym_tac : tactic =
 fun (asms, conc) ->
  burn 1;
  let thm =
    let* l, r = destruct_eq conc in
    let* flipped = safe_make_eq r l in
    let flip_thm = perform @@ Subgoal (asms, flipped) in
    sym flip_thm
  in
  return_thm ~from:"sym_tac" thm

(* tries to rewrite anywhere in the goal using subterm matching *)
let rewrite_tac : tactic =
 fun (asms, conc) ->
  burn 2;
  let thm =
    let rules = perform (Rules ()) in
    let* chosen_rule = strip_forall (choose_theorems rules) in

    let* rw_thm = rewrite_once chosen_rule conc in
    let* _, conc_rewritten = destruct_eq (concl rw_thm) in
    (* Fail if no progress was made *)
    if alphaorder conc conc_rewritten = 0 then fail ();
    let subthm = perform @@ Subgoal (asms, conc_rewritten) in
    let* rw_sym = sym rw_thm in
    eq_mp rw_sym subthm
  in
  return_thm ~from:"rewrite_tac" thm

(* rewrites in an assumption *)
let rewrite_asm_tac : tactic =
 fun (asms, conc) ->
  burn 2;
  let thm =
    let rules = perform (Rules ()) in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let chosen_asm = choose_terms asms in

    let* rw_thm = rewrite_once chosen_rule chosen_asm in
    let* _, asm_rewritten = destruct_eq (concl rw_thm) in
    if alphaorder chosen_asm asm_rewritten = 0 then fail ();

    let asms' = asm_rewritten :: List.filter (( <> ) chosen_asm) asms in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp rw_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"rewrite_asm_tac" thm

let beta_tac : tactic =
 fun (asms, conc) ->
  burn 1;
  let thm =
    let* beta_thm = deep_beta conc in
    let* _, conc_reduced = destruct_eq (concl beta_thm) in
    let subthm = perform @@ Subgoal (asms, conc_reduced) in
    let* beta_sym = sym beta_thm in
    eq_mp beta_sym subthm
  in
  return_thm ~from:"beta_tac" thm

let beta_asm_tac : tactic =
 fun (asms, conc) ->
  burn 1;
  let thm =
    let chosen_asm = choose_terms asms in
    let* beta_thm = deep_beta chosen_asm in
    let* _, asm_reduced = destruct_eq (concl beta_thm) in
    if alphaorder chosen_asm asm_reduced = 0 then fail ();

    let asms' = asm_reduced :: List.filter (( <> ) chosen_asm) asms in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp beta_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"beta_asm_tac" thm

let mp_asm_tac : tactic =
 fun (asms, concl) ->
  burn 3;
  let imps = List.filter is_imp asms in
  if List.is_empty imps then fail ()
  else
    let thm =
      let chosen_imp = choose_terms imps in
      let* prem, conc = destruct_imp chosen_imp in
      if List.mem prem asms && not (List.mem conc asms) then
        let asms' = conc :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        let* imp_thm = assume chosen_imp in
        let* prem_thm = assume prem in
        let* conc_thm = mp imp_thm prem_thm in
        prove_hyp conc_thm sub_thm
      else fail ()
    in
    return_thm ~from:"mp_asm_tac" thm

let intro_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let thm =
    let* hyp = side_of_op "==>" Left concl in
    let* conc = side_of_op "==>" Right concl in
    trace_dbg "destruct success";

    let body_thm = perform (Subgoal (hyp :: asms, conc)) in
    let t = disch hyp body_thm in
    trace_dbg "disch success";
    t
  in
  return_thm ~from:"intro_tac" thm

let refl_tac : tactic =
 fun (_asms, concl) ->
  let thm =
    let* l, r = destruct_eq concl in
    trace_dbg "destruct success";
    if l = r then (
      let t = refl l in
      trace_dbg "refl success";
      t)
    else (
      trace_error "refl failure: left and right not eq";
      fail ())
  in
  return_thm ~from:"refl_tac" thm

let assumption_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let asm = choose_terms asms in
  if concl <> asm then (
    trace_error "assumption doesn't match the goal";
    fail ())
  else (
    trace_dbg "Found matching assumption";
    let t = assume concl in
    trace_dbg "Assumption succeeded";
    return_thm ~from:"assumption_tac" t)

let conj_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let thm =
    let* l, r = destruct_conj concl in
    trace_dbg "Destruct succeeded";

    let goals = [ (asms, l); (asms, r) ] in
    let solved = choose_subgoals [] goals in
    let lthm = solved |> List.assoc (asms, l) in
    let rthm = solved |> List.assoc (asms, r) in

    let* thm = conj lthm rthm in

    trace_dbg "conj success";
    Ok thm
  in
  return_thm ~from:"conj_tac" thm

let elim_disj_asm_tac : tactic =
 fun (asms, concl) ->
  burn 4;
  let disjs = List.filter is_disj asms in
  if List.is_empty disjs then fail ()
  else
    let thm =
      let chosen = choose_terms disjs in
      let* l, r = destruct_disj chosen in
      let asms' = List.filter (( <> ) chosen) asms in

      let left_goal = (l :: asms', concl) in
      let right_goal = (r :: asms', concl) in
      let goals = [ left_goal; right_goal ] in

      let solved = choose_subgoals [] goals in
      let left_thm = solved |> List.assoc left_goal in
      let right_thm = solved |> List.assoc right_goal in

      let* disj_asm = assume chosen in
      disj_cases disj_asm left_thm right_thm
    in
    return_thm ~from:"elim_disj_asm_tac" thm

let elim_conj_asm_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let conjs = List.filter is_conj asms in
  if List.is_empty conjs then fail ()
  else
    let thm =
      let chosen = choose_terms conjs in
      let* l, r = destruct_conj chosen in
      let asms' = l :: r :: List.filter (( <> ) chosen) asms in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* conj_asm = assume chosen in
      let* l_thm = conj_left conj_asm in
      let* r_thm = conj_right conj_asm in
      let* p_1 = prove_hyp r_thm sub_thm in
      prove_hyp l_thm p_1
    in
    return_thm ~from:"elim_conj_asm_tac" thm

let neg_elim_tac : tactic =
 fun (asms, concl) ->
  burn 2;
  let negs = List.filter is_neg asms in
  if List.is_empty negs then fail ()
  else
    let thm =
      let chosen_neg = choose_terms negs in
      let* p = term_of_negation chosen_neg in
      if List.mem p asms then
        let* neg_thm = assume chosen_neg in
        let* p_thm = assume p in
        let* false_thm = not_elim neg_thm in
        let* false_proved = prove_hyp p_thm false_thm in
        contr concl false_proved
      else fail ()
    in
    return_thm ~from:"neg_elim_tac" thm

let neg_intro_tac : tactic =
 fun (asms, concl) ->
  burn 2;
  let thm =
    let* p = term_of_negation concl in
    if List.mem p asms then fail ()
    else
      let f = make_false () in
      let goal' = (p :: asms, f) in
      let sub_thm = perform (Subgoal goal') in
      not_intro p sub_thm
  in
  return_thm ~from:"neg_intro_tac" thm

let ccontr_tac : tactic =
 fun (asms, concl) ->
  burn 8;
  let false_tm = make_false () in
  let neg_concl = make_neg concl in
  if concl = false_tm || List.mem neg_concl asms then fail ()
  else
    let thm =
      let goal' = (neg_concl :: asms, false_tm) in
      let sub_thm = perform (Subgoal goal') in
      ccontr concl sub_thm
    in
    return_thm ~from:"ccontr_tac" thm

let false_elim_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let false_tm = make_false () in
  if List.mem false_tm asms then
    let thm =
      let* false_thm = assume false_tm in
      contr concl false_thm
    in
    return_thm ~from:"false_elim_tac" thm
  else fail ()

let gen_tac : tactic =
 fun (asms, concl) ->
  burn 1;
  let thm =
    let* x, body = destruct_forall concl in
    let body_thm = perform (Subgoal (asms, body)) in
    let hyps_with_x = List.filter (fun h -> var_free_in x h) (hyp body_thm) in
    let* discharged =
      List.fold_left
        (fun acc h ->
          let* thm = acc in
          disch h thm)
        (Ok body_thm) hyps_with_x
    in
    gen x discharged
  in
  return_thm ~from:"gen_tac" thm

let induct_tac : tactic =
 fun (asms, concl) ->
  burn 5;
  let thm =
    let* induction_var, bod = destruct_forall concl in
    let* ty = type_of_term induction_var in
    let* ty_name, ty_args = destruct_type ty in

    let inductive_def =
      match Hashtbl.find_opt the_inductives ty_name with
      | None ->
          trace_error "quantified type is not an inductive";
          fail ()
      | Some d -> d
    in

    let* _, def_ty_params = destruct_type inductive_def.ty in

    let type_sub = List.combine def_ty_params ty_args in

    let* typed_induction = inst_type type_sub inductive_def.induction in

    let binder = make_var "pred_binder" ty in
    let* bod_with_binder = vsubst [ (binder, induction_var) ] bod in
    let* p = make_lam binder bod_with_binder in

    let* inst_induction = spec p typed_induction in

    let rec collect_premises tm acc =
      match destruct_imp tm with
      | Ok (premise, rest) -> collect_premises rest (premise :: acc)
      | Error _ -> (List.rev acc, tm)
    in
    let cases, _conclusion =
      collect_premises (Kernel.concl inst_induction) []
    in

    let goals = List.map (fun case -> (asms, case)) cases in
    let solved = choose_subgoals [] goals in

    let* result =
      List.fold_left
        (fun acc_thm (_goal, case_thm) ->
          let* acc = acc_thm in
          mp acc case_thm)
        (Ok inst_induction)
        (List.map (fun g -> (g, List.assoc g solved)) goals)
    in
    Ok result
  in
  return_thm ~from:"induction_tac" thm

(* Complete automation for propositional logic goals *)
let ctauto_tac : tactic =
 fun goal ->
  let tac =
    choose_tactics
      [
        assumption_tac;
        intro_tac;
        neg_intro_tac;
        gen_tac;
        conj_tac;
        elim_conj_asm_tac;
        elim_disj_asm_tac;
        false_elim_tac;
        neg_elim_tac;
        apply_asm_tac;
        apply_neg_asm_tac;
        mp_asm_tac;
        left_tac;
        right_tac;
        ccontr_tac;
      ]
  in
  tac goal

(* 
   As a general rule, custom handlers should handle the least amount of 
   effects possible. The main handler captures all effects, but implements only basic
   interpretations of them.
*)
let rec prove g tactic_queue =
  match Queue.take_opt tactic_queue with
  | None ->
      print_endline "Out of tactics";
      Incomplete g
  | Some tactic -> (
      match tactic g with
      (* TacticQueue gives the current tactics waiting to be applied *)
      | effect Burn _, k -> continue k ()
      (* Trace is a unified interface for logs and errors *)
      | effect Trace (_, v), k ->
          print_endline v;
          continue k ()
      (* Rank is used to sort terms by an undetermined heuristic *)
      | effect Rank (Term terms), k -> continue k terms
      (* This represents failure for any reason *)
      | effect Fail, _k -> Incomplete g
      (* Choose is used to decide how to explore options *)
      | effect Choose choices, k -> (
          match as_chosen_list choices with
          | [] ->
              print_endline "no choices available";
              Incomplete g
          | c :: _ -> continue k c)
      (* Subgoal is used for branching the proof state *)
      | effect Subgoal g', k -> (
          match prove g' tactic_queue with
          | Complete thm -> continue k thm
          | incomplete -> incomplete)
      (* When a proof is complete we extract the theorem *)
      | thm -> Complete thm)

type pending_proof =
  | PendingProof : (unit -> proof_state) * string list -> pending_proof

let rec prove_bfs_traced g tactic_queue trace_ref =
  match Queue.take_opt tactic_queue with
  | None -> Incomplete g
  | Some tactic ->
      let q : pending_proof Queue.t = Queue.create () in

      let rec handler (f : unit -> proof_state) =
        match f () with
        | effect Burn _, k -> continue k ()
        | effect Trace (Proof, v), k ->
            trace_ref := v :: !trace_ref;
            continue k ()
        | effect Trace (_, v), k ->
            print_endline v;
            continue k ()
        | effect Rank (Term terms), k -> continue k terms
        | effect Fail, _k -> Incomplete g
        | effect Choose choices, k ->
            let r = Multicont.Deep.promote k in
            let snapshot = !trace_ref in
            List.iter
              (fun x ->
                Queue.add
                  (PendingProof ((fun () -> Multicont.Deep.resume r x), snapshot))
                  q)
              (as_chosen_list choices);
            next ()
        | effect Subgoal g', k -> (
            match prove_bfs_traced g' (Queue.copy tactic_queue) trace_ref with
            | Complete thm -> continue k thm
            | incomplete -> incomplete)
        | thm -> thm
      and next () =
        match Queue.take_opt q with
        | None -> Incomplete g
        | Some (PendingProof (thunk, snapshot)) -> (
            trace_ref := snapshot;
            match handler thunk with
            | Complete thm -> Complete thm
            | Incomplete _ -> next ())
      in

      handler (fun () -> Complete (tactic g))

let rec prove_dfs_traced ?(amb = false) g tactic_queue trace_ref =
  match Queue.take_opt tactic_queue with
  | None -> Incomplete g
  | Some tactic ->
      let rec handler (f : unit -> proof_state) =
        match f () with
        | effect Burn _, k -> continue k ()
        | effect Trace (Proof, v), k ->
            trace_ref := v :: !trace_ref;
            continue k ()
        | effect Trace (_, v), k ->
            print_endline v;
            continue k ()
        | effect Rank (Term terms), k -> continue k terms
        | effect Fail, _k -> Incomplete g
        | effect Choose choices, k ->
            let r = Multicont.Deep.promote k in
            let rec try_each = function
              | [] -> Incomplete g
              | c :: cs -> (
                  let snapshot = !trace_ref in
                  let result = handler (fun () -> Multicont.Deep.resume r c) in
                  match result with
                  | Complete thm -> Complete thm
                  | Incomplete _ ->
                      trace_ref := snapshot;
                      try_each cs)
            in
            try_each (as_chosen_list choices)
        | effect Subgoal g', k -> (
            match
              prove_dfs_traced ~amb g' (Queue.copy tactic_queue) trace_ref
            with
            | Complete thm -> continue k thm
            | Incomplete g ->
                (*
                TODO: can probably restructure some things such that
                we keep track of ambient handlers. maybe search handlers
                should always run under an ambient one.

                to run under an ambient handler and make partial progress we need some
                way to know when to backtrack and when to stop
              *)
                if amb then
                  let c = perform @@ Subgoal g in
                  continue k c
                else Incomplete g)
        | thm -> thm
      in
      handler (fun () -> Complete (tactic g))

let prove_bfs g tactic_queue =
  let trace_ref = ref [] in
  prove_bfs_traced g tactic_queue trace_ref

let prove_bfs_with_trace g tactic_queue =
  let trace_ref = ref [] in
  let result = prove_bfs_traced g tactic_queue trace_ref in
  (!trace_ref, result)

let prove_dfs ?(amb = false) g tactic_queue =
  let trace_ref = ref [] in
  prove_dfs_traced ~amb g tactic_queue trace_ref

let prove_dfs_with_trace g tactic_queue =
  let trace_ref = ref [] in
  let result = prove_dfs_traced g tactic_queue trace_ref in
  (!trace_ref, result)

let next_tactic_of_list l =
  let q = Queue.of_seq (List.to_seq l) in
  q

let with_skip_fail : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Fail, _ -> perform (Subgoal goal) | thm -> thm

let with_repeat : tactic_combinator =
 fun tac ->
  let rec aux (asms, concl) =
    match tac (asms, concl) with
    | effect Fail, _ -> perform (Subgoal (asms, concl))
    | effect Subgoal g, k ->
        let r = Multicont.Deep.promote k in
        let thm = aux g in
        (* idk man *)
        Multicont.Deep.resume r thm
    | thm -> thm
  in
  aux

(* this only trys choices at one level, for actual dfs we need a full handler *)
let with_first_success : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose choices, k ->
      let r = Multicont.Deep.promote k in
      let rec try_each = function
        | [] ->
            trace_error "no choices available";
            fail ()
        | c :: cs -> (
            match Multicont.Deep.resume r c with
            | effect Fail, _ -> try_each cs
            | thm -> thm)
      in
      try_each (as_chosen_list choices)
  | v -> v

let with_interactive_choice : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (_, s), k ->
      print_endline s;
      continue k ()
  | effect Choose choices, k ->
      if List.is_empty (as_chosen_list choices) then fail ()
      else
        let rec get_choice cs =
          let idx = read_int () in
          match List.nth_opt cs idx with
          | Some c -> c
          | None ->
              print_endline "Invalid choice";
              get_choice cs
        in
        continue k (get_choice (as_chosen_list choices))
  | v -> v

let with_nth_choice n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose cs, k -> (
      match List.nth_opt (as_chosen_list cs) n with
      | None -> fail ()
      | Some c -> continue k c)
  | v -> v

let with_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term terms), k ->
      if List.mem t terms then continue k t else fail ()
  | x -> x

let with_term_size_ranking : tactic_combinator =
  let rec term_size (t : term) =
    match t with
    | Var (_, _) -> 1
    | Const (_, _) -> 1
    | App (l, r) -> 1 + term_size l + term_size r
    | Lam (bind, bod) -> 1 + term_size bind + term_size bod
  in
  fun tac goal ->
    match tac goal with
    | effect Rank (Term terms), k ->
        let sorted =
          List.stable_sort
            (fun l r -> compare (term_size l) (term_size r))
            terms
        in
        continue k sorted
    | v -> v

let with_fuel_limit limit : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn n, k ->
      limit := !limit - n;
      if !limit <= 0 then discontinue k Out_of_fuel else continue k ()
  | v -> v

let with_fuel_counter r : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn n, k ->
      r := !r + n;
      continue k ()
  | v -> v

let with_no_trace ?(show_proof = false) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, _), k -> continue k ()
  | effect Trace (Debug, _), k -> continue k ()
  | effect Trace (Error, _), k -> continue k ()
  | effect Trace (Warn, _), k -> continue k ()
  | effect Trace (Proof, _), k when not show_proof -> continue k ()
  | v -> v

let with_assumption_rewrites : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with
  | effect Rules (), k -> continue k asm_thms
  | v -> v

let with_rewrites (rewrites : thm list) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules (), k -> continue k rewrites | v -> v

let with_lemmas (lemmas : thm list) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules (), k -> continue k lemmas | v -> v

let with_lemmas_and_assumptions (lemmas : thm list) : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with
  | effect Rules (), k -> continue k (lemmas @ asm_thms)
  | v -> v

let with_rewrites_and_assumptions (rewrites : thm list) : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun asm -> match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with
  | effect Rules (), k -> continue k (rewrites @ asm_thms)
  | v -> v

(* NOTE: 
    if I had some way to evaluate the subgoal complexity, I could have the search handler
    return early when it finds a subgoal within a threshold. This would let me use the handlers
    in a situation where they aren't able to close a goal, but could still make a bunch of progress.

    Maybe I could even get some functionality, like: "I couldn't find a complete proof, but I could solve
    the goal if I had this lemma or rewrite"
 *)

let with_dfs ?(amb = false) ?(tacs = []) : tactic_combinator =
 fun tac goal ->
  let q = Queue.of_seq (List.to_seq (tac :: tacs)) in
  match prove_dfs ~amb goal q with
  | Incomplete _ -> fail ()
  | Complete thm -> thm

let with_bfs ?(tacs = []) : tactic_combinator =
 fun tac goal ->
  let q = Queue.of_seq (List.to_seq (tac :: tacs)) in
  match prove_bfs goal q with Incomplete _ -> fail () | Complete thm -> thm

(*
  simp needs to pull in definition rewrite rules, assumptions rewrites,
  and try to keep applying them while performing beta reduction in between.
  To match lean, it should also try to use refl at the end and close the goal
  if possible
*)
let with_definition_rewrites : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Rules (), k ->
      let ambient_rules = perform @@ Rules () in
      let definitions =
        the_specifications |> Hashtbl.to_seq |> List.of_seq |> List.map snd
      in
      let rules =
        definitions
        |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
        |> List.flatten |> List.append ambient_rules
      in
      continue k rules
  | v -> v

(* TODO: maybe make better sequencing combinators so I don't have to use with_dfs here, something like with_first_success, try, ... *)
let core_simp : tactic =
 fun goal ->
  with_repeat
    (with_dfs ~amb:true
       ~tacs:(wrap_all with_no_trace [ beta_tac; refl_tac ])
       (with_no_trace rewrite_tac))
    goal

let simp_tac ?(with_asms = true) ?(add = []) : tactic =
 fun goal ->
  (* TODO: get the base simp set here. The effect for rules should return proper rules not just unprocessed thms *)
  let definitions =
    the_specifications |> Hashtbl.to_seq |> List.of_seq |> List.map snd
  in
  let rules =
    definitions
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten |> List.append add
  in

  let with_rw =
    if with_asms then with_rewrites_and_assumptions else with_rewrites
  in

  let thm =
    with_repeat
      (with_dfs ~amb:true
         ~tacs:(wrap_all with_no_trace [ beta_tac; refl_tac ])
         (with_no_trace @@ with_rw rules rewrite_tac))
      goal
  in
  thm

(* simp for assumptions - simplifies an assumption using definition rules *)
(* todo; remove the assumption we are currently simplifying from assumptions *)
let simp_asm_tac ?(with_asms = true) ?(add = []) : tactic =
 fun goal ->
  let definitions =
    the_specifications |> Hashtbl.to_seq |> List.of_seq |> List.map snd
  in
  let rules =
    definitions
    |> List.filter_map (fun d -> Result.to_option @@ rules_of_def d)
    |> List.flatten |> List.append add
  in

  let with_rw =
    if with_asms then with_rewrites_and_assumptions else with_rewrites
  in

  let thm =
    with_repeat
      (with_dfs ~amb:true
         ~tacs:(wrap_all with_no_trace [ beta_asm_tac; assumption_tac ])
         (with_no_trace @@ with_rw rules rewrite_asm_tac))
      goal
  in
  thm

let with_fail ~(on_fail : tactic) : tactic_combinator =
 fun tac goal -> match tac goal with effect Fail, _k -> on_fail goal | v -> v

let safe_tacs : tactic =
 fun goal ->
  let tac =
    choose_tactics
    @@ wrap_all with_first_success
         [
           assumption_tac;
           intro_tac;
           neg_intro_tac;
           gen_tac;
           conj_tac;
           elim_conj_asm_tac;
           false_elim_tac;
           mp_asm_tac;
         ]
  in
  tac goal

let test_list =
  [
    assumption_tac;
    intro_tac;
    neg_intro_tac;
    gen_tac;
    conj_tac;
    elim_conj_asm_tac;
    elim_disj_asm_tac;
    false_elim_tac;
    neg_elim_tac;
    apply_asm_tac;
    apply_neg_asm_tac;
    mp_asm_tac;
    left_tac;
    right_tac;
    ccontr_tac;
  ]

let with_search_dfs : tactic_combinator =
 fun tac goal ->
  let rec handler f =
    match f () with
    | effect Choose choices, k ->
        let r = Multicont.Deep.promote k in
        let rec try_each = function
          | [] -> fail ()
          | c :: cs -> (
              match handler (fun () -> Multicont.Deep.resume r c) with
              | effect Fail, _ -> try_each cs
              | thm -> thm)
        in
        try_each (as_chosen_list choices)
    | effect Fail, _ -> fail ()
    | thm -> thm
  in
  handler (fun () -> tac goal)

let rec auto_tac ?(add = []) goal : thm =
  let tacs =
    [
      simp_tac ~with_asms:true ~add;
      gen_tac;
      intro_tac;
      assumption_tac;
      neg_intro_tac;
      conj_tac;
      elim_conj_asm_tac;
      false_elim_tac;
      mp_asm_tac;
    ]
  in

  let handler (f : unit -> thm) : thm =
    match f () with
    | effect Subgoal g, k ->
        if g = goal then fail ()
        else
          let r = Multicont.Deep.promote k in
          let thm = auto_tac g in
          Multicont.Deep.resume r thm
    | thm -> thm
  in
  handler (fun () ->
      let tac = choose_tactics tacs in
      tac goal)

let auto_dfs_tac ?(add = []) = with_search_dfs (auto_tac ~add)

let rec ctauto_tac' goal : thm =
  let handler (f : unit -> thm) : thm =
    match f () with
    | effect Subgoal g, k ->
        let r = Multicont.Deep.promote k in
        let thm = ctauto_tac' g in
        Multicont.Deep.resume r thm
    | thm -> thm
  in
  handler (fun () ->
      let tac = choose_tactics test_list in
      tac goal)

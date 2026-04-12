open Kernel
open Derived
open Printing
open Effect
open Effect.Deep
open Result.Syntax
open Rewrite
open Names
open Fun

type goal = (string * term) list * term [@@deriving show { with_path = false }]

let asm_terms asms = List.map snd asms
let make_goal ?(asms = []) t = (asms, t)

type level = Debug | Info | Warn | Error | Proof | Search

type proof_state = Incomplete of goal | Complete of thm
[@@deriving show { with_path = false }]

type tactic = goal -> thm
type tactic_combinator = tactic -> tactic
type cost = Safe of int | Unsafe of int

type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable

exception Out_of_fuel

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Quiet : bool Effect.t
  | Burn : (string * cost) -> unit Effect.t
  | Rules : thm list Effect.t
  | Name : (term * (string * term) list) -> (string * term) Effect.t

let as_chosen_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Theorem thms -> thms
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let cost_of_tactic (tac : tactic) (goal : goal) =
  match tac goal with
  | effect Burn (name, cost), _k -> (name, cost)
  | _ -> failwith "Burn must be first call of tactic"

let cost_value = function Safe n | Unsafe n -> n
let fail () = perform Fail
let burn name cost = perform (Burn (name, cost))
let trace_dbg a = perform (Trace (Debug, a))
let trace_info a = perform (Trace (Info, a))
let trace_error a = perform (Trace (Error, a))
let trace_proof a = perform (Trace (Proof, a))
let choose_terms gs = perform (Choose (Term gs))
let choose_theorems gs = perform (Choose (Theorem gs))
let choose_tactics gs = perform (Choose (Tactic gs))
let choose_unknowns gs = perform (Choose (Unknown gs))

let return_thm ?(from = "unknown") res =
  let quiet = perform Quiet in
  match res with
  | Ok thm ->
      if quiet then () else perform (Trace (Proof, from));
      thm
  | Error e ->
      if quiet then fail () else trace_error @@ print_error e;
      fail ()

(* Combinators: Sequencing *)

let then_one (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let handled_first = ref false in
  let rec handler f =
    match f () with
    | effect Subgoal g, k when not !handled_first ->
        let r = Multicont.Deep.promote k in
        handled_first := true;
        let thm : thm = tac g in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >> ) = then_one

let then_all (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let rec handler f =
    match f () with
    | effect Subgoal g, k ->
        let r = Multicont.Deep.promote k in
        let thm : thm = tac g in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >>>> ) = then_all

let then_all_direct (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let depth = ref 0 in
  let rec handler f =
    match f () with
    | effect Subgoal g, k when !depth = 0 ->
        let r = Multicont.Deep.promote k in
        incr depth;
        let thm : thm = handler (fun () -> tac g) in
        decr depth;
        handler (fun () -> Multicont.Deep.resume r thm)
    | effect Subgoal g, k when !depth > 0 ->
        (* Re-emit for the outer handler *)
        let r = Multicont.Deep.promote k in
        let thm : thm = perform (Subgoal g) in
        handler (fun () -> Multicont.Deep.resume r thm)
    | v -> v
  in
  handler (fun () -> tac1 goal)

let ( >>> ) = then_all_direct

let then_each (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  fun tac goal ->
    match tac goal with
    | effect Subgoal g, k -> (
        let r = Multicont.Deep.promote k in
        match !tacs with
        | [] ->
            trace_proof "more subgoals than provided tactics";
            fail ()
        | next :: rest ->
            tacs := rest;
            Multicont.Deep.resume r @@ next g)
    | v -> v

let ( >>= ) = Fun.flip then_each

(* Combinators: Choice and Search *)

let with_first : tactic_combinator =
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

let with_first_term : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term choices), k ->
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
      try_each choices
  | v -> v

let with_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Choose (Term _), k -> continue k t | x -> x

(* [cond_tac] is logically part of Choice and Search but is defined later,
   together with [cases_tac], because it depends on it. *)

let try_ : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Fail, _ -> perform (Subgoal goal) | v -> v

let pick_tac (tacs : tactic list) : tactic =
 fun goal ->
  let tac = choose_tactics tacs in
  tac goal

let solve : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Subgoal _g', _k -> fail () | v -> v

let with_repeat : tactic_combinator =
 fun tac goal ->
  let made_progress = ref false in
  let rec aux goal =
    match tac goal with
    | effect Fail, _ ->
        if !made_progress then perform (Subgoal goal) else fail ()
    | effect Subgoal g, _k when g = goal ->
        if !made_progress then perform (Subgoal goal) else fail ()
    | effect Subgoal g, k ->
        made_progress := true;
        continue k (aux g)
    | v -> v
  in
  aux goal

(* Combinators: Interactive and Selection *)

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

let with_nth_term n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term ts), k -> (
      match List.nth_opt ts n with None -> fail () | Some c -> continue k c)
  | v -> v

(* Combinators: Fuel and Tracing *)

let with_fuel_limit limit : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      let n = cost_value cost in
      limit := !limit - n;
      if !limit <= 0 then discontinue k Out_of_fuel
      else (
        burn name cost;
        continue k ())
  | v -> v

let with_fuel_counter r : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Burn (name, cost), k ->
      r := !r + cost_value cost;
      burn name cost;
      continue k ()
  | v -> v

let show_tac : tactic =
 fun goal ->
  print_endline "Current subgoal:";
  fst goal
  |> List.iter (fun (name, asm) ->
      Printf.printf "[%s]:  %s\n" name
        (Printing.pretty_print_hol_term ~pretty:true asm));
  print_endline "-------------------------";
  print_term @@ snd goal;
  fail ()

let with_info_trace : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, t), k ->
      print_endline t;
      continue k ()
  | v -> v

let with_no_automation_trace : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Trace (Search, _), k -> continue k () | v -> v

let with_no_trace ?(show_proof = false) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Trace (Info, _), k -> continue k ()
  | effect Trace (Debug, _), k -> continue k ()
  | effect Trace (Error, _), k -> continue k ()
  | effect Trace (Warn, _), k -> continue k ()
  | effect Trace (Proof, _), k when not show_proof -> continue k ()
  | v -> v

(* Combinators: Rules *)

let with_assumptions : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun (_, asm) ->
        match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with effect Rules, k -> continue k asm_thms | v -> v

let with_rules (rules : thm list) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k rules | v -> v

let with_flip_rules : tactic_combinator =
 fun tac goal ->
  let rules = perform Rules in
  let flipped =
    List.filter_map
      (fun r ->
        let r' =
          let* stripped = strip_forall r in
          sym stripped
        in
        Result.to_option r')
      rules
  in
  match tac goal with effect Rules, k -> continue k flipped | v -> v

let with_rule (rule : thm) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k [ rule ] | v -> v

(* Combinators: Naming *)

let with_names (names : string list) : tactic_combinator =
 fun tac goal ->
  let queue = ref names in
  match tac goal with
  | effect Name (tm, asms), k ->
      let result =
        match !queue with
        | n :: rest ->
            queue := rest;
            (n, tm)
        | [] -> name_asm tm asms
      in
      continue k result
  | v -> v

let with_definition (names : string list) : tactic_combinator =
  let rules =
    names
    |> List.map (fun n ->
        match Rules.get_def n with
        | None ->
            trace_error (Printf.sprintf "Couldn't find def with name %s\n" n);
            fail ()
        | Some rules -> rules)
    |> List.flatten
  in
  fun tac goal ->
    match tac goal with effect Rules, k -> continue k rules | v -> v

let with_specialized ~(name : string) ~(specs : term list) : tactic_combinator =
  let rule =
    match Rules.get_proven name with
    | None ->
        trace_error (Printf.sprintf "Couldn't find rule with name %s\n" name);
        fail ()
    | Some rule -> rule
  in
  let specced =
    let fold_spec =
      List.fold_left
        (fun acc r ->
          let* gen_thm = acc in
          let* step = spec r gen_thm in
          Ok step)
        (Ok rule) specs
    in
    match fold_spec with
    | Error e ->
        trace_error
          (Printf.sprintf "Couldn't specialize rule: %s"
             (Printing.print_error e));
        fail ()
    | Ok thm -> thm
  in
  fun tac goal ->
    match tac goal with effect Rules, k -> continue k [ specced ] | v -> v

let with_proven (names : string list) : tactic_combinator =
  let rules =
    names
    |> List.map @@ fun n ->
       match Rules.get_proven n with
       | None ->
           trace_error (Printf.sprintf "Couldn't find rule with name %s\n" n);
           fail ()
       | Some rule -> rule
  in
  fun tac goal ->
    match tac goal with effect Rules, k -> continue k rules | v -> v

let with_rules_and_assumptions (rules : thm list) : tactic_combinator =
 fun tac (asms, concl) ->
  let asm_thms =
    List.filter_map
      (fun (_, asm) ->
        match assume asm with Ok thm -> Some thm | Error _ -> None)
      asms
  in
  match tac (asms, concl) with
  | effect Rules, k -> continue k (rules @ asm_thms)
  | v -> v

(* Tactics *)

let assumption_tac : tactic =
 fun (asms, concl) ->
  burn "assumption_tac" (Safe 1);
  match List.find_opt (fun (_, tm) -> tm = concl) asms with
  | None ->
      trace_error "assumption doesn't match the goal";
      fail ()
  | Some _ ->
      trace_dbg "Found matching assumption";
      let t = assume concl in
      trace_dbg "Assumption succeeded";
      return_thm ~from:"assumption_tac" t

let truth_tac : tactic =
 fun (_asms, concl) ->
  burn "truth_tac" (Safe 1);
  let t = make_true () in
  if t <> concl then (
    trace_error "goal is not T";
    fail ())
  else truth

let refl_tac : tactic =
 fun (_asms, concl) ->
  burn "refl_tac" (Safe 1);
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

let false_elim_tac : tactic =
 fun (asms, concl) ->
  burn "false_elim_tac" (Safe 1);
  let false_tm = make_false () in
  if List.mem false_tm (List.map snd asms) then
    let thm =
      let* false_thm = assume false_tm in
      let* thy = contr concl false_thm in
      trace_info (Printing.pretty_print_thm thy);
      Ok thy
    in
    return_thm ~from:"false_elim_tac" thm
  else fail ()

let neg_elim_tac : tactic =
 fun (asms, concl) ->
  burn "neg_elim_tac" (Unsafe 3);
  let negs = List.filter is_neg (asm_terms asms) in
  if List.is_empty negs then fail ()
  else
    let thm =
      let chosen_neg = choose_terms negs in
      let* p = term_of_negation chosen_neg in
      if List.mem p (asm_terms asms) then
        let* neg_thm = assume chosen_neg in
        let* p_thm = assume p in
        let* false_thm = not_elim neg_thm in
        let* false_proved = prove_hyp p_thm false_thm in
        contr concl false_proved
      else fail ()
    in
    return_thm ~from:"neg_elim_tac" thm

let sorry_tac : tactic =
 fun (_, conc) ->
  burn "sorry_tac" (Unsafe 1);
  let thm = new_axiom conc in
  return_thm ~from:"sorry_tac" thm

let intro_tac : tactic =
 fun (asms, concl) ->
  burn "intro_tac" (Safe 1);
  let thm =
    let* hyp = side_of_op "==>" Left concl in
    let* conc = side_of_op "==>" Right concl in
    trace_dbg "destruct success";

    let body_thm = perform (Subgoal (name_asm hyp asms :: asms, conc)) in
    let t = disch hyp body_thm in
    trace_dbg "disch success";
    t
  in
  return_thm ~from:"intro_tac" thm

let conj_tac : tactic =
 fun (asms, concl) ->
  burn "conj_tac" (Safe 1);
  let thm =
    let* l, r = destruct_conj concl in
    trace_dbg "Destruct succeeded";

    let lthm = perform (Subgoal (asms, l)) in
    let rthm = perform (Subgoal (asms, r)) in

    let* thm = conj lthm rthm in

    trace_dbg "conj success";
    Ok thm
  in
  return_thm ~from:"conj_tac" thm

let left_tac : tactic =
 fun (asms, concl) ->
  burn "left_tac" (Unsafe 6);
  let thm =
    let* l, r = destruct_disj concl in
    let l_thm = perform (Subgoal (asms, l)) in
    let t = disj_left r l_thm in
    trace_dbg "disj_left success";
    t
  in
  return_thm ~from:"left_tac" thm

let right_tac : tactic =
 fun (asms, concl) ->
  burn "right_tac" (Unsafe 6);
  let thm =
    let* l, r = destruct_disj concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm ~from:"right_tac" thm

let or_tac : tactic =
 fun (asms, concl) ->
  burn "or_tac" (Unsafe 6);
  let tac = choose_tactics [ left_tac; right_tac ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or_tac" thm

let neg_intro_tac : tactic =
 fun (asms, concl) ->
  burn "neg_intro_tac" (Unsafe 4);
  let thm =
    let* p = term_of_negation concl in
    if List.mem p (asm_terms asms) then fail ()
    else
      let f = make_false () in
      let goal' = (name_asm p asms :: asms, f) in
      let sub_thm = perform (Subgoal goal') in
      not_intro p sub_thm
  in
  return_thm ~from:"neg_intro_tac" thm

let elim_conj_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_conj_asm_tac" (Safe 1);
  let conjs = List.filter (fun (_, a) -> is_conj a) asms in
  if List.is_empty conjs then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms conjs) in
      let* l, r = destruct_conj chosen in
      let filtered = List.filter (fun (_, a) -> a <> chosen) asms in
      let add_r = name_asm r filtered :: filtered in
      let asms' = name_asm l add_r :: add_r in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* conj_asm = assume chosen in
      let* l_thm = conj_left conj_asm in
      let* r_thm = conj_right conj_asm in
      let* p_1 = prove_hyp r_thm sub_thm in
      prove_hyp l_thm p_1
    in
    return_thm ~from:"elim_conj_asm_tac" thm

let elim_disj_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_disj_asm_tac" (Unsafe 5);
  let disjs = List.filter (compose is_disj snd) asms in
  if List.is_empty disjs then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms disjs) in
      let* l, r = destruct_disj chosen in
      let asms' = List.filter (fun (_, a) -> a <> chosen) asms in

      let left_goal = (name_asm l asms' :: asms', concl) in
      let right_goal = (name_asm r asms' :: asms', concl) in

      let lthm = perform (Subgoal left_goal) in
      let rthm = perform (Subgoal right_goal) in

      let* disj_asm = assume chosen in
      disj_cases disj_asm lthm rthm
    in
    return_thm ~from:"elim_disj_asm_tac" thm

let elim_exists_asm_tac : tactic =
 fun (asms, concl) ->
  burn "elim_exists_asm_tac" (Safe 2);
  let exists_asms = List.filter (compose is_exists snd) asms in
  if List.is_empty exists_asms then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms exists_asms) in
      let* var, body = destruct_exists chosen in
      let other_asms = List.filter (fun (_, a) -> a <> chosen) asms in
      let avoid =
        all_vars_in concl
        @ (List.map all_vars_in (asm_terms other_asms) |> List.flatten)
      in
      let* var' = variant avoid var in
      let* body' = vsubst [ (var', var) ] body in
      let asms' = name_asm body' other_asms :: other_asms in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* exists_assumed = assume chosen in
      let c = choose var' exists_assumed sub_thm in
      (match c with Ok _ -> trace_info "ok" | Error _ -> trace_info "error");

      trace_info "after choose";
      c
    in
    return_thm ~from:"elim_exists_asm_tac" thm

let ccontr_tac : tactic =
 fun (asms, concl) ->
  burn "ccontr_tac" (Unsafe 10);
  let false_tm = make_false () in
  let neg_concl = make_neg concl in
  if concl = false_tm || List.mem neg_concl (asm_terms asms) then fail ()
  else
    let thm =
      let goal' = (name_asm neg_concl asms :: asms, false_tm) in
      let sub_thm = perform (Subgoal goal') in
      ccontr concl sub_thm
    in
    return_thm ~from:"ccontr_tac" thm

let gen_tac : tactic =
 fun (asms, concl) ->
  burn "gen_tac" (Safe 1);
  let thm =
    let* x, body = destruct_forall concl in
    let* x' = variant (concl :: asm_terms asms) x in
    let* body' = vsubst [ (x', x) ] body in
    let body_thm = perform (Subgoal (asms, body')) in
    gen x' body_thm
  in
  return_thm ~from:"gen_tac" thm

let exists_tac : tactic =
 fun (asms, concl) ->
  burn "exists_tac" (Unsafe 8);
  let thm =
    let* x, body = destruct_exists concl in
    let chosen = choose_terms [] in
    let* chosen_sub_raw = vsubst [ (chosen, x) ] body in
    let* beta_eq = deep_beta chosen_sub_raw in
    let* chosen_sub = rhs beta_eq in
    let body_thm = perform (Subgoal (asms, chosen_sub)) in
    let* thm = exists_p x body chosen body_thm in
    trace_info
      (Printf.sprintf "success with chosen term: %s"
         (pretty_print_hol_term chosen));
    Ok thm
  in
  return_thm ~from:"exists_tac" thm

let spec_asm_tac (tm : term) : tactic =
 fun (asms, concl) ->
  burn "spec_asm_tac" (Unsafe 3);
  let foralls =
    List.filter
      (fun a -> match destruct_forall a with Ok _ -> true | _ -> false)
      (asm_terms asms)
  in
  if List.is_empty foralls then fail ()
  else
    let thm =
      let chosen = choose_terms foralls in
      let* asm_thm = assume chosen in
      let* specialized = spec tm asm_thm in
      let spec_concl = Kernel.concl specialized in
      if List.mem spec_concl (asm_terms asms) then fail ()
      else
        let asms' = name_asm spec_concl asms :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        prove_hyp specialized sub_thm
    in
    return_thm ~from:"spec_asm_tac" thm

let sym_tac : tactic =
 fun (asms, conc) ->
  burn "sym_tac" (Safe 1);
  let thm =
    let* l, r = destruct_eq conc in
    let* flipped = safe_make_eq r l in
    let flip_thm = perform @@ Subgoal (asms, flipped) in
    sym flip_thm
  in
  return_thm ~from:"sym_tac" thm

let sym_asm_tac : tactic =
 fun (asms, concl) ->
  burn "sym_asm_tac" (Safe 2);
  let eqs = List.filter is_eq (asm_terms asms) in
  if List.is_empty eqs then fail ()
  else
    let thm =
      let chosen = choose_terms eqs in
      let* asm_thm = assume chosen in
      let* flipped = sym asm_thm in
      let flipped_concl = Kernel.concl flipped in
      if List.mem flipped_concl (asm_terms asms) then fail ()
      else
        let asms' = name_asm flipped_concl asms :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        prove_hyp flipped sub_thm
    in
    return_thm ~from:"sym_asm_tac" thm

let trans_tac : tactic =
 fun (asms, concl) ->
  burn "trans_tac" (Safe 1);
  let thm =
    let* l, r = destruct_eq concl in
    let s = choose_terms [] in
    let* leq = safe_make_eq l s in
    let* req = safe_make_eq s r in
    let lthm = perform (Subgoal (asms, leq)) in
    let rthm = perform (Subgoal (asms, req)) in
    trans lthm rthm
  in
  return_thm ~from:"trans_tac" thm

let fun_ext_tac : tactic =
 fun (asms, concl) ->
  burn "fun_ext_tac" (Safe 2);
  let thm =
    let* l, r = destruct_eq concl in
    let* l_ty = type_of_term l in
    match l_ty with
    | TyCon ("fun", [ arg_ty; _ ]) ->
        let x = Var ("_ext_x", arg_ty) in
        let* x' = variant (concl :: asm_terms asms) x in
        let l_is_lam, l_body =
          match destruct_lam l with
          | Ok (v, body) -> (true, vsubst [ (x', v) ] body)
          | Error _ -> (false, Ok (App (l, x')))
        in
        let r_is_lam, r_body =
          match destruct_lam r with
          | Ok (v, body) -> (true, vsubst [ (x', v) ] body)
          | Error _ -> (false, Ok (App (r, x')))
        in
        let* l_body = l_body in
        let* r_body = r_body in
        let* body_eq = safe_make_eq l_body r_body in
        let body_thm = perform (Subgoal (asms, body_eq)) in
        let* ext_thm = lam x' body_thm in
        let* ext_thm =
          if l_is_lam then Ok ext_thm
          else
            let* eta_l = eta x' l in
            trans eta_l ext_thm
        in
        if r_is_lam then Ok ext_thm
        else
          let* eta_r = eta x' r in
          let* sym_eta_r = sym eta_r in
          trans ext_thm sym_eta_r
    | _ -> fail ()
  in
  return_thm ~from:"fun_ext_tac" thm

let eq_iff_tac : tactic =
 fun (asms, conc) ->
  burn "eq_iff_tac" (Safe 1);
  let thm =
    let* p, q = destruct_eq conc in
    let* p_ty = type_of_term p in
    if p_ty <> bool_ty then fail ();
    let p_from_q = perform (Subgoal (name_asm q asms :: asms, p)) in
    let q_from_p = perform (Subgoal (name_asm p asms :: asms, q)) in
    deduct_antisym_rule p_from_q q_from_p
  in
  return_thm ~from:"eq_iff_tac" thm

let rewrite_tac : tactic =
 fun (asms, conc) ->
  burn "rewrite_tac" (Unsafe 5);
  let thm =
    let rules = perform Rules in
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

let rewrite_asm_tac : tactic =
 fun (asms, conc) ->
  burn "rewrite_asm_tac" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let chosen_asm = choose_terms (asm_terms asms) in
    (*TODO: Make sure this isn't broken*)
    let chosen_name =
      asms
      |> List.filter (fun (_, a) -> a = chosen_asm)
      |> List.map fst |> List.hd
    in
    (* prevent an assumption from being used as a rule to rewrite itself *)
    if List.mem chosen_asm (hyp chosen_rule) then fail ();

    let* rw_thm = rewrite_once chosen_rule chosen_asm in
    let* _, asm_rewritten = destruct_eq (concl rw_thm) in
    if alphaorder chosen_asm asm_rewritten = 0 then fail ();
    let asms' =
      (chosen_name, asm_rewritten)
      :: List.filter (fun (_, a) -> a <> chosen_asm) asms
    in
    let sub_thm = perform @@ Subgoal (asms', conc) in
    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp rw_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"rewrite_asm_tac" thm

let beta_tac : tactic =
 fun (asms, conc) ->
  burn "beta_tac" (Safe 1);
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
  burn "beta_asm_tac" (Safe 1);
  let thm =
    let chosen_asm = choose_terms (asm_terms asms) in
    (*TODO: Make sure this isn't broken*)
    let chosen_name =
      asms
      |> List.filter (fun (_, a) -> a = chosen_asm)
      |> List.map fst |> List.hd
    in
    let* beta_thm = deep_beta chosen_asm in
    let* _, asm_reduced = destruct_eq (concl beta_thm) in
    if alphaorder chosen_asm asm_reduced = 0 then fail ();

    let asms' =
      (chosen_name, asm_reduced)
      :: List.filter (fun (_, a) -> a <> chosen_asm) asms
    in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp beta_thm asm_thm in
    prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"beta_asm_tac" thm

let eq_true_asm_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_asm_tac" (Safe 2);
  let thm =
    let chosen = choose_terms (asm_terms asms) in
    let* asm_thm = assume chosen in
    let* eq_t = eq_truth_intro asm_thm in
    let new_asm = Kernel.concl eq_t in
    let asms' = name_asm new_asm asms :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    prove_hyp eq_t sub_thm
  in
  return_thm ~from:"eq_true_asm_tac" thm

let eq_true_elim_asm_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_elim_asm_tac" (Safe 2);
  let thm =
    let chosen = choose_terms (asm_terms asms) in
    let* asm_thm = assume chosen in
    let* p = eq_truth_elim asm_thm in
    let new_asm = Kernel.concl p in
    let asms' = name_asm new_asm asms :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    prove_hyp p sub_thm
  in
  return_thm ~from:"eq_true_elim_asm_tac" thm

let eq_true_elim_tac : tactic =
 fun (asms, concl) ->
  burn "eq_true_elim_tac" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, l)) in
    eq_truth_intro elim_thm
  in
  return_thm ~from:"eq_true_elim_tac" thm

let eq_false_elim_tac : tactic =
 fun (asms, concl) ->
  burn "eq_false_elim_tac" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, make_neg l)) in
    eq_false_intro elim_thm
  in
  return_thm ~from:"eq_false_elim_tac" thm

let apply_tac : tactic =
 fun (asms, conc) ->
  burn "apply_tac" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let avoid = conc :: asm_terms asms in
  let thm =
    let* stripped_thm, quant_vars = strip_foralls_acc chosen_thm avoid in
    let premises, final_conc = collect_premises (concl stripped_thm) in
    match Rewrite.match_term final_conc conc with
    | None -> fail ()
    | Some env ->
        let* type_inst = inst_type env.type_sub stripped_thm in
        let term_sub_flipped = List.map (fun (v, t) -> (t, v)) env.term_sub in
        let* inst_thm = inst term_sub_flipped type_inst in
        if
          List.exists
            (fun h -> not (List.mem h (List.map snd asms)))
            (hyp inst_thm)
        then fail ();
        if premises = [] then Ok inst_thm
        else
          let inst_premises, _ = collect_premises (concl inst_thm) in
          let typed_undetermined =
            quant_vars
            |> List.filter (fun v ->
                let v_typed = Rewrite.term_type_subst env.type_sub v in
                not
                  (List.exists
                     (fun (pat, _) -> alphaorder pat v_typed = 0)
                     env.term_sub))
            |> List.map (Rewrite.term_type_subst env.type_sub)
          in
          let subgoal_thms =
            inst_premises
            |> List.map (fun prem ->
                let free_undet =
                  List.filter (fun v -> var_free_in v prem) typed_undetermined
                in
                let subgoal_term = make_foralls free_undet prem in
                let sg_thm = perform (Subgoal (asms, subgoal_term)) in
                if free_undet = [] then sg_thm
                else
                  match specs free_undet sg_thm with
                  | Ok thm -> thm
                  | Error e ->
                      trace_error (print_error e);
                      fail ())
          in
          List.fold_left
            (fun acc sg ->
              let* imp = acc in
              mp imp sg)
            (Ok inst_thm) subgoal_thms
  in
  return_thm ~from:"apply_tac" thm

let apply_asm_tac : tactic =
 fun (asms, conc) ->
  burn "apply_asm_tac" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let chosen_asm = choose_terms (asm_terms asms) in
  let avoid = conc :: asm_terms asms in
  let thm =
    let* stripped_thm, quant_vars = strip_foralls_acc chosen_thm avoid in
    let premises, _final_conc = collect_premises (concl stripped_thm) in
    if premises = [] then fail ();
    let first_premise = List.hd premises in
    match Rewrite.match_term first_premise chosen_asm with
    | None -> fail ()
    | Some env ->
        let* type_inst = inst_type env.type_sub stripped_thm in
        let term_sub_flipped = List.map (fun (v, t) -> (t, v)) env.term_sub in
        let* inst_thm = inst term_sub_flipped type_inst in
        if
          List.exists
            (fun h -> not (List.mem h (List.map snd asms)))
            (hyp inst_thm)
        then fail ();
        let inst_premises, inst_final = collect_premises (concl inst_thm) in
        let remainder =
          if List.length inst_premises = 1 then inst_final
          else make_imps (List.tl inst_premises) inst_final
        in
        let typed_undetermined =
          quant_vars
          |> List.filter (fun v ->
              let v_typed = Rewrite.term_type_subst env.type_sub v in
              not
                (List.exists
                   (fun (pat, _) -> alphaorder pat v_typed = 0)
                   env.term_sub))
          |> List.map (Rewrite.term_type_subst env.type_sub)
        in
        let free_undet =
          List.filter (fun v -> var_free_in v remainder) typed_undetermined
        in
        if List.exists (fun v -> var_free_in v chosen_asm) free_undet then
          fail ();
        let new_asm = make_foralls free_undet remainder in
        if List.mem new_asm (asm_terms asms) then fail ();
        let asms' = name_asm new_asm asms :: asms in
        let sub_thm = perform (Subgoal (asms', conc)) in
        let* asm_thm = assume chosen_asm in
        let* remainder_thm = mp inst_thm asm_thm in
        let* gen_thm = gens (List.rev free_undet) remainder_thm in
        prove_hyp gen_thm sub_thm
  in
  return_thm ~from:"apply_asm_tac" thm

(* This is temporary, with named assumptions I should be able to make a more 
   powerful apply tac which can handle different situations like this by name
   rather than index, potentially looking for the given name in the assumptions,
   and falling back to Rules.proven if it doesn't exist, then calling the
   appropriate tactic based on that. It could have an optional argument for the 
   `to` part of the application. Where if it is supplied it is an assumption
   name to apply to, and if its left out we can apply to the goal.

   On named assumptions. I think I can just add a name to each hyp in the 
   goal type, and when we add an assumption we use a name hint or provided
   optional name. If a tactic replaces an assumption then it should keep the
   name.
 *)
let apply_asm_to_asm_tac ~asm_thm ~asm_to =
  with_nth_choice asm_thm
    (with_nth_term asm_to (with_assumptions apply_asm_tac))

let contradict_asm_tac : tactic =
 fun (asms, concl) ->
  burn "contradict_asm_tac" (Unsafe 5);
  let false_tm = make_false () in
  if concl <> false_tm then fail ()
  else
    let negs = List.filter is_neg (asm_terms asms) in
    if List.is_empty negs then fail ()
    else
      let thm =
        let chosen = choose_terms negs in
        let* p = term_of_negation chosen in
        if List.mem p (asm_terms asms) then fail ()
        else
          let* neg_thm = assume chosen in
          let* elim = not_elim neg_thm in
          let sub_thm = perform (Subgoal (asms, p)) in
          prove_hyp sub_thm elim
      in
      return_thm ~from:"contradict_asm_tac" thm

let discriminate_tac : tactic =
 fun (asms, conc) ->
  burn "discriminate_tac" (Safe 5);
  let equalities =
    asm_terms asms
    |> List.map (fun asm ->
        let* l, _ = destruct_eq asm in
        let* ty = type_of_term l in
        let* ty_name, _ = destruct_type ty in
        let* ind_def =
          Hashtbl.find_opt the_inductives ty_name
          |> Option.to_result ~none:(`TypeNotDeclared ty_name)
        in
        Ok (asm, ind_def.distinct))
    |> List.filter_map Result.to_option
  in
  let try_distinct_tac asm thms =
    with_term asm sym_asm_tac
    >> with_first (with_rules thms rewrite_asm_tac)
    >> false_elim_tac
  in

  let attempts =
    equalities |> List.map @@ fun (asm, thms) -> try_distinct_tac asm thms
  in
  let thm = Ok (with_first (pick_tac attempts) (asms, conc)) in
  return_thm ~from:"discriminate_tac" thm

(* [cases_tac] and [induct_tac] are mutually recursive, and [cond_tac] depends
   on [cases_tac], so they are grouped here. [destruct_tac] is independent but
   included in the [and] chain to preserve mli ordering. *)
let rec cases_tac : tactic =
 fun (asms, concl) ->
  burn "cases_tac" (Unsafe 8);
  let bool_case_branch var bod value asms =
    let* var_eq_val = safe_make_eq var value in
    let* bod_subst = vsubst [ (value, var) ] bod in
    let subgoal_thm =
      perform (Subgoal (name_asm var_eq_val asms :: asms, bod_subst))
    in
    let* pred_lam = make_lam var bod in
    let* var_eq_val_assumed = assume var_eq_val in
    let* val_eq_var = sym var_eq_val_assumed in
    let* lam_eq = mk_comb (refl pred_lam |> Result.get_ok) val_eq_var in
    let* beta_eq = conv_equality deep_beta lam_eq in
    eq_mp beta_eq subgoal_thm
  in
  let bool_forall_cases asms var bod =
    let* bc = spec var bool_cases in
    let* case_t = bool_case_branch var bod (make_true ()) asms in
    let* case_f = bool_case_branch var bod (make_false ()) asms in
    let* result = disj_cases bc case_t case_f in
    gen var result
  in
  let bool_expr_cases asms concl tm =
    let* bc = spec tm bool_cases in
    let* tm_eq_t = safe_make_eq tm (make_true ()) in
    let* tm_eq_f = safe_make_eq tm (make_false ()) in
    let t_thm = perform (Subgoal (name_asm tm_eq_t asms :: asms, concl)) in
    let f_thm = perform (Subgoal (name_asm tm_eq_f asms :: asms, concl)) in
    disj_cases bc t_thm f_thm
  in
  let thm =
    match destruct_forall concl with
    | Ok (var, bod) ->
        let ty = type_of_var var in
        if compare ty bool_ty = 0 then bool_forall_cases asms var bod
        else Ok (induct_tac (asms, concl))
    | Error _ ->
        let tm = perform (Choose (Term [ concl ])) in
        bool_expr_cases asms concl tm
  in
  return_thm ~from:"cases_tac" thm

and destruct_tac : tactic =
 fun (asms, concl) ->
  burn "destruct_tac" (Unsafe 6);
  let thm =
    let tm = choose_terms [] in
    let* ty = type_of_term tm in
    let* ty_name, ty_args = destruct_type ty in
    let ind_def =
      match Hashtbl.find_opt the_inductives ty_name with
      | None ->
          trace_error
            (Printf.sprintf "destruct: %s is not an inductive type" ty_name);
          fail ()
      | Some d -> d
    in
    let* _, def_ty_params = destruct_type ind_def.ty in
    let type_sub = List.combine def_ty_params ty_args in
    let* typed_exhaust = inst_type type_sub ind_def.exhaustiveness in
    let* specced = spec tm typed_exhaust in
    let exhaust_fact = Kernel.concl specced in
    let sub_thm =
      perform (Subgoal (name_asm exhaust_fact asms :: asms, concl))
    in
    prove_hyp specced sub_thm
  in
  return_thm ~from:"destruct_tac" thm

and induct_tac : tactic =
 fun (asms, concl) ->
  burn "induct_tac" (Unsafe 8);
  match destruct_forall concl with
  | Ok _ ->
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
        let cases, _conclusion =
          collect_premises (Kernel.concl inst_induction)
        in
        let solved =
          cases
          |> List.map (fun case ->
              ((asms, case), perform (Subgoal (asms, case))))
        in
        let* result =
          List.fold_left
            (fun acc_thm (_goal, case_thm) ->
              let* acc = acc_thm in
              mp acc case_thm)
            (Ok inst_induction) solved
        in
        Ok result
      in
      return_thm ~from:"induction_tac" thm
  | Error _ ->
      let thm =
        let var = choose_terms [] in
        let mentioning =
          List.filter (fun h -> var_free_in var h) (asm_terms asms)
        in
        let discharged_concl =
          List.fold_left (fun c asm -> make_imp asm c) concl mentioning
        in
        let forall_concl = make_forall var discharged_concl in
        let non_mentioning =
          List.filter (fun (_, h) -> not (var_free_in var h)) asms
        in
        let induct_thm = induct_tac (non_mentioning, forall_concl) in
        let* specced = spec var induct_thm in
        List.fold_left
          (fun acc asm ->
            let* th = acc in
            let* assumed = assume asm in
            mp th assumed)
          (Ok specced) mentioning
      in
      return_thm ~from:"induction_tac" thm

and cond_tac : tactic =
 fun (asms, concl) ->
  let rec collect_cond_args tm acc =
    match tm with
    | App (App (App (Const ("COND", _), b), t), e) ->
        let acc = collect_cond_args b acc in
        let acc = collect_cond_args t acc in
        collect_cond_args e (b :: acc)
    | App (f, x) ->
        let acc = collect_cond_args f acc in
        collect_cond_args x acc
    | Lam (_, body) -> collect_cond_args body acc
    | _ -> acc
  in
  let cond_args = collect_cond_args concl [] in
  match cond_args with
  | [] ->
      trace_error "no COND expressions found in goal";
      fail ()
  | terms ->
      let tm = choose_terms terms in
      with_term tm cases_tac (asms, concl)

let assert_tac : tactic =
 fun (asms, concl) ->
  burn "assert_tac" (Unsafe 5);
  let thm =
    let assertion = choose_terms [] in
    let asserted_thm = perform (Subgoal (asms, assertion)) in
    let with_assertion_thm =
      perform (Subgoal (name_asm assertion asms :: asms, concl))
    in
    prove_hyp asserted_thm with_assertion_thm
  in
  return_thm ~from:"assert_tac" thm

(* Simplification and Automation *)

let intros_tac : tactic =
 fun goal -> with_repeat (with_first (pick_tac [ intro_tac; gen_tac ])) goal

let simp_tac ?(exclude = []) ?(with_asms = true) : tactic =
 fun goal ->
  let add = perform Rules in
  let definitions =
    !Rules.definitions
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let simps =
    !Rules.simps
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let rules =
    definitions |> List.append [ add ] |> List.append simps |> List.flatten
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first
      @@ pick_tac
           [
             with_rw rules rewrite_tac;
             with_repeat beta_tac;
             refl_tac;
             truth_tac;
           ])
      goal
  in
  thm

let auto_tac : tactic =
  pick_tac
    [
      simp_tac ~with_asms:true;
      gen_tac;
      intro_tac;
      truth_tac;
      assumption_tac;
      neg_intro_tac;
      conj_tac;
      elim_conj_asm_tac;
      elim_exists_asm_tac;
      false_elim_tac;
      with_assumptions (with_first_term apply_asm_tac);
    ]

let simp_asm_tac ?(exclude = []) ?(with_asms = true) ?(add = []) : tactic =
 fun goal ->
  let extra = perform Rules in
  let definitions =
    !Rules.definitions
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let simps =
    !Rules.simps
    |> List.filter (fun (n, _) -> not @@ List.mem n exclude)
    |> List.map snd
  in
  let rules =
    definitions |> List.append [ extra ] |> List.append simps
    |> List.append [ add ] |> List.flatten
  in

  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in

  let thm =
    with_repeat
      (with_first
      @@ pick_tac
           [
             with_rw rules rewrite_asm_tac;
             with_repeat beta_asm_tac;
             assumption_tac;
           ])
      goal
  in
  thm

(* Term Synthesis *)

let with_synthetic_term ?(extra = []) (depth : int) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term _), k ->
      let r = Multicont.Deep.promote k in
      let ty = type_of_existential goal |> Result.get_ok in
      let terms = Synth.enumerate ~extra [] ty depth in
      trace_info
        (Printf.sprintf "enumerated %d unique terms" (List.length terms));

      List.iter
        (fun t ->
          trace_dbg (Printf.sprintf "term: %s" (pretty_print_hol_term t)))
        terms;
      let t = choose_terms (List.rev terms) in
      trace_info (Printf.sprintf "chose synth: %s" (pretty_print_hol_term t));
      Multicont.Deep.resume r t
  | v -> v

(* Proof Runner *)

let prove ?(quiet = false) ?(name = "") (goal : goal) (tactic : tactic) =
  match tactic goal with
  (* Burn is used for resource tracking/limiting *)
  | effect Burn _, k -> continue k ()
  (* Rules is used for passing rewrites and lemmas to different tactics *)
  | effect Rules, k -> continue k []
  (* Trace is a unified interface for logs and errors *)
  | effect Trace (_, v), k ->
      print_endline v;
      continue k ()
  (* While trace is used to decide how/when to report our traces, quiet is used
      to keep them from happening in situations where we want maximumm performance *)
  | effect Quiet, k -> continue k quiet
  (* Name is used to name assumptions, defaulting to auto-generation *)
  | effect Name (tm, asms), k -> continue k (name_asm tm asms)
  (* This represents failure for any reason *)
  | effect Fail, _k -> Incomplete goal
  (* Choose is used to decide how to explore options *)
  | effect Choose choices, k -> (
      match as_chosen_list choices with
      | [] ->
          print_endline "no choices available";
          Incomplete goal
      | c :: _ -> continue k c)
  (* Subgoal is used for branching the proof state,
         but prove should solve the goal completely *)
  | effect Subgoal g', _k -> Incomplete g'
  (* When a proof is complete we extract the theorem *)
  | exception Out_of_fuel ->
      print_endline "Out of fuel";
      Incomplete goal
  | thm ->
      Rules.add_proven name thm;
      Complete thm

(* Proof Execution *)

let run_proof ?(pretty = false) ?(notrace = true) ?(name = "") ?(simp = false)
    ?(quiet = false) goal tac =
  let fuel_count = ref 0 in
  let limit = ref 1_000_000 in
  let wrapped =
    (if notrace then with_no_trace ~show_proof:false else Fun.id)
    @@ (with_fuel_limit limit) (with_fuel_counter fuel_count tac)
  in
  match prove ~quiet ~name goal wrapped with
  | Complete thm ->
      if simp then Rules.add_simp name thm;
      if not quiet then (
        print_thm ~pretty thm;
        print_endline "Proof Complete!";
        Printf.printf "with fuel: %d\n" !fuel_count)
  | Incomplete (asms, c) ->
      if not quiet then (
        List.iter (print_term ~pretty) (asm_terms asms);
        print_endline "--------------";
        print_term ~pretty c;
        print_endline "Proof Incomplete";
        Printf.printf "with fuel: %d\n" !fuel_count)

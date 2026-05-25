open Kernel
open Printing
open Effect
open Effect.Deep
open Result.Syntax
open Rewrite
open Fun
module D = Derived

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
exception Cleanup

let cleanup k =
  match discontinue k Cleanup with
  | exception Cleanup -> ()
  | t -> failwith "should fail"

type tactic_info = { name : string; cost : cost; prob : float }

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Quiet : bool Effect.t
  | Register : tactic_info -> unit Effect.t
  | Rules : thm list Effect.t
  | Name : (term * (string * term) list) -> (string * term) Effect.t

let as_chosen_list : type a. a choosable -> a list = function
  | Term ts -> ts
  | Theorem thms -> thms
  | Tactic tacs -> tacs
  | Unknown xs -> xs

let cost_of_tactic (tac : tactic) (goal : goal) =
  match tac goal with
  | effect Register info, k ->
      cleanup k;
      (info.name, info.cost)
  | _ -> failwith "Register must be first call of tactic"

let prob_of_tactic (tac : tactic) (goal : goal) =
  match tac goal with
  | effect Register info, k ->
      cleanup k;
      (info.name, info.prob)
  | _ -> failwith "Register must be first call of tactic"

let default_prob = function Safe _ -> 1.0 | Unsafe _ -> 0.5
let cost_value = function Safe n | Unsafe n -> n
let fail () = perform Fail

let register ?(prob : float option) name cost =
  let prob = match prob with Some p -> p | None -> default_prob cost in
  perform (Register { name; cost; prob })

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
  match tac1 goal with
  | effect Subgoal g, k when not !handled_first ->
      handled_first := true;
      let thm : thm = tac g in
      continue k thm
  | (v : thm) -> v

let ( >> ) = then_one

let then_all (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  match tac1 goal with
  | effect Subgoal g, k ->
      let thm : thm = tac g in
      continue k thm
  | v -> v

let ( @>>> ) = then_all

let then_all_direct (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let depth = ref 0 in
  match tac1 goal with
  | effect Subgoal g, k when !depth = 0 ->
      incr depth;
      let thm : thm = tac g in
      decr depth;
      continue k thm
  | v -> v

let ( @>> ) = then_all_direct

let then_each (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  fun tac goal ->
    match tac goal with
    | effect Subgoal g, k -> (
        match !tacs with
        | [] ->
            trace_proof "more subgoals than provided tactics";
            fail ()
        | next :: rest ->
            tacs := rest;
            continue k @@ next g)
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
            | effect Fail, k ->
                cleanup k;
                try_each cs
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
            | effect Fail, k ->
                cleanup k;
                try_each cs
            | thm -> thm)
      in
      try_each choices
  | v -> v

let all_subterms tm =
  let rec go acc = function
    | [] -> List.rev acc
    | t :: rest ->
        let children =
          match t with
          | Var _ | Const _ -> rest
          | App (f, x) -> f :: x :: rest
          | Lam (_, bod) -> bod :: rest
        in
        go (t :: acc) children
  in
  go [] [ tm ]

let with_term (t : term) : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Choose (Term _), k -> continue k t | x -> x

let with_context_terms : tactic_combinator =
 fun tac goal ->
  let c = snd goal in
  let asms = asm_terms (fst goal) in
  let subterms =
    List.map all_subterms (c :: asms)
    |> List.flatten |> List.sort_uniq compare
    |> List.sort (fun a b -> compare (D.term_size a) (D.term_size b))
  in
  match tac goal with
  | effect Choose (Term _), k ->
      let chosen = choose_terms subterms in
      continue k chosen
  | x -> x

(* [cond] is logically part of Choice and Search but is defined later,
   together with [cases], because it depends on it. *)

let try_ : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Fail, k ->
      cleanup k;
      perform (Subgoal goal)
  | v -> v

let pick (tacs : tactic list) : tactic =
 fun goal ->
  let tac = choose_tactics tacs in
  tac goal

let solve : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Subgoal _g', k ->
      cleanup k;
      fail ()
  | v -> v

let with_repeat : tactic_combinator =
 fun tac goal ->
  let made_progress = ref false in
  let rec aux goal =
    match tac goal with
    | effect Fail, k ->
        cleanup k;
        if !made_progress then perform (Subgoal goal) else fail ()
    | effect Subgoal g, k when g = goal ->
        cleanup k;
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

let with_named_asm_term n : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Choose (Term _ts), k -> (
      match fst goal |> List.find_opt (fun (name, _) -> n = name) with
      | None -> fail ()
      | Some c -> continue k (snd c))
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
  | effect Register info, k ->
      let n = cost_value info.cost in
      limit := !limit - n;
      if !limit <= 0 then discontinue k Out_of_fuel
      else (
        register ~prob:info.prob info.name info.cost;
        continue k ())
  | v -> v

let with_fuel_counter r : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Register info, k ->
      r := !r + cost_value info.cost;
      register ~prob:info.prob info.name info.cost;
      continue k ()
  | v -> v

let show : tactic =
 fun goal ->
  Printing.display_goal ~pretty:true goal;
  perform (Subgoal goal)

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

let with_axioms : tactic_combinator =
 fun tac goal ->
  match tac goal with effect Rules, k -> continue k !the_axioms | v -> v

let with_flip_rules : tactic_combinator =
 fun tac goal ->
  let rules = perform Rules in
  let flipped =
    List.filter_map
      (fun r ->
        let r' =
          let* stripped = strip_forall r in
          D.sym stripped
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
        | [] -> Names.name_asm tm asms
      in
      continue k result
  | v -> v

let with_const_names (name : string) : tactic_combinator =
 fun tac goal ->
  match tac goal with
  | effect Name (tm, asms), k -> continue k (name, tm)
  | v -> v

let ( @: ) tc names = with_names names tc (*TODO: remove*)
let ( /: ) tc names = with_names names tc
let ( @! ) tc name = with_names [ name ] tc (*TODO: remove*)
let ( /! ) tc name = with_names [ name ] tc
let ( /* ) tc name = with_const_names name tc

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
 fun tac goal ->
  let rule =
    match Rules.find_thm name (fst goal) with
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
          let* quant = D.quantifier_of_forall (concl gen_thm) in
          let* quant_ty = type_of_term quant in
          let* r_ty = type_of_term r in
          match type_match [] quant_ty r_ty with
          | None ->
              let* step = D.spec r gen_thm in
              Ok step
          | Some env ->
              let* typed_gen_thm = inst_type env gen_thm in
              let* step = D.spec r typed_gen_thm in
              Ok step)
        (Ok rule) specs
    in
    match fold_spec with
    | Error e ->
        trace_error
          (Printf.sprintf "Couldn't specialize rule: %s"
             (Printing.print_error e));
        fail ()
    | Ok thm ->
        trace_info ((Printf.sprintf "thm: %s\n") (pretty_print_thm thm));
        thm
  in
  match tac goal with effect Rules, k -> continue k [ specced ] | v -> v

let with_proven (names : string list) : tactic_combinator =
 fun tac goal ->
  let rules =
    names
    |> List.map @@ fun n ->
       match Rules.get_proven n with
       | None ->
           trace_error (Printf.sprintf "Couldn't find rule with name %s\n" n);
           fail ()
       | Some rule -> rule
  in
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

let assumption : tactic =
 fun (asms, concl) ->
  register "assumption" (Safe 1);
  match List.find_opt (fun (_, tm) -> tm = concl) asms with
  | None ->
      trace_error "assumption doesn't match the goal";
      fail ()
  | Some _ ->
      trace_dbg "Found matching assumption";
      let t = assume concl in
      trace_dbg "Assumption succeeded";
      return_thm ~from:"assumption" t

let truth : tactic =
 fun (_asms, concl) ->
  register "truth" (Safe 1);
  let t = D.make_true () in
  if t <> concl then (
    trace_error "goal is not T";
    fail ())
  else D.truth

let refl : tactic =
 fun (_asms, concl) ->
  register "refl" (Safe 1);
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
  return_thm ~from:"refl" thm

let false_elim : tactic =
 fun (asms, concl) ->
  register "false_elim" (Safe 1);
  let false_tm = D.make_false () in
  if List.mem false_tm (List.map snd asms) then
    let thm =
      let* false_thm = assume false_tm in
      let* thy = D.contr concl false_thm in
      trace_info (Printing.pretty_print_thm thy);
      Ok thy
    in
    return_thm ~from:"false_elim" thm
  else fail ()

let neg_elim : tactic =
 fun (asms, concl) ->
  register "neg_elim" (Safe 3);
  let negs = List.filter D.is_neg (asm_terms asms) in
  if List.is_empty negs then fail ()
  else
    let thm =
      let chosen_neg = choose_terms negs in
      let* p = D.term_of_negation chosen_neg in
      if List.mem p (asm_terms asms) then
        let* neg_thm = assume chosen_neg in
        let* p_thm = assume p in
        let* false_thm = D.not_elim neg_thm in
        let* false_proved = D.prove_hyp p_thm false_thm in
        D.contr concl false_proved
      else fail ()
    in
    return_thm ~from:"neg_elim" thm

let noop : tactic =
 fun goal ->
  register "noop" (Safe 10);
  let thm = perform (Subgoal goal) in
  return_thm ~from:"noop" (Ok thm)

let sorry : tactic =
 fun (_, conc) ->
  register "sorry" (Unsafe 1);
  let thm = new_axiom conc in
  return_thm ~from:"sorry" thm

let intro : tactic =
 fun (asms, concl) ->
  register "intro" (Safe 1);
  let thm =
    let* hyp = D.side_of_op "==>" Left concl in
    let* conc = D.side_of_op "==>" Right concl in
    trace_dbg "destruct success";

    let body_thm =
      perform (Subgoal (perform (Name (hyp, asms)) :: asms, conc))
    in
    let t = D.disch hyp body_thm in
    trace_dbg "disch success";
    t
  in
  return_thm ~from:"intro" thm

let conj : tactic =
 fun (asms, concl) ->
  register "conj" (Safe 1);
  let thm =
    let* l, r = D.destruct_conj concl in
    trace_dbg "Destruct succeeded";

    let lthm = perform (Subgoal (asms, l)) in
    let rthm = perform (Subgoal (asms, r)) in

    let* thm = D.conj lthm rthm in

    trace_dbg "conj success";
    Ok thm
  in
  return_thm ~from:"conj" thm

let left : tactic =
 fun (asms, concl) ->
  register "left" (Unsafe 6);
  let thm =
    let* l, r = D.destruct_disj concl in
    let l_thm = perform (Subgoal (asms, l)) in
    let t = D.disj_left r l_thm in
    trace_dbg "disj_left success";
    t
  in
  return_thm ~from:"left" thm

let right : tactic =
 fun (asms, concl) ->
  register "right" (Unsafe 6);
  let thm =
    let* l, r = D.destruct_disj concl in
    let r_thm = perform (Subgoal (asms, r)) in
    let t = D.disj_right r_thm l in
    trace_dbg "disj_right success";
    t
  in
  return_thm ~from:"right" thm

let or_ : tactic =
 fun (asms, concl) ->
  register "or" (Unsafe 6);
  let tac = choose_tactics [ left; right ] in
  let thm = Ok (tac (asms, concl)) in
  return_thm ~from:"or" thm

let neg_intro : tactic =
 fun (asms, concl) ->
  register "neg_intro" (Safe 4);
  let thm =
    let* p = D.term_of_negation concl in
    if List.mem p (asm_terms asms) then fail ()
    else
      let f = D.make_false () in
      let goal' = (perform (Name (p, asms)) :: asms, f) in
      let sub_thm = perform (Subgoal goal') in
      D.not_intro p sub_thm
  in
  return_thm ~from:"neg_intro" thm

let elim_conj_asm : tactic =
 fun (asms, concl) ->
  register "elim_conj_asm" (Safe 1);
  let conjs = List.filter (fun (_, a) -> D.is_conj a) asms in
  if List.is_empty conjs then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms conjs) in
      let* l, r = D.destruct_conj chosen in
      let filtered = List.filter (fun (_, a) -> a <> chosen) asms in
      let add_r = perform (Name (r, filtered)) :: filtered in
      let asms' = perform (Name (l, add_r)) :: add_r in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* conj_asm = assume chosen in
      let* l_thm = D.conj_left conj_asm in
      let* r_thm = D.conj_right conj_asm in
      let* p_1 = D.prove_hyp r_thm sub_thm in
      D.prove_hyp l_thm p_1
    in
    return_thm ~from:"elim_conj_asm" thm

let elim_disj_asm : tactic =
 fun (asms, concl) ->
  register "elim_disj_asm" (Safe 5);
  let disjs = List.filter (compose D.is_disj snd) asms in
  if List.is_empty disjs then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms disjs) in
      let* l, r = D.destruct_disj chosen in
      let asms' = List.filter (fun (_, a) -> a <> chosen) asms in

      let left_goal = (perform (Name (l, asms')) :: asms', concl) in
      let right_goal = (perform (Name (r, asms')) :: asms', concl) in

      let lthm = perform (Subgoal left_goal) in
      let rthm = perform (Subgoal right_goal) in

      let* disj_asm = assume chosen in
      D.disj_cases disj_asm lthm rthm
    in
    return_thm ~from:"elim_disj_asm" thm

let elim_exists_asm : tactic =
 fun (asms, concl) ->
  register "elim_exists_asm" (Safe 2);
  let exists_asms = List.filter (compose D.is_exists snd) asms in
  if List.is_empty exists_asms then fail ()
  else
    let thm =
      let chosen = choose_terms (asm_terms exists_asms) in
      let* var, body = D.destruct_exists chosen in
      let other_asms = List.filter (fun (_, a) -> a <> chosen) asms in
      let avoid =
        D.all_vars_in concl
        @ (List.map D.all_vars_in (asm_terms other_asms) |> List.flatten)
      in
      let* var' = variant avoid var in
      let* body' = vsubst [ (var', var) ] body in
      let asms' = perform (Name (body', other_asms)) :: other_asms in
      let sub_thm = perform (Subgoal (asms', concl)) in
      let* exists_assumed = assume chosen in
      let c = D.choose var' exists_assumed sub_thm in
      (match c with Ok _ -> trace_info "ok" | Error _ -> trace_info "error");

      trace_info "after choose";
      c
    in
    return_thm ~from:"elim_exists_asm" thm

let ccontr : tactic =
 fun (asms, concl) ->
  register ~prob:0.01 "ccontr" (Unsafe 10);
  let false_tm = D.make_false () in
  let neg_concl = D.make_neg concl in
  if concl = false_tm || List.mem neg_concl (asm_terms asms) then fail ()
  else
    let thm =
      let goal' = (perform (Name (neg_concl, asms)) :: asms, false_tm) in
      let sub_thm = perform (Subgoal goal') in
      D.ccontr concl sub_thm
    in
    return_thm ~from:"ccontr" thm

let gen : tactic =
 fun (asms, concl) ->
  register "gen" (Safe 1);
  let thm =
    let* x, body = D.destruct_forall concl in
    let* x' = variant (concl :: asm_terms asms) x in
    let* body' = vsubst [ (x', x) ] body in
    let body_thm = perform (Subgoal (asms, body')) in
    D.gen x' body_thm
  in
  return_thm ~from:"gen" thm

let generalize (x : term) : tactic =
 fun (asms, concl) ->
  register "generalize" (Safe 1);
  let thm =
    if List.exists (var_free_in x) (asm_terms asms) then fail ()
    else
      let gen_concl = D.make_forall x concl in
      let gen_thm = perform (Subgoal (asms, gen_concl)) in
      D.spec x gen_thm
  in
  return_thm ~from:"generalize" thm

let exists : tactic =
 fun (asms, concl) ->
  register ~prob:0.3 "exists" (Unsafe 8);
  let thm =
    let* x, body = D.destruct_exists concl in
    let chosen = choose_terms [] in
    let* chosen_sub_raw = vsubst [ (chosen, x) ] body in
    let* beta_eq = D.deep_beta chosen_sub_raw in
    let* chosen_sub = D.rhs beta_eq in
    let body_thm = perform (Subgoal (asms, chosen_sub)) in
    let* thm = D.exists_p x body chosen body_thm in
    trace_info
      (Printf.sprintf "success with chosen term: %s"
         (pretty_print_hol_term chosen));
    Ok thm
  in
  return_thm ~from:"exists" thm

let spec_asm (tm : term) : tactic =
 fun (asms, concl) ->
  register ~prob:0.4 "spec_asm" (Unsafe 3);
  let foralls =
    List.filter
      (fun a -> match D.destruct_forall a with Ok _ -> true | _ -> false)
      (asm_terms asms)
  in
  if List.is_empty foralls then fail ()
  else
    let thm =
      let chosen = choose_terms foralls in
      let* asm_thm = assume chosen in
      let* specialized = D.spec tm asm_thm in
      let spec_concl = Kernel.concl specialized in
      if List.mem spec_concl (asm_terms asms) then fail ()
      else
        let asms' = perform (Name (spec_concl, asms)) :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        D.prove_hyp specialized sub_thm
    in
    return_thm ~from:"spec_asm" thm

let sym : tactic =
 fun (asms, conc) ->
  register ~prob:0.7 "sym" (Safe 1);
  let thm =
    let* l, r = destruct_eq conc in
    let* flipped = safe_make_eq r l in
    let flip_thm = perform @@ Subgoal (asms, flipped) in
    D.sym flip_thm
  in
  return_thm ~from:"sym" thm

let sym_asm : tactic =
 fun (asms, concl) ->
  register ~prob:0.7 "sym_asm" (Safe 2);
  let eqs = List.filter D.is_eq (asm_terms asms) in
  if List.is_empty eqs then fail ()
  else
    let thm =
      let chosen = choose_terms eqs in
      let* asm_thm = assume chosen in
      let* flipped = D.sym asm_thm in
      let flipped_concl = Kernel.concl flipped in
      if List.mem flipped_concl (asm_terms asms) then fail ()
      else
        let asms' = perform (Name (flipped_concl, asms)) :: asms in
        let sub_thm = perform (Subgoal (asms', concl)) in
        D.prove_hyp flipped sub_thm
    in
    return_thm ~from:"sym_asm" thm

let trans : tactic =
 fun (asms, concl) ->
  register ~prob:0.5 "trans" (Safe 1);
  let thm =
    let* l, r = destruct_eq concl in
    let s = choose_terms [] in
    let* leq = safe_make_eq l s in
    let* req = safe_make_eq s r in
    let lthm = perform (Subgoal (asms, leq)) in
    let rthm = perform (Subgoal (asms, req)) in
    trans lthm rthm
  in
  return_thm ~from:"trans" thm

let fun_ext : tactic =
 fun (asms, concl) ->
  register "fun_ext" (Safe 2);
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
            let* eta_l = D.eta x' l in
            Kernel.trans eta_l ext_thm
        in
        if r_is_lam then Ok ext_thm
        else
          let* eta_r = D.eta x' r in
          let* sym_eta_r = D.sym eta_r in
          Kernel.trans ext_thm sym_eta_r
    | _ -> fail ()
  in
  return_thm ~from:"fun_ext" thm

let eq_iff : tactic =
 fun (asms, conc) ->
  register "eq_iff" (Safe 1);
  let thm =
    let* p, q = destruct_eq conc in
    let* p_ty = type_of_term p in
    if p_ty <> bool_ty then fail ();
    let p_from_q = perform (Subgoal (perform (Name (q, asms)) :: asms, p)) in
    let q_from_p = perform (Subgoal (perform (Name (p, asms)) :: asms, q)) in
    deduct_antisym_rule p_from_q q_from_p
  in
  return_thm ~from:"eq_iff" thm

let rewrite ?position : tactic =
 fun (asms, conc) ->
  register ~prob:0.6 "rewrite" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in

    let* rw_thm =
      match position with
      | None -> rewrite_once chosen_rule conc
      | Some idx -> (
          (*pick which position to rewrite in*)
          let* lhs, _ = destruct_eq (concl chosen_rule) in
          let subterms = all_subterms conc in
          let matches =
            List.filter (fun t -> match_term lhs t |> Option.is_some) subterms
          in
          let chosen_position = List.nth_opt matches idx in
          match chosen_position with
          | None ->
              trace_error "target index out of bounds";
              fail ()
          | Some target ->
              (* print_term target; *)
              rewrite_once ~target chosen_rule conc)
    in
    let* _, conc_rewritten = destruct_eq (concl rw_thm) in

    (* Fail if no progress was made *)
    if alphaorder conc conc_rewritten = 0 then fail ();

    let subthm = perform @@ Subgoal (asms, conc_rewritten) in
    let* rw_sym = D.sym rw_thm in
    eq_mp rw_sym subthm
  in
  return_thm ~from:"rewrite" thm

let show_rewrite_positions : tactic =
 fun (_, conc) ->
  register "show_rewrite_positions" (Safe 1);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let* lhs, _ = destruct_eq (concl chosen_rule) in
    let subterms = all_subterms conc in
    let matches =
      List.filter (fun t -> match_term lhs t |> Option.is_some) subterms
    in
    List.iter (fun t -> trace_info (pretty_print_hol_term t)) matches;
    (* List.iter (fun t -> trace_info (pretty_print_hol_term t)) subterms; *)
    let _ = matches in
    fail ()
  in
  return_thm ~from:"show_rewrite_positions" thm

let rewrite_asm : tactic =
 fun (asms, conc) ->
  register ~prob:0.6 "rewrite_asm" (Unsafe 5);
  let thm =
    let rules = perform Rules in
    let* chosen_rule = strip_forall (choose_theorems rules) in
    let chosen_asm = choose_terms (asm_terms asms) in
    let chosen_name =
      match List.find_opt (fun (_, a) -> alphaorder a chosen_asm = 0) asms with
      | Some (name, _) -> name
      | None -> fail ()
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
    D.prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"rewrite_asm" thm

let beta : tactic =
 fun (asms, conc) ->
  register "beta" (Safe 1);
  let thm =
    let* beta_thm = D.deep_beta conc in
    let* _, conc_reduced = destruct_eq (concl beta_thm) in
    let subthm = perform @@ Subgoal (asms, conc_reduced) in
    let* beta_sym = D.sym beta_thm in
    eq_mp beta_sym subthm
  in
  return_thm ~from:"beta" thm

let beta_asm : tactic =
 fun (asms, conc) ->
  register "beta_asm" (Safe 1);
  let thm =
    let chosen_asm = choose_terms (asm_terms asms) in
    let chosen_name =
      match List.find_opt (fun (_, a) -> alphaorder a chosen_asm = 0) asms with
      | Some (name, _) -> name
      | None -> fail ()
    in
    let* beta_thm = D.deep_beta chosen_asm in
    let* _, asm_reduced = destruct_eq (concl beta_thm) in
    if alphaorder chosen_asm asm_reduced = 0 then fail ();

    let asms' =
      (chosen_name, asm_reduced)
      :: List.filter (fun (_, a) -> a <> chosen_asm) asms
    in
    let sub_thm = perform @@ Subgoal (asms', conc) in

    let* asm_thm = assume chosen_asm in
    let* new_asm_thm = eq_mp beta_thm asm_thm in
    D.prove_hyp new_asm_thm sub_thm
  in
  return_thm ~from:"beta_asm" thm

let eq_true_asm : tactic =
 fun (asms, concl) ->
  register "eq_true_asm" (Safe 2);
  let thm =
    let chosen = choose_terms (asm_terms asms) in
    let* asm_thm = assume chosen in
    let* eq_t = D.eq_truth_intro asm_thm in
    let new_asm = Kernel.concl eq_t in
    let asms' = perform (Name (new_asm, asms)) :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    D.prove_hyp eq_t sub_thm
  in
  return_thm ~from:"eq_true_asm" thm

let eq_true_elim_asm : tactic =
 fun (asms, concl) ->
  register "eq_true_elim_asm" (Safe 2);
  let thm =
    let chosen = choose_terms (asm_terms asms) in
    let* asm_thm = assume chosen in
    let* p = D.eq_truth_elim asm_thm in
    let new_asm = Kernel.concl p in
    let asms' = perform (Name (new_asm, asms)) :: asms in
    let sub_thm = perform (Subgoal (asms', concl)) in
    D.prove_hyp p sub_thm
  in
  return_thm ~from:"eq_true_elim_asm" thm

let eq_true_elim : tactic =
 fun (asms, concl) ->
  register "eq_true_elim" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, l)) in
    D.eq_truth_intro elim_thm
  in
  return_thm ~from:"eq_true_elim" thm

let eq_false_elim : tactic =
 fun (asms, concl) ->
  register "eq_false_elim" (Safe 2);
  let thm =
    let* l, _r = destruct_eq concl in
    let elim_thm = perform (Subgoal (asms, D.make_neg l)) in
    D.eq_false_intro elim_thm
  in
  return_thm ~from:"eq_false_elim" thm

let exact : tactic =
 fun (_, conc) ->
  register "exact" (Safe 2);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let order = alphaorder conc (concl chosen_thm) in
  let thm = if order = 0 then chosen_thm else fail () in
  return_thm ~from:"exact" (Ok thm)

let apply : tactic =
 fun (asms, conc) ->
  register ~prob:0.65 "apply" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let avoid = conc :: asm_terms asms in
  let thm =
    let* stripped_thm, quant_vars = D.strip_foralls_acc chosen_thm avoid in
    let premises, final_conc = D.collect_premises (concl stripped_thm) in
    match Rewrite.match_term final_conc conc with
    | None ->
        trace_info
          (Printf.sprintf "couldn't match: \n%s\nwith:\n%s\n"
             (pretty_print_hol_term final_conc)
             (pretty_print_hol_term conc));
        fail ()
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
          let inst_premises, _ = D.collect_premises (concl inst_thm) in
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
                let subgoal_term = D.make_foralls free_undet prem in
                let sg_thm = perform (Subgoal (asms, subgoal_term)) in
                if free_undet = [] then sg_thm
                else
                  match D.specs free_undet sg_thm with
                  | Ok thm -> thm
                  | Error e ->
                      trace_error (print_error e);
                      fail ())
          in
          List.fold_left
            (fun acc sg ->
              let* imp = acc in
              D.mp imp sg)
            (Ok inst_thm) subgoal_thms
  in
  return_thm ~from:"apply" thm

let apply_asm : tactic =
 fun (asms, conc) ->
  register ~prob:0.65 "apply_asm" (Unsafe 5);
  let lemmas = perform Rules in
  let chosen_thm = choose_theorems lemmas in
  let chosen_asm = choose_terms (asm_terms asms) in
  let avoid = conc :: asm_terms asms in
  let thm =
    let* stripped_thm, quant_vars = D.strip_foralls_acc chosen_thm avoid in
    let premises, _final_conc = D.collect_premises (concl stripped_thm) in
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
        let inst_premises, inst_final = D.collect_premises (concl inst_thm) in
        let remainder =
          if List.length inst_premises = 1 then inst_final
          else D.make_imps (List.tl inst_premises) inst_final
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
        let new_asm = D.make_foralls free_undet remainder in
        if List.mem new_asm (asm_terms asms) then fail ();
        let asms' = perform (Name (new_asm, asms)) :: asms in
        let sub_thm = perform (Subgoal (asms', conc)) in
        let* asm_thm = assume chosen_asm in
        let* remainder_thm = D.mp inst_thm asm_thm in
        let* gen_thm = D.gens (List.rev free_undet) remainder_thm in
        D.prove_hyp gen_thm sub_thm
  in
  return_thm ~from:"apply_asm" thm

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
let apply_asm_to_asm ~asm_thm ~asm_to =
  with_nth_choice asm_thm (with_nth_term asm_to (with_assumptions apply_asm))

(* Take a thm, from (in order of precedence) 
   1. A named assumption (will fail if name is auto generated
   2. A proven lemma or theorem
   3. A definition
   and apply it to [target], where target is the goal by default, but if provided will look up a named assumption
   *)
let apply_at (source : string) ?target =
 fun goal ->
  let found = Rules.find_thm source (fst goal) in
  if Option.is_none found then fail ();
  let thm = Option.get found in
  match target with
  | None -> (with_rule thm apply) goal
  | Some name -> (with_named_asm_term name (with_rule thm apply_asm)) goal

let rewrite_at (source : string) ?target ?position =
 fun goal ->
  let found = Rules.find_thms source (fst goal) in
  if Option.is_none found then fail ();
  let thms = Option.get found in
  match target with
  | None -> (with_rules thms (rewrite ?position)) goal
  | Some name -> (with_named_asm_term name (with_rules thms rewrite_asm)) goal

let with_named_rule names : tactic_combinator =
 fun tac goal ->
  let rules =
    names
    |> List.map (fun n ->
        match Rules.find_thms n (fst goal) with
        | None ->
            trace_error (Printf.sprintf "Couldn't find def with name %s\n" n);
            fail ()
        | Some rules -> rules)
    |> List.flatten
  in
  match tac goal with effect Rules, k -> continue k rules | v -> v

let contradict_asm : tactic =
 fun (asms, concl) ->
  register "contradict_asm" (Safe 5);
  let false_tm = D.make_false () in
  if concl <> false_tm then fail ()
  else
    let negs = List.filter D.is_neg (asm_terms asms) in
    if List.is_empty negs then fail ()
    else
      let thm =
        let chosen = choose_terms negs in
        let* p = D.term_of_negation chosen in
        if List.mem p (asm_terms asms) then fail ()
        else
          let* neg_thm = assume chosen in
          let* elim = D.not_elim neg_thm in
          let sub_thm = perform (Subgoal (asms, p)) in
          D.prove_hyp sub_thm elim
      in
      return_thm ~from:"contradict_asm" thm

let discriminate : tactic =
 fun (asms, conc) ->
  register "discriminate" (Safe 5);
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
  let try_distinct asm thms =
    with_term asm sym_asm
    >> with_first (with_rules thms rewrite_asm)
    >> false_elim
  in

  let attempts =
    equalities |> List.map @@ fun (asm, thms) -> try_distinct asm thms
  in
  let thm = Ok (with_first (pick attempts) (asms, conc)) in
  return_thm ~from:"discriminate" thm

let destruct : tactic =
 fun (asms, concl) ->
  register ~prob:0.35 "destruct" (Unsafe 6);
  let thm =
    let tm = choose_terms [] in
    let* ty = type_of_term tm in
    let* ty_name, ty_args = destruct_type ty in
    let* exhaustiveness =
      if ty = bool_ty then Ok Derived.bool_cases
      else
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
        inst_type type_sub ind_def.exhaustiveness
    in

    let* specced = D.spec tm exhaustiveness in
    let exhaust_fact = Kernel.concl specced in

    let sub_thm =
      perform (Subgoal (perform (Name (exhaust_fact, asms)) :: asms, concl))
    in
    D.prove_hyp specced sub_thm
  in
  return_thm ~from:"destruct" thm

let rec induct : tactic =
 fun (asms, concl) ->
  register ~prob:0.3 "induct" (Unsafe 8);
  match D.destruct_forall concl with
  | Ok _ ->
      let thm =
        let* induction_var, bod = D.destruct_forall concl in
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
        let* inst_induction = D.spec p typed_induction in
        let cases, _conclusion =
          D.collect_premises (Kernel.concl inst_induction)
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
              D.mp acc case_thm)
            (Ok inst_induction) solved
        in
        Ok result
      in
      return_thm ~from:"induction" thm
  | Error _ ->
      let thm =
        let var = choose_terms [] in
        let mentioning =
          List.filter (fun h -> var_free_in var h) (asm_terms asms)
        in
        let discharged_concl =
          List.fold_left (fun c asm -> D.make_imp asm c) concl mentioning
        in
        let forall_concl = D.make_forall var discharged_concl in
        let non_mentioning =
          List.filter (fun (_, h) -> not (var_free_in var h)) asms
        in
        let induct_thm = induct (non_mentioning, forall_concl) in
        let* specced = D.spec var induct_thm in
        List.fold_left
          (fun acc asm ->
            let* th = acc in
            let* assumed = assume asm in
            D.mp th assumed)
          (Ok specced) mentioning
      in
      return_thm ~from:"induction" thm

let have : tactic =
 fun (asms, concl) ->
  register ~prob:0.2 "have" (Unsafe 5);
  let thm =
    let assertion = choose_terms [] in
    let asserted_thm = perform (Subgoal (asms, assertion)) in
    let with_assertion_thm =
      perform (Subgoal (perform (Name (assertion, asms)) :: asms, concl))
    in
    D.prove_hyp asserted_thm with_assertion_thm
  in
  return_thm ~from:"have" thm

let have_premise : tactic =
 fun (asms, concl) ->
  register ~prob:0.2 "have_premise" (Unsafe 5);
  let thm =
    let imps = asms |> List.filter (compose D.is_imp snd) in
    let chosen_imp = choose_terms (asm_terms imps) in
    let* prem, _ = D.destruct_imp chosen_imp in
    Ok (with_term prem have (asms, concl))
  in
  return_thm ~from:"have_premise" thm

(* Simplification and Automation *)

let intros : tactic =
 fun goal -> with_repeat (with_first (pick [ intro; gen ])) goal

let simp_only ?(with_asms = true) : tactic =
 fun goal ->
  register "simp" (Safe 1);
  let rules = perform Rules in
  let with_rw = if with_asms then with_rules_and_assumptions else with_rules in
  let thm =
    with_repeat
      (with_first
      @@ pick [ with_rw rules rewrite; with_repeat beta; refl; truth ])
      goal
  in
  thm

let simp ?(exclude = []) ?(with_asms = true) : tactic =
 fun goal ->
  register "simp" (Safe 1);
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
  (with_rules rules @@ simp_only ~with_asms) goal

let auto : tactic =
  pick
    [
      simp ~with_asms:true;
      gen;
      intro;
      truth;
      assumption;
      neg_intro;
      conj;
      elim_conj_asm;
      elim_exists_asm;
      false_elim;
      with_assumptions (with_first_term apply_asm);
    ]

let simp_asm ?(exclude = []) ?(with_asms = true) ?(add = []) : tactic =
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
      @@ pick [ with_rw rules rewrite_asm; with_repeat beta_asm; assumption ])
      goal
  in
  thm

(* Term Synthesis *)

let with_synthetic_term ?(extra = []) (depth : int) : tactic_combinator =
  let terms = Hashtbl.create 1024 in
  fun tac goal ->
    match tac goal with
    | effect Choose (Term _), k ->
        let r = Multicont.Deep.promote k in
        let ty = D.type_of_existential goal |> Result.get_ok in
        let terms =
          match Hashtbl.find_opt terms (ty, depth) with
          | None ->
              let tms = Synth.enumerate ~extra [] ty depth in
              Hashtbl.add terms (ty, depth) tms;
              trace_info
                (Printf.sprintf "enumerated %d unique terms" (List.length tms));
              tms
          | Some tms -> tms
        in

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
  (* Register is used for tracking data about tactics during runtime *)
  | effect Register _, k -> continue k ()
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
  | effect Name (tm, asms), k -> continue k (Names.name_asm tm asms)
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
  | Incomplete g -> Printing.display_goal g

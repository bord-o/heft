open Kernel
open Derived
open Effect
open Effect.Deep
open Multicont.Deep
open Tactic

type choice_kind =
  | CTerm of (goal * term)
  | CTheorem of goal * thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal

(* let is_ctactic = function CTactic _ -> true | _ -> false *)

type search_metadata = MSubgoal of goal | MChoice of choice_kind | MResume

type step_result =
  | Cont of (choice_kind * (unit -> step_result)) list
  | Need of goal * (thm -> step_result)
  | Done of thm
  | Dead

type cancel_token = { mutable cancelled : bool }

let fresh_token () = { cancelled = false }
let cancel token = token.cancelled <- true

module Priority = struct
  type t =
    search_metadata
    * (unit -> step_result)
    * (thm -> step_result) list
    * string list
    * cancel_token

  let compare : t -> t -> int =
   fun (a, _, _, _, _) (b, _, _, _, _) ->
    match (a, b) with
    | MSubgoal _, MResume -> 1
    | MSubgoal _, MChoice _ -> 1
    | MResume, MChoice _ -> 1
    | MChoice m1, MChoice m2 -> (
        match (m1, m2) with
        | CTerm (_, t1), CTerm (_, t2) ->
            let s1, s2 = (term_size t1, term_size t2) in
            compare s2 s1
        | CTactic (_, c1, _), CTactic (_, c2, _) -> (
            match (c1, c2) with
            | Safe _, Unsafe _ -> 1
            | Unsafe _, Safe _ -> -1
            | Safe n, Safe m -> compare m n
            | Unsafe n, Unsafe m -> compare m n)
        | _ -> 0)
    | _ -> 0
end

module PriorityQueue = Pqueue.MakeMax (Priority)

module type Frontier = sig
  type t

  val create : unit -> t
  val pop : t -> Priority.t option
  val add : t -> Priority.t -> unit
  val stats : t -> string
end

let step (tac : tactic) (goal : goal) : step_result =
  match tac goal with
  | effect Choose cs, k ->
      let r = promote k in
      let choosable = as_chosen_list cs |> List.map (fun c () -> resume r c) in
      let real_choices =
        match cs with
        | Term ts ->
            List.combine (ts |> List.map @@ fun t -> CTerm (goal, t)) choosable
        | Theorem ts ->
            List.combine
              (ts |> List.map @@ fun t -> CTheorem (goal, t))
              choosable
        | Tactic ts ->
            List.combine
              (ts
              |> List.map @@ fun t ->
                 let _, cost = cost_of_tactic t goal in
                 CTactic (goal, cost, t))
              choosable
        | Unknown _ ->
            List.combine
              (List.init (List.length choosable) (fun _ -> CUnknown goal))
              choosable
      in
      Cont real_choices
  | effect Subgoal g, k ->
      let r = promote k in
      Need (g, fun (v : thm) -> resume r v)
  | effect Fail, k ->
      cleanup k;
      Dead
  | v -> Done v

let run_thunk_with_path (path : string list ref) (thunk : unit -> 'a) : 'a =
  let rec loop f =
    match f () with
    | effect Trace (Proof, name), k ->
        path := name :: !path;
        loop (fun () -> continue k ())
    | v -> v
  in
  loop thunk

let emit_proof_path (path : string list) : unit =
  let rec format_path = function
    | [] -> ""
    | [ last ] -> "  " ^ last
    | t :: rest -> "  " ^ t ^ " >>\n" ^ format_path rest
  in
  let proof_str = "Proof:\n" ^ format_path path in
  perform (Trace (Search, proof_str))

let stats_of_list l =
  List.fold_left
    (fun (sub, choice, res) (e, _, _, _, _) ->
      match e with
      | MResume -> (sub, choice, res + 1)
      | MSubgoal _ -> (sub + 1, choice, res)
      | MChoice _ -> (sub, choice + 1, res))
    (0, 0, 0) l
  |> fun (s, c, r) ->
  Printf.sprintf "Subgoals: %d | Choices: %d | Resumptions: %d\n" s c r

module StackFrontier : Frontier = struct
  type t = Priority.t Stack.t

  let create () = Stack.create ()
  let pop = Stack.pop_opt
  let add s x = Stack.push x s
  let stats (s : t) = s |> Stack.to_seq |> List.of_seq |> stats_of_list
end

let make_search (module F : Frontier) : tactic_combinator =
 fun tac goal ->
  let s = F.create () in
  let root_token = fresh_token () in
  F.add s (MSubgoal goal, (fun () -> step tac goal), [], [], root_token);
  let rec aux () =
    trace_info (F.stats s);
    (* print_endline (F.stats s); *)
    match F.pop s with
    | None -> fail ()
    | Some (_, _, _, _, token) when token.cancelled -> aux ()
    | Some (_, thunk, parents, path, token) -> (
        let current_path = ref path in
        match run_thunk_with_path current_path thunk with
        | Done v -> (
            match parents with
            | [] ->
                emit_proof_path !current_path;
                v
            | resume :: rest ->
                (* This subgoal is solved — cancel all sibling entries *)
                cancel token;
                let new_token = fresh_token () in
                F.add s
                  (MResume, (fun () -> resume v), rest, !current_path, new_token);
                aux ())
        | Need (g, resume) ->
            (* New subgoal gets a fresh token; entries spawned during its
               exploration will inherit it and be cancelled when it's solved *)
            let subgoal_token = fresh_token () in
            F.add s
              ( MSubgoal g,
                (fun () -> step tac g),
                resume :: parents,
                !current_path,
                subgoal_token );
            aux ()
        | Dead -> aux ()
        | Cont thunks ->
            (* Choices inherit the current token — they're siblings exploring
               the same subgoal *)
            thunks |> List.rev
            |> List.iter (fun (m, t) ->
                F.add s (MChoice m, t, parents, !current_path, token));
            aux ())
  in
  aux ()

let with_dfs : tactic_combinator = make_search (module StackFrontier)

module PQueueFrontier : Frontier = struct
  type t = PriorityQueue.t

  let create = PriorityQueue.create
  let pop = PriorityQueue.pop_max
  let add q x = PriorityQueue.add q x

  let stats (s : t) =
    s
    |> PriorityQueue.fold_unordered (fun acc a -> a :: acc) []
    |> stats_of_list
end

let with_best_first : tactic_combinator = make_search (module PQueueFrontier)

module QueueFrontier : Frontier = struct
  type t = Priority.t Queue.t

  let create () = Queue.create ()
  let pop = Queue.take_opt
  let add q x = Queue.add x q
  let stats (s : t) = s |> Queue.to_seq |> List.of_seq |> stats_of_list
end

let with_bfs : tactic_combinator = make_search (module QueueFrontier)

let with_dfs'' : tactic_combinator =
 fun tac goal ->
  let rec handler s f =
    match f () with
    | effect Choose choices, k ->
        let r = promote k in
        (choices |> as_chosen_list |> List.rev
        |> List.iter @@ fun c -> Stack.push (fun () -> resume r c) s);
        next s
    | effect Subgoal g, k -> (
        let s' = Stack.create () in
        match handler s' (fun () -> tac g) with
        | effect Fail, _ -> next s
        | (thm : thm) -> handler s (fun () -> continue k thm))
    | effect Fail, k ->
        cleanup k;
        next s
    | v -> v
  and next s =
    match Stack.pop_opt s with None -> fail () | Some thunk -> handler s thunk
  in
  handler (Stack.create ()) (fun () -> tac goal)

let with_dfs' tac goal =
  match tac goal with
  | effect Choose choices, k ->
      let rec try_each r = function
        | [] -> fail ()
        | c :: cs -> (
            match resume r c with
            | effect Fail, k ->
                cleanup k;
                try_each r cs
            | thm -> thm)
      in
      try_each (promote k) (as_chosen_list choices)
  | v -> v

let _ = (with_dfs', with_dfs'')

let itauto : tactic =
  pick
    [
      assumption;
      intro;
      neg_intro;
      gen;
      conj;
      elim_conj_asm;
      elim_disj_asm;
      false_elim;
      neg_elim;
      with_assumptions apply;
      contradict_asm;
      with_assumptions apply_asm;
      left;
      right;
    ]

let ctauto : tactic =
  pick
    [
      assumption;
      intro;
      neg_intro;
      gen;
      conj;
      elim_conj_asm;
      elim_disj_asm;
      false_elim;
      neg_elim;
      with_assumptions apply;
      contradict_asm;
      with_assumptions apply_asm;
      left;
      right;
      ccontr;
    ]

let ctauto_dfs : tactic = with_dfs ctauto

let auto_dfs : tactic =
 fun goal ->
  let thm = with_dfs auto goal in
  return_thm ~from:"auto_dfs" (Ok thm)

let destruct_elim =
  (destruct @! "ignore")
  @>> try_ (with_repeat (with_first elim_disj_asm))
  @>> try_ (with_repeat (with_first elim_exists_asm))

let simp_all = try_ simp_asm >> try_ simp

let rewrite_term ~target : tactic =
  let open Result.Syntax in
  let open Rewrite in
  fun (asms, conc) ->
    register ~prob:0.6 "rewrite" (Unsafe 5);
    let thm =
      let rules = perform Rules in
      let* chosen_rule = strip_forall (choose_theorems rules) in

      let* rw_thm = rewrite_once ~target chosen_rule conc in
      let* _, conc_rewritten = destruct_eq (concl rw_thm) in

      (* Fail if no progress was made *)
      if alphaorder conc conc_rewritten = 0 then fail ();

      let subthm = perform @@ Subgoal (asms, conc_rewritten) in
      let* rw_sym = Derived.sym rw_thm in
      eq_mp rw_sym subthm
    in
    return_thm ~from:"rewrite" thm

(* 
    assumes term is a comm monoid chain that is right associated
    effectively insertion sorts the terms using left_comm, then 
    finishing the last pair with comm

    later the thms and operators will be args but right now I'm just doing it for co_add

    returns a list of pairs, which are the subterm and the rewrite needed at that spot
 *)
type ac_rw = Comm_left of term | Comm of term

let rec ac_norm_tm_step op = function
  (* If the right operand is a var or const it means that it is the end of the chain *)
  | App (App (Const (op1, _), left), right) as t when op1 = op -> (
      (* Looking at the right operand *)
      match right with
      | (Const (_, _) | Var (_, _)) when alphaorder left right > 0 -> None
      | (Const (_, _) | Var (_, _)) when alphaorder left right <= 0 ->
          Some (Comm t)
      | App (App (Const (op1, _), b), _)
        when String.equal op1 op && alphaorder left b > 0 ->
          ac_norm_tm_step op right
      | App (App (Const (op1, _), b), _)
        when String.equal op1 op && alphaorder left b <= 0 ->
          Some (Comm_left t)
      | _ -> None)
  | _ -> None

(*First version only handles bare terms or equalities *)
let ac_norm op : tactic =
 fun g ->
  let rec aux acc = function
    | Var _ | Const _ -> acc
    | App (App (Const (op1, _), a), b) as t when String.equal op1 op ->
        aux (aux (t :: acc) a) b
    | App (f, x) -> aux (aux acc f) x
    | Lam (_, bod) -> aux acc bod
  in
  (* let possible_chains = aux [] (snd g) |> List.sort_uniq compare in *)
  let possible_chains = aux [] (snd g) in
  let comm = op ^ "_comm" in
  let comm_left = op ^ "_comm_left" in
  let assoc = op ^ "_assoc" in
  let step_tactics =
    List.filter_map
      (fun chain ->
        match ac_norm_tm_step op chain with
        | None -> None
        | Some (Comm t) ->
            (* trace_info *)
            (* @@ Printf.sprintf "Comm: %s\n" (Printing.pretty_print_hol_term t); *)
            Some (try_ @@ with_proven [ comm ] (rewrite_term ~target:t))
        | Some (Comm_left t) ->
            (* trace_info *)
            (* @@ Printf.sprintf "Comm_left: %s\n" *)
            (*      (Printing.pretty_print_hol_term t); *)
            Some (try_ @@ with_proven [ comm_left ] (rewrite_term ~target:t)))
      possible_chains
  in
  (List.fold_right
     (fun tac acc -> acc >> tac)
     step_tactics
     (try_ (with_repeat (with_proven [ assoc ] rewrite))))
    g

let cond : tactic =
 fun (asms, concl) ->
  register ~prob:0.2 "cond" (Unsafe 5);
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
  trace_info
    (Printf.sprintf "Found %d cond expressions\n" (List.length cond_args));
  match cond_args with
  | [] ->
      trace_error "no COND expressions found in goal";
      fail ()
  | terms ->
      let tm = choose_terms terms in
      trace_info "continuing with chosen term";

      (with_term tm destruct
      (* >> try_ (fun _ -> trace_info "testing"; fail ()) *)
      >> try_ (with_repeat (with_first elim_disj_asm)))
        (asms, concl)

module T = Domainslib.Task

(* This is generally recommended but I am setting to physical cores - 1 instead *)
(* let pool = T.setup_pool ~num_domains:(Domain.recommended_domain_count () - 1) () *)
let pool = T.setup_pool ~num_domains:3 ()

let parallel_map pool f lst =
  let promises = List.map (fun x -> T.async pool (fun () -> f x)) lst in
  List.map (T.await pool) promises

let run_tactic_in_worker (g : goal) (tac : tactic) : thm =
  match tac g with
  | effect Register _, k -> continue k ()
  | effect Rules, k -> continue k []
  | effect Trace (_, _), k -> continue k () (* or buffer *)
  | effect Quiet, k -> continue k true
  | effect Name (tm, asms), k -> continue k (Names.name_asm tm asms)
  | effect Fail, _ -> failwith "worker fail" (* or signal back *)
  | effect Choose choices, k -> (
      match as_chosen_list choices with
      | [] -> failwith "no choices"
      | c :: _ -> continue k c)
  | effect Subgoal _, _ -> failwith "unexpected subgoal in worker"
  | thm -> thm

let collect_subgoals (tacs : tactic list) : tactic_combinator =
  let tacs = ref tacs in
  let subgoals : (goal * tactic) list ref = ref [] in
  let mode = ref `Collect in
  let real_thms : thm list ref = ref [] in
  fun tac goal ->
    let rec handler f =
      match f () with
      | effect Subgoal g, k -> (
          match !mode with
          | `Collect -> (
              match !tacs with
              | [] ->
                  trace_proof "more subgoals than provided tactics";
                  fail ()
              | next :: rest ->
                  tacs := rest;
                  subgoals := (g, next) :: !subgoals;
                  handler (fun () -> continue k Derived.truth))
          | `Replay -> (
              match !real_thms with
              | [] ->
                  trace_proof "replay ran out of thms";
                  fail ()
              | thm :: rest ->
                  real_thms := rest;
                  handler (fun () -> continue k thm)))
      | v -> (
          match !mode with
          | `Replay -> v
          | `Collect ->
              (* Printf.printf "encountered count: %d\n" (List.length !subgoals); *)
              (* !subgoals *)
              (* |> List.iter (fun ((_, g), _) -> *)
              (*     print_endline @@ Printing.pretty_print_hol_term g); *)
              let ordered = List.rev !subgoals in

              (* let computed = List.map (fun (g, t) -> t g) ordered in *)
              let computed =
                T.run pool (fun () ->
                    parallel_map pool
                      (fun (g, t) -> run_tactic_in_worker g t)
                      ordered)
              in
              mode := `Replay;
              real_thms := computed;
              handler (fun () -> tac goal))
    in
    handler (fun () -> tac goal)

let ( >>=! ) = Fun.flip collect_subgoals

let collect_all_subgoals (tac1 : tactic) : tactic_combinator =
 fun tac goal ->
  let depth = Atomic.make 0 in
  let subgoals : goal list ref = ref [] in
  let mode = ref `Collect in
  let real_thms : thm list ref = ref [] in
  let rec handler f =
    match f () with
    | effect Subgoal g, k when Atomic.get depth = 0 -> (
        match !mode with
        | `Collect ->
            subgoals := g :: !subgoals;
            handler (fun () -> continue k Derived.truth)
        | `Replay -> (
            match !real_thms with
            | [] -> fail ()
            | thm :: rest ->
                real_thms := rest;
                handler (fun () -> continue k thm)))
    | effect Subgoal g, k when Atomic.get depth > 0 ->
        let thm : thm = perform (Subgoal g) in
        handler (fun () -> continue k thm)
    | v -> (
        match !mode with
        | `Replay -> v
        | `Collect ->
            let ordered = List.rev !subgoals in
            (* Printf.printf "collected %d subgoals\n" (List.length ordered); *)
            let run_follower g =
              Atomic.incr depth;
              let thm = run_tactic_in_worker g tac in
              Atomic.decr depth;
              thm
            in
            let computed =
              T.run pool (fun () -> parallel_map pool run_follower ordered)
            in
            mode := `Replay;
            real_thms := computed;
            handler (fun () -> tac1 goal))
  in
  handler (fun () -> tac1 goal)

let ( @>>! ) = collect_all_subgoals

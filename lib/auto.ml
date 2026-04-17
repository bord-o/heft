open Kernel
open Derived
open Effect
open Effect.Deep
open Tactic

type choice_kind =
  | CTerm of (goal * term)
  | CTheorem of goal * thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal

type search_metadata = MSubgoal of goal | MChoice of choice_kind | MResume

type step_result =
  | Cont of (choice_kind * (unit -> step_result)) list
  | Need of goal * (thm -> step_result)
  | Done of thm
  | Dead

module Priority = struct
  type t =
    search_metadata
    * (unit -> step_result)
    * (thm -> step_result) list
    * string list

  let compare : t -> t -> int =
   fun (a, _, _, _) (b, _, _, _) ->
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
      let r = Multicont.Deep.promote k in
      let choosable =
        as_chosen_list cs |> List.map (fun c () -> Multicont.Deep.resume r c)
      in
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
      let r = Multicont.Deep.promote k in
      Need (g, fun (v : thm) -> Multicont.Deep.resume r v)
  | effect Fail, _ -> Dead
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
    (fun (sub, choice, res) (e, _, _, _) ->
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
  F.add s (MSubgoal goal, (fun () -> step tac goal), [], []);
  let rec aux () =
    (* print_endline (F.stats s); *)
    match F.pop s with
    | None -> fail ()
    | Some (_, thunk, parents, path) -> (
        let current_path = ref path in
        match run_thunk_with_path current_path thunk with
        | Done v -> (
            match parents with
            | [] ->
                emit_proof_path !current_path;
                v
            | resume :: rest ->
                F.add s (MResume, (fun () -> resume v), rest, !current_path);
                aux ())
        | Need (g, resume) ->
            F.add s
              ( MSubgoal g,
                (fun () -> step tac g),
                resume :: parents,
                !current_path );
            aux ()
        | Dead -> aux ()
        | Cont thunks ->
            thunks |> List.rev
            |> List.iter (fun (m, t) ->
                F.add s (MChoice m, t, parents, !current_path));
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
        let r = Multicont.Deep.promote k in
        (choices |> as_chosen_list |> List.rev
        |> List.iter @@ fun c ->
           Stack.push (fun () -> Multicont.Deep.resume r c) s);
        next s
    | effect Subgoal g, k -> (
        let s' = Stack.create () in
        match handler s' (fun () -> tac g) with
        | effect Fail, _ -> next s
        | (thm : thm) -> handler s (fun () -> continue k thm))
    | effect Fail, _ -> next s
    | v -> v
  and next s =
    match Stack.pop_opt s with None -> fail () | Some thunk -> handler s thunk
  in
  handler (Stack.create ()) (fun () -> tac goal)

let with_dfs' : tactic_combinator =
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
    | effect Subgoal g, k ->
        let thm : thm = handler (fun () -> tac g) in
        handler (fun () -> continue k thm)
    | effect Fail, _ -> fail ()
    | v -> v
  in
  handler (fun () -> tac goal)

let _ = (with_dfs', with_dfs'')

let itauto_tac : tactic =
  pick_tac
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
      with_assumptions apply_tac;
      contradict_asm_tac;
      with_assumptions (with_first_term apply_asm_tac);
      left_tac;
      right_tac;
    ]

let ctauto_tac : tactic =
  pick_tac
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
      with_assumptions apply_tac;
      contradict_asm_tac;
      with_assumptions (with_first_term apply_asm_tac);
      left_tac;
      right_tac;
      ccontr_tac;
    ]

let ctauto_dfs_tac : tactic = with_dfs ctauto_tac

let auto_dfs_tac : tactic =
 fun goal ->
  let thm = with_dfs auto_tac goal in
  return_thm ~from:"auto_dfs_tac" (Ok thm)

let destruct_elim_tac =
  destruct_tac @! "ignore"
  >>> try_ (with_first elim_disj_asm_tac)
  >>> try_ (with_repeat (with_first elim_exists_asm_tac))

let simp_all_tac = try_ simp_asm_tac >> try_ simp_tac

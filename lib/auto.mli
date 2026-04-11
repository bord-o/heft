open Tactic

type search_metadata =
  | MSubgoal of goal
  | MChoice of choice_kind
  | MResume
      (** [search_metadata] is used by [with_best_first] to sort a priority
          queue, deciding which path of a proof space to explore next *)

type step_result =
  | Cont of (choice_kind * (unit -> step_result)) list
  | Need of goal * (Kernel.thm -> step_result)
  | Done of Kernel.thm
  | Dead
      (** In search [tactic_combinator]s, [step_result] is used to represent
          possible continuations of a search *)

(** {1 Search Infrastructure} *)

module Priority : sig
  type t =
    search_metadata
    * (unit -> step_result)
    * (Kernel.thm -> step_result) list
    * string list

  val compare : t -> t -> int
end

module PriorityQueue : sig
  type t = Pqueue.MakeMax(Priority).t

  val create : unit -> t
  val length : t -> int
  val is_empty : t -> bool
  val add : t -> Priority.t -> unit
  val add_iter : t -> ((Priority.t -> unit) -> 'x -> unit) -> 'x -> unit
  val max_elt : t -> Priority.t option
  val get_max_elt : t -> Priority.t
  val pop_max : t -> Priority.t option
  val remove_max : t -> unit
  val clear : t -> unit
  val copy : t -> t
  val of_array : Priority.t array -> t
  val of_list : Priority.t list -> t
  val of_iter : ((Priority.t -> unit) -> 'x -> unit) -> 'x -> t
  val iter_unordered : (Priority.t -> unit) -> t -> unit
  val fold_unordered : ('acc -> Priority.t -> 'acc) -> 'acc -> t -> 'acc
end

module type Frontier = sig
  type t

  val create : unit -> t
  val pop : t -> Priority.t option
  val add : t -> Priority.t -> unit
  val stats : t -> string
end

val step : tactic -> goal -> step_result
(** Performs one expansion of the proof tree and aggregates the results along
    with their continuations *)

val run_thunk_with_path : string list ref -> (unit -> 'a) -> 'a
(** Executes a thunk while capturing [Trace (Proof, _)] effects into the
    provided path reference. Used by search combinators to track the winning
    proof sequence *)

val emit_proof_path : string list -> unit
(** Formats a proof path as a tactic script and emits it as a
    [Trace (Search, _)] effect *)

val stats_of_list : (search_metadata * 'a * 'b * 'c) list -> string
(** Summarizes a list of search entries by counting subgoals, choices, and
    resumptions *)

module StackFrontier : Frontier

val make_search : (module Frontier) -> tactic_combinator
(** Creates a search combinator from a [Frontier] module. The frontier
    determines exploration order (stack for DFS, queue for BFS, priority queue
    for best-first) *)

val with_dfs : tactic_combinator
(** Performs depth-first search over choices and subgoals. Explores the proof
    space using a stack, backtracking on failure. Emits the winning proof path
    on success *)

module PQueueFrontier : Frontier

val with_best_first : tactic_combinator
(** Performs best-first search over choices and subgoals. Uses a priority queue
    ordered by [search_metadata] to explore promising paths first (resumes
    before choices, choices before subgoals). Emits the winning proof path on
    success *)

module QueueFrontier : Frontier

val with_bfs : tactic_combinator
(** Performs breadth-first search over choices and subgoals. Uses a queue to
    explore paths level by level. Emits the winning proof path on success *)

val with_dfs'' : tactic_combinator
(** Alternative DFS implementation using an explicit stack for choice points.
    Does not track proof paths *)

val with_dfs' : tactic_combinator
(** Recursive DFS implementation that uses the call stack for backtracking.
    Simpler but may overflow on deep searches. Does not track proof paths *)

(** {1 Automation Tactics} *)

val itauto_tac : tactic
(** Complete automation tactic for intuitionistic propositional logic. Chooses
    among various introduction and elimination tactics. Use with a search
    combinator like [with_dfs] or [with_best_first] *)

val ctauto_tac : tactic
(** Complete automation tactic for classical propositional logic. Includes all
    intuitionistic tactics plus [ccontr_tac]. Use with a search combinator like
    [with_dfs] or [with_best_first] *)

val ctauto_dfs_tac : tactic
(** [ctauto_tac] wrapped with [with_dfs] for automatic depth-first proof search
*)

val auto_dfs_tac : tactic
(** [auto_tac] wrapped with [with_dfs] for automatic depth-first proof search *)

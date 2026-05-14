open Kernel
open Tactic

(** Search-based proof automation built on top of [Tactic]. *)

(** {1 Search Infrastructure} *)

type choice_kind =
  | CTerm of (goal * term)
  | CTheorem of goal * thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal
      (** Tag describing what was offered at a given [Choose] point. *)

type search_metadata =
  | MSubgoal of goal
  | MChoice of choice_kind
  | MResume
      (** Classification of an entry in a search frontier, used by
          [with_best_first] to order exploration. *)

type step_result =
  | Cont of (choice_kind * (unit -> step_result)) list
  | Need of goal * (Kernel.thm -> step_result)
  | Done of Kernel.thm
  | Dead  (** Result of one expansion of the proof tree by [step]. *)

type cancel_token = { mutable cancelled : bool }

val fresh_token : unit -> cancel_token

module Priority : sig
  type t =
    search_metadata
    * (unit -> step_result)
    * (Kernel.thm -> step_result) list
    * string list
    * cancel_token

  val compare : t -> t -> int
  (** Orders entries with cheapest steps first. Among [MChoice]s, prefers
      smaller terms and cheaper tactics. *)
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

(** A container of pending search entries. The choice of frontier determines the
    search order: stack for DFS, queue for BFS, priority queue for best-first.
*)
module type Frontier = sig
  type t

  val create : unit -> t
  val pop : t -> Priority.t option
  val add : t -> Priority.t -> unit
  val stats : t -> string
end

val step : tactic -> goal -> step_result
(** Runs a tactic until it performs its next [Subgoal], [Choose], [Fail], or
    completes, and packages the continuation. *)

val stats_of_list : (search_metadata * 'a * 'b * 'c * 'd) list -> string
(** Formats counts of subgoals, choices, and resumptions in a list of frontier
    entries. *)

module StackFrontier : Frontier

val make_search : (module Frontier) -> tactic_combinator
(** Builds a search combinator from a [Frontier] implementation. *)

val with_dfs : tactic_combinator
(** Depth-first search using [StackFrontier]. *)

val with_dfs' : tactic_combinator

module PQueueFrontier : Frontier

val with_best_first : tactic_combinator
(** Best-first search using [PQueueFrontier]. *)

module QueueFrontier : Frontier

val with_bfs : tactic_combinator
(** Breadth-first search using [QueueFrontier]. *)

(** {1 Automation Tactics} *)

val itauto : tactic
(** Choice over the basic intuitionistic propositional tactics. Wrap with a
    search combinator to drive automation. *)

val ctauto : tactic
(** Like [itauto], extended with [ccontr] for classical propositional logic. *)

val ctauto_dfs : tactic
(** [ctauto] wrapped with [with_dfs]. *)

val auto_dfs : tactic
(** [auto] wrapped with [with_dfs]. *)

val destruct_elim : tactic
(** A variation of [destruct] which also eliminates the existentials it
    generates *)

val simp_all : tactic
(** A combination of [simp_asm] and [simp] *)

val ac_norm : string -> tactic
(** [ac_norm op] performs normalization using associativity and commutativity
    theorems with names of ["op_comm_left"], ["op_comm"], and ["op_assoc"]. *)

val cond : tactic
(** Finds [COND] applications in the goal, chooses one of their conditions via
    [Choose], and delegates to [destruct] on the chosen condition. *)

val ( >>=! ) : tactic -> tactic list -> tactic
val ( @>>! ) : tactic -> tactic_combinator

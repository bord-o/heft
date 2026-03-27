(** Tactic engine for interactive theorem proving with algebraic effects. *)

(** {1 Goals and Proof State} *)

type goal = Kernel.term list * Kernel.term
(** A list of assumptions and a term to prove under them *)

val pp_goal :
  Ppx_deriving_runtime.Format.formatter -> goal -> Ppx_deriving_runtime.unit

val show_goal : goal -> Ppx_deriving_runtime.string

type level =
  | Debug
  | Info
  | Warn
  | Error
  | Proof
  | Search
      (** [level] is used to distinguish between different types of traces *)

type proof_state =
  | Incomplete of goal
  | Complete of Kernel.thm
      (** [proof_state] is used by the ambient handler [prove] to represent the
          result of applying a tactic *)

val pp_proof_state :
  Ppx_deriving_runtime.Format.formatter ->
  proof_state ->
  Ppx_deriving_runtime.unit

val show_proof_state : proof_state -> Ppx_deriving_runtime.string

type tactic = goal -> Kernel.thm
(** A [tactic] is a function that works on a goal, possibly performing effects
*)

type tactic_combinator = tactic -> tactic
(** A [tactic_combinator] is a function between tactics. It has many uses like
    sequencing tactics ([then_one], [then_all]), handling specific effects
    ([with_no_trace], [with_fuel_limit]), or managing search over a tactics
    choices ([with_dfs], [with_best_first]). *)

type cost = Safe of int | Unsafe of int

type choice_kind =
  | CTerm of (goal * Kernel.term)
  | CTheorem of goal * Kernel.thm
  | CTactic of goal * cost * tactic
  | CUnknown of goal

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

(** {1 Choice and Ranking GADTs} *)

type _ rankable =
  | Term : Kernel.term list -> Kernel.term rankable
  | Goal : goal list -> goal rankable
  | Tactic : tactic list -> tactic rankable
  | Unknown : 'a list -> 'a rankable
      (** The [rankable] GADT is used to allow both agnostic treatment of the
          [Rank] effect as well as deeper introspection into the underlying data
          when needed *)

type _ choosable =
  | Term : Kernel.term list -> Kernel.term choosable
  | Theorem : Kernel.thm list -> Kernel.thm choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable
      (** The [choosable] GADT is used to allow both agnostic treatment of the
          [Choose] effect as well as deeper introspection into the underlying
          data when needed *)

exception Out_of_fuel
(** Raised by the [with_fuel_limit] [tactic_combinator] to indicate that a
    tactic has gone over its limit *)

(** {1 Effects} *)

type _ Effect.t +=
  | Subgoal : goal -> Kernel.thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Rank : 'a rankable -> 'a list Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Burn : (string * cost) -> unit Effect.t
  | Rules : Kernel.thm list Effect.t

(** {1 Effect Helpers} *)

val as_ranked_list : 'a rankable -> 'a list
(** Extracts the underlying list from the [rankable] GADT *)

val as_chosen_list : 'a choosable -> 'a list
(** Extracts the underlying list from the [choosable] GADT *)

val cost_of_tactic : tactic -> goal -> string * cost
(** Runs a tactic just far enough to extract its name and [Burn] cost. The
    tactic must perform [Burn] as its first effect *)

val step : tactic -> goal -> step_result
(** Performs one expansion of the proof tree and aggregates the results along
    with their continuations *)

val fail : unit -> 'a
(** Performs the [Fail] effect. Used to signal when a tactic doesn't apply or
    doesn't make progress *)

val burn : string -> cost -> unit
(** Performs the [Burn] effect. Used to signal the cost of a tactic relative to
    other tactics *)

val trace_dbg : string -> unit
(** Emits a debug-level trace message *)

val trace_info : string -> unit
(** Emits an info-level trace message *)

val trace_error : string -> unit
(** Emits an error-level trace message *)

val trace_proof : string -> unit
(** Emits a proof-level trace message, used by tactics to record their name in
    the proof path *)

val choose_terms : Kernel.term list -> Kernel.term
(** Requests a choice among a list of terms *)

val choose_theorems : Kernel.thm list -> Kernel.thm
(** Requests a choice among a list of theorems *)

val choose_tactics : tactic list -> tactic
(** Requests a choice among a list of tactics *)

val choose_unknowns : 'a list -> 'a
(** Requests a choice among a list of unknown type *)

val rank_terms : Kernel.term list -> Kernel.term list
(** Requests a ranking/sorting of terms by some heuristic *)

val return_thm :
  ?from:string ->
  ( 'a,
    [< `BadSubstitutionList of (Kernel.term * Kernel.term) list
    | `CantApplyNonFunctionType of Kernel.term
    | `CantCreateVariantForNonVariable of Kernel.term
    | `CantDestructEquality of Kernel.term
    | `Clash of Kernel.term
    | `ConstantTermAlreadyDeclared of string
    | `ConstructorsAlreadyExist of string list
    | `DefinitionError of string
    | `EqMp of Kernel.thm * Kernel.thm
    | `InvariantViolation of string
    | `LamRuleCantApply of Kernel.term * Kernel.thm
    | `MakeAppTypesDontAgree of Kernel.hol_type * Kernel.hol_type
    | `MakeLamNotAVariable of Kernel.term
    | `NameMappingError of string
    | `NewAxiomNotAProp of Kernel.term
    | `NewBasicDefinition of Kernel.term
    | `NewBasicDefinitionAlreadyDefined of string
    | `NoBaseCase of string
    | `NoRewriteMatch of Kernel.thm * Kernel.term
    | `NotAConj of Kernel.term
    | `NotAConst of Kernel.term
    | `NotAConstantName of string
    | `NotADisj of Kernel.term
    | `NotAForall of Kernel.term
    | `NotALam of Kernel.term
    | `NotANegation of Kernel.term
    | `NotAProposition of Kernel.term
    | `NotAVar of Kernel.term
    | `NotAnApp of Kernel.term
    | `NotAnApplication of Kernel.term
    | `NotAnExists of Kernel.term
    | `NotAnImp of Kernel.term
    | `NotBothEquations of Kernel.thm * Kernel.thm
    | `NotFreshConstructor of string list
    | `NotPositive of string
    | `NotTrivialBetaRedex of Kernel.term
    | `OperationDoesntMatch of string
    | `RuleTrans of Kernel.thm * Kernel.thm
    | `TypeAlreadyDeclared of string
    | `TypeAlreadyExists of string
    | `TypeConstructorNotAVariable of string
    | `TypeDefinitionError of string
    | `TypeEquivalenceNotImplemented of Kernel.hol_type * Kernel.hol_type
    | `TypeNotDeclared of string
    | `TypeVariableNotAConstructor of string
    | `TypesDontAgree of Kernel.hol_type * Kernel.hol_type
    | `UnexpectedLambdaForm of Kernel.term
    | `WrongNumberOfTypeArgs of string ] )
  result ->
  'a
(** Used by tactics to handle failure and trace information about which tactic
    was run *)

(** {1 Tactics} *)

val left_tac : tactic
(** Takes goals like [P \/ Q] and creates the subgoal [P]. Fails if the goal's
    conclusion is not a disjunction. This tactic is {b not safe}, as it is not
    true that [P] is always provable when [P \/ Q] is *)

val right_tac : tactic
(** Takes goals like [P \/ Q] and creates the subgoal [Q]. Fails if the goal's
    conclusion is not a disjunction. This tactic is {b not safe}, as it is not
    true that [Q] is always provable when [P \/ Q] is *)

val or_tac : tactic
(** Chooses between [left_tac] and [right_tac], ensuring both sides are
    attempted if used under a search combinator *)

val apply_asm_tac : tactic
(** Finds assumptions of the form [P -> Q] for the goal [Q] and creates a
    subgoal [P] *)

val apply_thm_tac : tactic
(** Applies a chosen theorem from [Rules] by stripping foralls and matching the
    conclusion against the goal *)

val apply_thm_asm_tac : tactic
(** Applies a chosen theorem from [Rules] to a chosen assumption. If theorem is
    [P ==> Q] and assumption is [P], replaces the assumption with [Q] and
    creates a subgoal with the updated assumptions *)

val apply_neg_asm_tac : tactic
(** Proves [F] by finding a negation [~P] in assumptions and creating a subgoal
    to prove [P]. Fails if the goal is not [F] or no suitable negation exists *)

val assume_tac : tactic
(** Proves any goal by assuming it. This creates a theorem with the goal as a
    hypothesis *)

val sorry_tac : tactic

val sym_tac : tactic
(** Transforms a goal [l = r] into [r = l] *)

val rewrite_tac : tactic
(** Rewrites the goal using a chosen theorem from [Rules]. Performs subterm
    matching and fails if no progress is made *)

val rewrite_asm_tac : tactic
(** Rewrites a chosen assumption using a theorem from [Rules]. Fails if no
    progress is made *)

val beta_tac : tactic
(** Performs deep beta reduction on the goal and creates a subgoal with the
    reduced term *)

val beta_asm_tac : tactic
(** Performs deep beta reduction on a chosen assumption. Fails if no progress is
    made *)

val assert_tac : tactic
(** Introduces an assertion: chooses a term, creates a subgoal to prove it, then
    adds it as an assumption for the original goal *)

val mp_asm_tac : tactic
(** Finds an implication [P ==> Q] in assumptions where [P] is also an
    assumption, and adds [Q] to the assumptions. Fails if no such implication
    exists or [Q] is already present *)

val intro_tac : tactic
(** Transforms a goal [P ==> Q] into a subgoal [Q] with [P] added to the
    assumptions. Fails if goal is not an implication *)

val refl_tac : tactic
(** Proves goals of the form [t = t] by reflexivity. Fails if the goal is not an
    equality or the sides are not identical *)

val trans_tac : tactic
(** Proves an equality [l = r] by choosing an intermediate term [s] and creating
    two subgoals [l = s] and [s = r], then combining them via transitivity *)

val assumption_tac : tactic
(** Proves the goal if it matches one of the assumptions. Fails if no matching
    assumption is found *)

val spec_asm_tac : Kernel.term -> tactic
(** [spec_asm_tac tm] specializes a universally quantified assumption
    [forall x. P x] with [tm], adding the result as a new assumption. The forall
    assumption is chosen via [Choose] *)

val sym_asm_tac : tactic
(** Finds an equality assumption [a = b] and replaces it with [b = a]. The
    assumption is chosen via [Choose] *)

val eq_true_asm_tac : tactic
(** Finds a bare boolean assumption [P] (not an equality) and adds [P = T] to
    the assumptions *)

val eq_true_elim_asm_tac : tactic
(** Finds an assumption [P = T] and adds [P] to the assumptions *)

val eq_true_elim_tac : tactic
(** Transforms a goal [P = T] into a subgoal [P], then wraps the result with
    [eq_truth_intro] *)

val eq_false_elim_tac : tactic

val conj_tac : tactic
(** Transforms a goal [P /\ Q] into two subgoals [P] and [Q]. Fails if the goal
    is not a conjunction *)

val elim_disj_asm_tac : tactic
(** Eliminates a disjunction [P \/ Q] in the assumptions by case splitting,
    creating two subgoals: one with [P] and one with [Q] *)

val elim_conj_asm_tac : tactic
(** Eliminates a conjunction [P /\ Q] in the assumptions by replacing it with
    both [P] and [Q] as separate assumptions *)

val neg_elim_tac : tactic
(** Proves any goal when both [P] and [~P] are in assumptions, deriving a
    contradiction. Fails if no such pair exists *)

val neg_intro_tac : tactic
(** Transforms a goal [~P] into a subgoal [F] with [P] added to the assumptions.
    Fails if goal is not a negation or [P] is already an assumption *)

val ccontr_tac : tactic
(** Proves [P] by classical contradiction: assumes [~P] and derives [F]. This is
    a classical (non-intuitionistic) tactic *)

val false_elim_tac : tactic
(** Proves any goal when [F] (false) is in the assumptions. Fails if [F] is not
    present *)

val exists_tac : tactic
(** Proves an existential goal [exists x. P x] by choosing a witness term and
    creating a subgoal to prove [P] with the chosen term substituted *)

val gen_tac : tactic
(** Transforms a goal [forall x. P] into a subgoal [P]. Fails if the goal is not
    a universal quantification *)

val induct_tac : tactic
(** Applies structural induction. Works on both [forall x. P x] goals (inducting
    on the quantified variable) and goals with a free variable (discharges
    assumptions, requantifies, inducts, then re-specializes). For the free
    variable case, the variable is chosen via [Choose]. *)

val truth_tac : tactic
(** Proves the goal [T] (truth). Fails if the goal is not [T] *)

val cases_tac : tactic
(** Performs case splitting. For [forall b:bool] goals, splits into [b=T] and
    [b=F] cases. For [forall x:inductive] goals, delegates to [induct_tac]. For
    arbitrary bool expressions (via [with_arbitrary_term]), adds [e=T] and [e=F]
    as assumptions *)

val destruct_tac : tactic
(** Performs case analysis on a chosen term of an inductive type using
    exhaustiveness. Adds an assumption of the form
    [tm = C1 \/ (exists a0. tm = C2 a0) \/ ...] to the goal. Works on arbitrary
    terms, not just variables. Use [elim_disj_asm_tac] and [elim_exists_asm_tac]
    to split the resulting disjunction. For induction with hypotheses, use
    [induct_tac] instead. *)

val elim_exists_asm_tac : tactic
(** Eliminates an existential [exists x. P x] in the assumptions by replacing it
    with [P x] where [x] is the bound variable. The existential assumption is
    chosen via [Choose]. Fails if no existential assumptions exist. *)

(** {1 Proof Runner} *)

val prove : ?name:string -> goal -> tactic -> proof_state
(** The main effect handler that runs a tactic on a goal. Provides default
    interpretations for all effects: printing traces, taking first choices,
    ignoring fuel costs, etc. Returns [Complete thm] on success or
    [Incomplete goal] on failure *)

(** {1 Tactic Combinators: Sequencing} *)

val then_one : tactic -> tactic_combinator
(** Sequences two tactics: applies [tac1] then applies [tac] to only the first
    subgoal. Remaining subgoals bubble up. Infix: [>>] *)

val ( >> ) : tactic -> tactic_combinator

val then_all : tactic -> tactic_combinator
(** Sequences two tactics: applies [tac1] then applies [tac] to all subgoals,
    including subgoals emitted from children. Infix: [>>>>] *)

val ( >>>> ) : tactic -> tactic_combinator

val then_all_direct : tactic -> tactic_combinator
(** Applies [tac] to each direct subgoal of [tac1], but lets subgoals from [tac]
    itself bubble up to the outer handler. Infix: [>>>] *)

val ( >>> ) : tactic -> tactic_combinator

val then_each : tactic list -> tactic_combinator
(** Applies a list of tactics to subgoals in order. Fails if there are more
    subgoals than tactics provided. Infix: [>>=] *)

val ( >>= ) : tactic -> tactic list -> tactic

(** {1 Tactic Combinators: Choice and Search} *)

val with_first : tactic_combinator
(** Handles [Choose] by trying each choice in order until one succeeds. Only
    handles choices at one level; for recursive search use [with_dfs] or
    [with_best_first] *)

val with_arbitrary_term : Kernel.term -> tactic_combinator
(** Forces a specific term to be chosen when a [Choose (Term _)] effect is
    performed, regardless of whether it appears in the choices *)

val with_term : Kernel.term -> tactic_combinator
(** Forces a specific term to be chosen when a [Choose (Term _)] effect is
    performed. Fails if the term is not among the choices *)

val cond_tac : tactic
(** Finds COND applications in the goal and case-splits on the condition
    argument. Collects all condition terms from COND expressions, presents them
    via [Choose], then delegates to [cases_tac] *)

val try_ : tactic_combinator
(** Converts failure into a subgoal request, allowing a tactic sequence to
    continue when intermediate tactics fail *)

val pick_tac : tactic list -> tactic
(** Creates a tactic that chooses among the given tactics. Used with search
    combinators to explore different proof strategies *)

val solve : tactic_combinator
(** Requires a tactic to completely solve the goal without leaving subgoals.
    Fails if any subgoals remain *)

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

val with_repeat : tactic_combinator
(** Repeatedly applies a tactic until it fails or makes no progress. On failure
    after progress, emits a subgoal for the current state *)

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

(** {1 Tactic Combinators: Interactive and Selection} *)

val with_interactive_choice : tactic_combinator
(** Handles [Choose] effects by prompting the user to select from the available
    options via stdin *)

val with_nth_choice : int -> tactic_combinator
(** Always selects the [n]th option from any [Choose] effect. Fails if [n] is
    out of bounds *)

val with_nth_term : int -> tactic_combinator
(** Always selects the [n]th term from a [Choose (Term _)] effect. Fails if [n]
    is out of bounds. Only handles term choices, other choices pass through *)

val with_term_size_ranking : tactic_combinator
(** Handles [Rank (Term _)] effects by sorting terms from smallest to largest
    based on AST size *)

(** {1 Tactic Combinators: Fuel and Tracing} *)

val cost_value : cost -> int
(** Extracts the integer value from a [cost], whether [Safe] or [Unsafe] *)

val with_added_fuel : int -> tactic_combinator
(** Adds extra fuel to each [Burn] effect, increasing all tactic costs by the
    given amount *)

val with_fuel_limit' : int -> tactic_combinator
(** Tracks fuel consumption and fails when the limit is exceeded. Uses an
    internal mutable counter *)

val with_fuel_limit : int ref -> tactic_combinator
(** Tracks fuel consumption and raises [Out_of_fuel] when the limit is exceeded.
    The limit is a mutable reference that decreases with each [Burn] effect *)

val with_fuel_counter : int ref -> tactic_combinator
(** Tracks total fuel consumed by incrementing a mutable reference for each
    [Burn] effect *)

val show_tac : tactic

val with_show_subgoal : tactic_combinator
(** Prints the current subgoal (assumptions and conclusion) before running the
    tactic *)

val with_info_trace : tactic_combinator
(** Prints info-level trace messages to stdout, letting all other effects pass
    through *)

val with_no_automation_trace : tactic_combinator

val with_no_trace : ?show_proof:bool -> tactic_combinator
(** Suppresses trace messages. By default suppresses all except [Search]. Set
    [show_proof:true] to also show [Proof] traces *)

(** {1 Tactic Combinators: Rules} *)

val with_assumptions : tactic_combinator
(** Provides the goal's assumptions as theorems when a [Rules] effect is
    performed *)

val with_rules : Kernel.thm list -> tactic_combinator
(** Provides a fixed list of theorems when a [Rules] effect is performed *)

val with_flip_rules : tactic_combinator
(** Inverts the direction of all equality rules provided by the outer [Rules]
    handler using [sym] *)

val with_rule : Kernel.thm -> tactic_combinator
(** Provides a single theorem when a [Rules] effect is performed *)

val with_definition : string list -> tactic_combinator
(** Looks up definitions by name and provides them when a [Rules] effect is
    performed. Fails if any name is not found *)

val with_proven : string list -> tactic_combinator
(** Looks up previously proven theorems by name and provides them when a [Rules]
    effect is performed. Fails if any name is not found *)

val with_rules_and_assumptions : Kernel.thm list -> tactic_combinator
(** Provides both the given rules and the goal's assumptions as theorems when a
    [Rules] effect is performed *)

(** {1 Simplification and Automation} *)

val intros_tac : tactic
(** Repeatedly applies [intro_tac] and [gen_tac] until neither makes progress.
    Useful for introducing all hypotheses at once *)

val simp_tac : ?with_asms:bool -> tactic
(** Simplifies the goal using rewrite rules from definitions and registered simp
    lemmas. Set [with_asms:false] to exclude assumptions *)

val auto_tac : tactic
(** Automation tactic combining simplification with basic logical tactics. Use
    with a search combinator for full automation *)

val auto_dfs_tac : tactic
(** [auto_tac] wrapped with [with_dfs] for automatic depth-first proof search *)

val simp_asm_tac : ?with_asms:bool -> ?add:Kernel.thm list -> tactic
(** Simplifies assumptions using rewrite rules from definitions. Use [add] to
    provide additional rules. Set [with_asms:false] to exclude other assumptions
    as rewrite rules *)

(** {1 Term Synthesis} *)

val with_synthetic_term :
  ?extra:(string * Kernel.hol_type) list -> int -> tactic_combinator
(** Handles [Choose (Term _)] effects by enumerating terms of the appropriate
    type up to the given depth, then choosing among them. Use [extra] to provide
    additional variables for synthesis *)

(** {1 Proof Execution} *)

val run_proof :
  ?notrace:bool ->
  ?name:string ->
  ?simp:bool ->
  ?quiet:bool ->
  goal ->
  tactic ->
  unit
(** Runs a proof with fuel tracking and tracing. Prints the resulting theorem
    and fuel usage on success, or the incomplete subgoal on failure. Set
    [simp:true] to register the result as a simp lemma. Set [quiet:true] to
    suppress output *)

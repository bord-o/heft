open Kernel

(** Tactic engine for interactive theorem proving, built on OCaml algebraic
    effects. *)

(** {1 Goals and Proof State} *)

type goal = (string * term) list * term
(** A goal is a pair of assumptions and a conclusion to prove under them. *)

val make_goal : ?asms:(string * term) list -> term -> goal
(** [make_goal ?asms concl] builds a goal with conclusion [concl]. Defaults to
    no assumptions.

    {[
    make_goal (make_imp p q) (* ⊢ p ==> q *) make_goal ~asms:[ p ] q (* p ⊢ q *)
    ]} *)

val pp_goal : Format.formatter -> goal -> unit
val show_goal : goal -> string

type level =
  | Debug
  | Info
  | Warn
  | Error
  | Proof
  | Search
      (** Trace severity. [Proof] is used by tactics to record their name on the
          proof path; [Search] is used by search combinators. *)

type proof_state =
  | Incomplete of goal
  | Complete of thm  (** Result of running a tactic through [prove]. *)

val pp_proof_state : Format.formatter -> proof_state -> unit
val show_proof_state : proof_state -> string

type tactic = goal -> thm
(** A tactic transforms a goal into a theorem, possibly performing effects. *)

type tactic_combinator = tactic -> tactic
(** A function between tactics. Used for sequencing ([then_one], [then_all]),
    handling effects ([with_no_trace], [with_fuel_limit]), and managing search
    ([with_dfs], [with_best_first]). *)

type cost =
  | Safe of int
  | Unsafe of int
      (** Cost associated with a tactic. [Safe] tactics preserve provability;
          [Unsafe] tactics may fail even when the goal is provable. *)

(** {1 Choice} *)

type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
  | Tactic : tactic list -> tactic choosable
  | Unknown : 'a list -> 'a choosable
      (** Typed wrapper for the [Choose] effect. Allows handlers to introspect
          the kind of value being chosen. *)

exception Out_of_fuel
(** Raised by [with_fuel_limit] when the fuel counter reaches zero. *)

exception Cleanup

val cleanup : ('a, 'b) continuation -> unit

type tactic_info = { name : string; cost : cost; prob : float }

(** {1 Effects} *)

type _ Effect.t +=
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Quiet : bool Effect.t
  | Register : tactic_info -> unit Effect.t
  | Rules : thm list Effect.t
  | Name : (term * (string * term) list) -> (string * term) Effect.t

(** {1 Effect Helpers} *)

val as_chosen_list : 'a choosable -> 'a list
(** Extracts the underlying list from a [choosable]. *)

val cost_of_tactic : tactic -> goal -> string * cost
(** Runs a tactic just far enough to extract its name and first [Register] cost.
    The tactic must perform [Register] before any other effect. *)

val prob_of_tactic : tactic -> goal -> string * float
(** Like [cost_of_tactic] but returns the probability. *)

val default_prob : cost -> float
(** Default probability for a cost: [Safe] -> 1.0, [Unsafe] -> 0.5. *)

val fail : unit -> 'a
(** Performs the [Fail] effect. Signals that a tactic does not apply. *)

val register : ?prob:float -> string -> cost -> unit
(** Performs the [Register] effect. If [prob] is omitted, [default_prob cost] is
    used. *)

val trace_dbg : string -> unit
val trace_info : string -> unit
val trace_error : string -> unit

val trace_proof : string -> unit
(** Emits a [Proof]-level trace. Used by tactics to record their name on the
    proof path. *)

val choose_terms : term list -> term
val choose_theorems : thm list -> thm
val choose_tactics : tactic list -> tactic
val choose_unknowns : 'a list -> 'a

val return_thm :
  ?from:string ->
  ( 'a,
    [< `BadSubstitutionList of (term * term) list
    | `CantApplyNonFunctionType of term
    | `CantCreateVariantForNonVariable of term
    | `CantDestructEquality of term
    | `Clash of term
    | `ConstantTermAlreadyDeclared of string
    | `ConstructorsAlreadyExist of string list
    | `DefinitionError of string
    | `EqMp of thm * thm
    | `InvariantViolation of string
    | `LamRuleCantApply of term * thm
    | `MakeAppTypesDontAgree of hol_type * hol_type
    | `MakeLamNotAVariable of term
    | `NameMappingError of string
    | `NewAxiomNotAProp of term
    | `NewBasicDefinition of term
    | `NewBasicDefinitionAlreadyDefined of string
    | `NoBaseCase of string
    | `NoRewriteMatch of thm * term
    | `NotAConj of term
    | `NotAConst of term
    | `NotAConstantName of string
    | `NotADisj of term
    | `NotAForall of term
    | `NotALam of term
    | `NotANegation of term
    | `NotAProposition of term
    | `NotAVar of term
    | `NotAnApp of term
    | `NotAnApplication of term
    | `NotAnExists of term
    | `NotAnImp of term
    | `NotBothEquations of thm * thm
    | `NotFreshConstructor of string list
    | `NotPositive of string
    | `NotTrivialBetaRedex of term
    | `OperationDoesntMatch of string
    | `RuleTrans of thm * thm
    | `TypeAlreadyDeclared of string
    | `TypeAlreadyExists of string
    | `TypeConstructorNotAVariable of string
    | `TypeDefinitionError of string
    | `TypeEquivalenceNotImplemented of hol_type * hol_type
    | `TypeNotDeclared of string
    | `TypeVariableNotAConstructor of string
    | `TypesDontAgree of hol_type * hol_type
    | `UnexpectedLambdaForm of term
    | `WrongNumberOfTypeArgs of string ] )
  result ->
  'a
(** Unwraps a kernel result into a theorem. On [Ok], emits a [Proof] trace
    tagged with [from] and returns the theorem. On [Error], traces the error and
    performs [Fail]. *)

(** {1 Tactics} *)

val assumption : tactic
(** Closes the goal if its conclusion matches an assumption. *)

val truth : tactic
(** Closes a goal whose conclusion is [T]. *)

val refl : tactic
(** Closes a goal of the form [t = t]. *)

val false_elim : tactic
(** Closes any goal if [F] is among the assumptions. *)

val neg_elim : tactic
(** Closes any goal if both [P] and [~P] appear as assumptions. *)

val noop : tactic
(** Does nothing *)

val sorry : tactic
(** Closes the goal by admitting it as a new axiom. Use to skip a proof
    obligation while developing. {b Unsound}. *)

val intro : tactic
(** Transforms a goal [P ==> Q] into [Q] with [P] added to the assumptions. *)

val conj : tactic
(** Splits a goal [P /\ Q] into subgoals [P] and [Q]. *)

val left : tactic
(** Reduces a goal [P \/ Q] to the subgoal [P]. {b Unsafe}: not complete for
    disjunction. *)

val right : tactic
(** Reduces a goal [P \/ Q] to the subgoal [Q]. {b Unsafe}: not complete for
    disjunction. *)

val or_ : tactic
(** Performs a [Choose] between [left] and [right]. *)

val neg_intro : tactic
(** Transforms a goal [~P] into a subgoal [F] with [P] added to the assumptions.
*)

val elim_conj_asm : tactic
(** Replaces a conjunction [P /\ Q] among the assumptions with [P] and [Q]. *)

val elim_disj_asm : tactic
(** Case-splits on a disjunction [P \/ Q] among the assumptions, producing two
    subgoals. *)

val elim_exists_asm : tactic
(** Eliminates an existential [?x. P x] from the assumptions, introducing a
    fresh witness. The existential is selected via [Choose]. *)

val ccontr : tactic
(** Proof by classical contradiction: reduces a goal [P] to [F] under the added
    assumption [~P]. *)

val gen : tactic
(** Strips a universal quantifier from a goal [!x. P x], leaving the subgoal
    [P x]. *)

val generalize : term -> tactic

val exists : tactic
(** Reduces a goal [?x. P x] to [P t] for a witness [t] chosen via [Choose]. *)

val spec_asm : term -> tactic
(** [spec_asm t] specializes a universally quantified assumption [!x. P x] with
    [t], adding [P t] as a new assumption. The assumption to specialize is
    selected via [Choose]. *)

val sym : tactic
(** Rewrites a goal [l = r] to [r = l]. *)

val sym_asm : tactic
(** Replaces an equality assumption [a = b] (chosen via [Choose]) with [b = a].
*)

val trans : tactic
(** Proves a goal [l = r] by choosing an intermediate term [m] and creating
    subgoals [l = m] and [m = r]. *)

val fun_ext : tactic
(** Reduces a function equality [f = g] to pointwise equality [f x = g x] for a
    fresh [x]. *)

val eq_iff : tactic
(** Reduces a boolean equality [P = Q] to two subgoals: [P] under [Q], and [Q]
    under [P]. *)

val discriminate : tactic
(** Closes a goal by deriving a contradiction from an equality assumption
    between distinct constructors of an inductive type. *)

val show_rewrite_positions : tactic

val rewrite : ?position:int -> tactic
(** Rewrites a subterm of the goal with a theorem chosen from [Rules]. Fails if
    no rewrite makes progress. *)

val rewrite_asm : tactic
(** Rewrites a subterm of an assumption with a theorem chosen from [Rules]. The
    assumption is selected via [Choose]. *)

val beta : tactic
(** Beta-reduces the goal. Fails if no beta redex is found. *)

val beta_asm : tactic
(** Beta-reduces an assumption chosen via [Choose]. *)

val eq_true_asm : tactic
(** For a boolean assumption [P] (not already an equality), adds [P = T] as an
    assumption. *)

val eq_true_elim_asm : tactic
(** For an assumption [P = T], adds [P] as an assumption. *)

val eq_true_elim : tactic
(** Reduces a goal [P = T] to a subgoal [P]. *)

val eq_false_elim : tactic
(** Reduces a goal [P = F] to a subgoal [~P]. *)

val exact : tactic
(** UNDER CONSTRUCTION *)

val apply : tactic
(** Backward chaining. Chooses a theorem from [Rules], strips its outer
    quantifiers, and matches its conclusion against the goal. Each remaining
    premise becomes a subgoal, quantified over variables that matching did not
    determine. *)

val apply_asm : tactic
(** Forward chaining on an assumption. Chooses a theorem from [Rules] and an
    assumption, then matches the theorem's first premise against the assumption.
    The assumption is replaced with the remainder of the theorem, quantified
    over variables that matching did not determine. *)

val apply_asm_to_asm : asm_thm:int -> asm_to:int -> tactic
(** Apply the assumption at index [asm_thm] to the assumption at index [asm_to]
    using [apply_asm] *)

val apply_at : string -> ?target:string -> tactic
(** Smarter version of [apply] that will look up a name in both assumptions and
    proven lemmas, applying the chosen rule to a target assumption, or the goal
    if the target is not provided *)

val rewrite_at : string -> ?target:string -> ?position:int -> tactic
(** Smarter version of [rewrite] that will look up a name in both assumptions
    and proven lemmas, rewriting with the chosen rule at a target assumption, or
    in the goal if the target is not provided *)

val contradict_asm : tactic
(** For a goal [F], finds a negation [~P] among the assumptions (via [Choose])
    and creates a subgoal [P]. *)

val destruct : tactic
(** Case analysis via exhaustiveness. Chooses a term [t] of some inductive or
    boolean type and adds the exhaustiveness disjunction for [t] (e.g.
    [t = C1 \/ ?a. t = C2 a \/ ...]) as an assumption. Follow with
    [elim_disj_asm] and [elim_exists_asm] to split the cases. Unlike [induct],
    produces no induction hypothesis. *)

val induct : tactic
(** Structural induction on an inductive type. For a goal [!x. P x], produces
    one subgoal per constructor. For a goal with a free variable [x], the
    variable is chosen via [Choose], mentioning assumptions are discharged,
    induction runs on the resulting [!x. ...] goal, and the assumptions are
    re-introduced. *)

val have : tactic
(** Chooses a term [p] via [Choose] and produces two subgoals: prove [p] under
    the current assumptions, then prove the original goal with [p] added as an
    assumption. *)

val have_premise : tactic

(** {1 Proof Runner} *)

val prove : ?quiet:bool -> ?name:string -> goal -> tactic -> proof_state
(** Top-level handler that interprets every effect with defaults: [Choose] takes
    the first option, [Rules] is empty, [Register] is ignored, [Trace] prints,
    [Fail] yields [Incomplete], and [Subgoal] yields [Incomplete]. On success,
    registers the resulting theorem under [name] via [Rules.add_proven]. *)

(** {1 Tactic Combinators: Sequencing} *)

val then_one : tactic -> tactic_combinator
(** [then_one t1 t2] runs [t1], then runs [t2] on its first subgoal. Later
    subgoals bubble up. Infix: [>>]. *)

val ( >> ) : tactic -> tactic_combinator

val then_all : tactic -> tactic_combinator
(** [then_all t1 t2] runs [t1], then runs [t2] on every [Subgoal] it emits,
    recursively (subgoals from [t2] are also handled). Infix: [@>>>]. *)

val ( @>>> ) : tactic -> tactic_combinator

val then_all_direct : tactic -> tactic_combinator
(** Like [then_all], but subgoals emitted by [t2] itself bubble up instead of
    being handled. Infix: [@>>]. *)

val ( @>> ) : tactic -> tactic_combinator

val then_each : tactic list -> tactic_combinator
(** [t >>= [t1; t2; ...]] runs [t], then applies [ti] to the [i]th subgoal in
    order. Fails if there are more subgoals than tactics. *)

val ( >>= ) : tactic -> tactic list -> tactic

(** {1 Tactic Combinators: Choice and Search} *)

val with_first : tactic_combinator
(** Handles [Choose] by trying each option in order until one succeeds. Does not
    recurse into nested [Choose] effects; for full search, use [Auto.with_dfs]
    or [Auto.with_best_first]. *)

val with_first_term : tactic_combinator
(** Like [with_first], but only handles [Choose (Term _)]. Other choices pass
    through. *)

val with_term : term -> tactic_combinator
(** [with_term t] resolves any [Choose (Term _)] by returning [t], regardless of
    the offered options. *)

val with_context_terms : tactic_combinator

val try_ : tactic_combinator
(** Converts [Fail] into a [Subgoal] for the current goal, letting a tactic
    sequence continue past a failing step. *)

val pick : tactic list -> tactic
(** Performs a [Choose] among the given tactics and runs the result. *)

val solve : tactic_combinator
(** Requires the wrapped tactic to close the goal completely. Fails on any
    remaining [Subgoal]. *)

val with_repeat : tactic_combinator
(** Runs the wrapped tactic repeatedly until it fails. If progress was made
    before the failure, emits a [Subgoal] for the current state instead of
    failing. *)

(** {1 Tactic Combinators: Interactive and Selection} *)

val with_interactive_choice : tactic_combinator
(** Handles [Choose] by prompting on stdin for an option index. *)

val with_nth_choice : int -> tactic_combinator
(** Resolves every [Choose] by taking its [n]th option. Fails if [n] is out of
    range. *)

val with_named_rule : string list -> tactic_combinator

val with_named_asm_term : string -> tactic_combinator
(** resolves [Choose (Term _)] by finding an assumption matching the given name.
    Fails if the name isn't in the assumptions list *)

val with_nth_term : int -> tactic_combinator
(** Like [with_nth_choice], but only for [Choose (Term _)]. *)

(** {1 Tactic Combinators: Fuel and Tracing} *)

val cost_value : cost -> int
(** Extracts the integer from a [cost]. *)

val with_fuel_limit : int ref -> tactic_combinator
(** Decrements the given counter on each [Register] and raises [Out_of_fuel] if
    it reaches zero. *)

val with_fuel_counter : int ref -> tactic_combinator
(** Increments the given counter on each [Register]. Does not enforce a limit.
*)

val show : tactic
(** Prints the current goal and leaves it open *)

val with_info_trace : tactic_combinator
(** Prints [Info]-level traces to stdout. Other effects pass through. *)

val with_no_automation_trace : tactic_combinator
(** Suppresses [Search]-level traces. *)

val with_no_trace : ?show_proof:bool -> tactic_combinator
(** Suppresses [Debug], [Info], [Warn], and [Error] traces. [Proof] traces pass
    through unless [show_proof:false] is set, in which case they are also
    suppressed. *)

(** {1 Tactic Combinators: Rules} *)

val with_assumptions : tactic_combinator
(** Answers [Rules] with theorems obtained by [assume]-ing each of the goal's
    assumptions. *)

val with_rules : thm list -> tactic_combinator
(** Answers [Rules] with the given list of theorems. *)

val with_axioms : tactic_combinator
(** Answers [Rules] with the systems current axioms. *)

val with_flip_rules : tactic_combinator
(** Re-answers [Rules] with each equation from the outer handler flipped via
    [sym]. Non-equations are dropped. *)

val with_rule : thm -> tactic_combinator
(** Answers [Rules] with a single theorem. *)

val with_definition : string list -> tactic_combinator
(** Answers [Rules] with definitions looked up by name in [Rules.get_def]. Fails
    if any name is unknown. *)

val with_specialized : name:string -> specs:term list -> tactic_combinator
(** Looks up a proven theorem by [name], specializes its outer universal
    quantifiers with [specs] in order, and answers [Rules] with the result.
    Fails if the name is unknown or specialization fails. *)

val with_proven : string list -> tactic_combinator
(** Answers [Rules] with theorems looked up by name in [Rules.get_proven]. Fails
    if any name is unknown. *)

val with_names : string list -> tactic_combinator
(** Handles [Name] by supplying names from the given list in order. When the
    list is exhausted, falls back to auto-generation. *)

val ( @: ) : tactic -> string list -> tactic
val ( /: ) : tactic -> string list -> tactic
val ( @! ) : tactic -> string -> tactic
val ( /! ) : tactic -> string -> tactic
val ( /* ) : tactic -> string -> tactic

val with_rules_and_assumptions : thm list -> tactic_combinator
(** Answers [Rules] with the given theorems together with the goal's assumptions
    (as in [with_assumptions]). *)

(** {1 Simplification and Automation} *)

val intros : tactic
(** Repeatedly applies [intro] or [gen] until neither makes progress. *)

val simp_only : ?with_asms:bool -> tactic

val simp : ?exclude:string list -> ?with_asms:bool -> tactic
(** Repeatedly rewrites the goal using the definitions and simp lemmas
    registered in [Rules], plus any theorems provided by an outer [Rules]
    handler. Also runs [beta], [refl], and [truth]. [exclude] skips definitions
    and simps by name. [with_asms] (default [true]) includes the goal's
    assumptions as rewrites. *)

val auto : tactic
(** Performs a [Choose] among simplification, introduction rules, elimination
    rules, and assumption-apply. Intended to be wrapped with a search
    combinator. *)

val simp_asm :
  ?exclude:string list -> ?with_asms:bool -> ?add:thm list -> tactic
(** Like [simp], but rewrites assumptions instead of the goal. [add] provides
    extra rules. *)

(** {1 Term Synthesis} *)

val with_synthetic_term :
  ?extra:(string * hol_type) list -> int -> tactic_combinator
(** Handles [Choose (Term _)] by enumerating well-typed terms up to the given
    depth (using the type inferred from the current goal) and choosing among
    them. [extra] adds named variables to the enumeration context. *)

(** {1 Proof Execution} *)

val run_proof :
  ?pretty:bool ->
  ?notrace:bool ->
  ?name:string ->
  ?simp:bool ->
  ?quiet:bool ->
  goal ->
  tactic ->
  unit
(** Runs a tactic through [prove] with a fuel limit of 1,000,000, prints the
    result, and reports fuel used. [notrace] (default [true]) wraps the tactic
    in [with_no_trace]. [simp:true] registers a successful proof as a simp lemma
    under [name]. [quiet:true] suppresses all output. *)

open Kernel

(** Tactic engine for interactive theorem proving with algebraic effects. *)

(** {1 Goals and Proof State} *)

type goal = term list * term
(** A list of assumptions and a term to prove under them *)

val make_goal : ?asms:term list -> term -> goal
val pp_goal : Format.formatter -> goal -> unit
val show_goal : goal -> string

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
  | Complete of thm
      (** [proof_state] is used by the ambient handler [prove] to represent the
          result of applying a tactic *)

val pp_proof_state : Format.formatter -> proof_state -> unit
val show_proof_state : proof_state -> string

type tactic = goal -> thm
(** A [tactic] is a function that works on a goal, possibly performing effects
*)

type tactic_combinator = tactic -> tactic
(** A [tactic_combinator] is a function between tactics. It has many uses like
    sequencing tactics ([then_one], [then_all]), handling specific effects
    ([with_no_trace], [with_fuel_limit]), or managing search over a tactics
    choices ([with_dfs], [with_best_first]). *)

type cost = Safe of int | Unsafe of int

(** {1 Choice} *)

type _ choosable =
  | Term : term list -> term choosable
  | Theorem : thm list -> thm choosable
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
  | Subgoal : goal -> thm Effect.t
  | Choose : 'a choosable -> 'a Effect.t
  | Fail : 'a Effect.t
  | Trace : (level * string) -> unit Effect.t
  | Quiet : bool Effect.t
  | Burn : (string * cost) -> unit Effect.t
  | Rules : thm list Effect.t

(** {1 Effect Helpers} *)

val as_chosen_list : 'a choosable -> 'a list
(** Extracts the underlying list from the [choosable] GADT *)

val cost_of_tactic : tactic -> goal -> string * cost
(** Runs a tactic just far enough to extract its name and [Burn] cost. The
    tactic must perform [Burn] as its first effect *)

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

val choose_terms : term list -> term
(** Requests a choice among a list of terms *)

val choose_theorems : thm list -> thm
(** Requests a choice among a list of theorems *)

val choose_tactics : tactic list -> tactic
(** Requests a choice among a list of tactics *)

val choose_unknowns : 'a list -> 'a
(** Requests a choice among a list of unknown type *)

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

val apply_tac : tactic

val apply_asm_tac : tactic
(** Forward reasoning on an assumption. Chooses a theorem from [Rules], strips
    foralls, matches its first premise against a chosen assumption. Replaces the
    chosen assumption with the remainder of the theorem (possibly re-quantified
    over undetermined variables). *)

val apply_neg_asm_tac : tactic
(** Proves [F] by finding a negation [~P] in assumptions and creating a subgoal
    to prove [P]. Fails if the goal is not [F] or no suitable negation exists *)

val sorry_tac : tactic

val sym_tac : tactic
(** Transforms a goal [l = r] into [r = l] *)

val fun_ext_tac : tactic
(** Proves function equality [f = g] by reducing to pointwise equality. Creates
    a subgoal [f x = g x] for a fresh variable [x], then uses [lam] to recover
    the equality. Both lambda and non-lambda terms are handled. *)

val eq_iff_tac : tactic
(** Proves boolean equality [P = Q] by bi-implication. Creates two subgoals:
    prove [P] assuming [Q], and prove [Q] assuming [P]. Combines the results via
    [deduct_antisym_rule]. Fails if the equality is not at type [bool]. *)

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

val spec_asm_tac : term -> tactic
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
    arbitrary bool expressions (via [with_term]), adds [e=T] and [e=F] as
    assumptions *)

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

val prove : ?quiet:bool -> ?name:string -> goal -> tactic -> proof_state
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

val with_first_term : tactic_combinator

val with_term : term -> tactic_combinator
(** Forces a specific term to be chosen when a [Choose (Term _)] effect is
    performed, regardless of whether it appears in the choices *)

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

val with_repeat : tactic_combinator
(** Repeatedly applies a tactic until it fails or makes no progress. On failure
    after progress, emits a subgoal for the current state *)

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

(** {1 Tactic Combinators: Fuel and Tracing} *)

val cost_value : cost -> int
(** Extracts the integer value from a [cost], whether [Safe] or [Unsafe] *)

val with_fuel_limit : int ref -> tactic_combinator
(** Tracks fuel consumption and raises [Out_of_fuel] when the limit is exceeded.
    The limit is a mutable reference that decreases with each [Burn] effect *)

val with_fuel_counter : int ref -> tactic_combinator
(** Tracks total fuel consumed by incrementing a mutable reference for each
    [Burn] effect *)

val show_tac : tactic
(** Prints the current subgoal (assumptions and conclusion) *)

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

val with_rules : thm list -> tactic_combinator
(** Provides a fixed list of theorems when a [Rules] effect is performed *)

val with_flip_rules : tactic_combinator
(** Inverts the direction of all equality rules provided by the outer [Rules]
    handler using [sym] *)

val with_rule : thm -> tactic_combinator
(** Provides a single theorem when a [Rules] effect is performed *)

val with_definition : string list -> tactic_combinator
(** Looks up definitions by name and provides them when a [Rules] effect is
    performed. Fails if any name is not found *)

val with_specialized : name:string -> specs:term list -> tactic_combinator

val with_proven : string list -> tactic_combinator
(** Looks up previously proven theorems by name and provides them when a [Rules]
    effect is performed. Fails if any name is not found *)

val with_rules_and_assumptions : thm list -> tactic_combinator
(** Provides both the given rules and the goal's assumptions as theorems when a
    [Rules] effect is performed *)

(** {1 Simplification and Automation} *)

val intros_tac : tactic
(** Repeatedly applies [intro_tac] and [gen_tac] until neither makes progress.
    Useful for introducing all hypotheses at once *)

val simp_tac : ?exclude:string list -> ?with_asms:bool -> tactic
(** Simplifies the goal using rewrite rules from definitions and registered simp
    lemmas. Set [with_asms:false] to exclude assumptions *)

val auto_tac : tactic
(** Automation tactic combining simplification with basic logical tactics. Use
    with a search combinator for full automation *)

val simp_asm_tac :
  ?exclude:string list -> ?with_asms:bool -> ?add:thm list -> tactic
(** Simplifies assumptions using rewrite rules from definitions. Use [add] to
    provide additional rules. Set [with_asms:false] to exclude other assumptions
    as rewrite rules *)

(** {1 Term Synthesis} *)

val with_synthetic_term :
  ?extra:(string * hol_type) list -> int -> tactic_combinator
(** Handles [Choose (Term _)] effects by enumerating terms of the appropriate
    type up to the given depth, then choosing among them. Use [extra] to provide
    additional variables for synthesis *)

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
(** Runs a proof with fuel tracking and tracing. Prints the resulting theorem
    and fuel usage on success, or the incomplete subgoal on failure. Set
    [simp:true] to register the result as a simp lemma. Set [quiet:true] to
    suppress output *)

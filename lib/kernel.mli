(** A HOL kernel ported from Harrison's HOL Light [fusion.ml]. Inductive type
    definitions are the only kernel extension. *)

(** {1 Types} *)

type hol_type =
  | TyVar of string
  | TyCon of string * hol_type list
      (** A HOL type: either a type variable or a type constructor applied to
          arguments. The function type is encoded as [TyCon ("fun", [a; b])]. *)

val pp_hol_type : Format.formatter -> hol_type -> unit
val show_hol_type : hol_type -> string

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | App of term * term
  | Lam of term * term
      (** A simply-typed lambda term. [Lam (v, body)] requires [v] to be a
          [Var]; the kernel does not enforce this in the type, but constructor
          functions like [make_lam] do. *)

val pp_term : Format.formatter -> term -> unit
val show_term : term -> string

type thm
(** A sequent [{a₁,…,aₙ} ⊢ c]. The constructor is hidden — values of this type
    can only be produced by the primitive inference rules and definition
    mechanisms below. *)

val pp_thm : Format.formatter -> thm -> unit
val show_thm : thm -> string

type constructor_spec = { name : string; arg_types : hol_type list }

val pp_constructor_spec : Format.formatter -> constructor_spec -> unit
val show_constructor_spec : constructor_spec -> string

type inductive_def = {
  ty : hol_type;
  constructors : (string * term) list;
  induction : thm;
  recursion : thm;
  distinct : thm list;
  injective : thm list;
  exhaustiveness : thm;
  match_function : thm;
}
(** Bundle of theorems produced when defining an inductive type. *)

val pp_inductive_def : Format.formatter -> inductive_def -> unit
val show_inductive_def : inductive_def -> string

type kernel_error =
  [ `BadSubstitutionList of (term * term) list
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
  | `NotAConst of term
  | `NotAConstantName of string
  | `NotALam of term
  | `NotAProposition of term
  | `NotAVar of term
  | `NotAnApp of term
  | `NotAnApplication of term
  | `NotBothEquations of thm * thm
  | `NotFreshConstructor of string list
  | `NotPositive of string
  | `NotTrivialBetaRedex of term
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
  | `WrongNumberOfTypeArgs of string
  | `NoRewriteMatch of thm * term ]
(** Closed sum of every error the kernel can return. *)

val pp_kernel_error : Format.formatter -> kernel_error -> unit
val show_kernel_error : kernel_error -> string

(** {1 Global State} *)

val the_type_constants : (string, int) Hashtbl.t
(** Declared type constants, mapped to their arity. *)

val the_term_constants : (string, hol_type) Hashtbl.t
(** Declared term constants, mapped to their generic types. *)

val the_inductives : (string, inductive_def) Hashtbl.t
(** Inductive type definitions registered with the kernel. *)

val the_specifications : (string, thm) Hashtbl.t

val the_axioms : thm list ref
(** Theorems introduced via [new_axiom]. *)

val the_definitions : thm list ref
(** Theorems introduced via [new_basic_definition]. *)

val bool_ty : hol_type
(** The type [bool]. *)

val aty : hol_type
(** The type variable [A]. *)

(** {1 Type Operations} *)

val get_type_arity : string -> int option

val new_type :
  string -> int -> (unit, [> `TypeAlreadyDeclared of string ]) result
(** [new_type name arity] declares a fresh type constant. *)

val make_type :
  string ->
  hol_type list ->
  ( hol_type,
    [> `TypeNotDeclared of string | `WrongNumberOfTypeArgs of string ] )
  result
(** [make_type name args] applies a declared type constructor to [args]. *)

val make_vartype : string -> hol_type
(** [make_vartype name] returns the type variable named [name]. *)

val destruct_type :
  hol_type ->
  (string * hol_type list, [> `TypeVariableNotAConstructor of string ]) result

val destruct_vartype :
  hol_type -> (string, [> `TypeConstructorNotAVariable of string ]) result

val is_type : hol_type -> bool
val is_vartype : hol_type -> bool

val type_vars : hol_type -> hol_type list
(** Returns the type variables occurring in a type, sorted and deduplicated. *)

val type_substitution : (hol_type * hol_type) list -> hol_type -> hol_type
(** [type_substitution [(t₁, α₁); …]] applies a parallel type substitution. The
    substitution is given as [(replacement, target)] pairs. *)

(** {1 Term Operations} *)

val get_const_term_type : string -> hol_type option
(** Returns the generic type of a declared constant. *)

val new_constant :
  string ->
  hol_type ->
  (unit, [> `ConstantTermAlreadyDeclared of string ]) result
(** Declares a fresh term constant with the given (possibly polymorphic) type.
*)

val type_of_term :
  term ->
  ( hol_type,
    [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm of term ] )
  result
(** Computes the type of a well-formed term. *)

val is_var : term -> bool
val is_const : term -> bool
val is_lam : term -> bool
val is_app : term -> bool

val make_var : string -> hol_type -> term
(** [make_var name ty] builds the variable [name : ty]. *)

val make_const :
  string ->
  (hol_type * hol_type) list ->
  (term, [> `NotAConstantName of string ]) result
(** [make_const name theta] looks up [name] and instantiates its generic type
    with the type substitution [theta]. *)

val make_lam : term -> term -> (term, [> `MakeLamNotAVariable of term ]) result
(** [make_lam v body] builds [λv. body]. Fails if [v] is not a variable. *)

val make_app :
  term ->
  term ->
  ( term,
    [> `CantApplyNonFunctionType of term
    | `MakeAppTypesDontAgree of hol_type * hol_type
    | `UnexpectedLambdaForm of term ] )
  result
(** [make_app f x] builds the application [f x], checking that the types agree.
*)

val destruct_var : term -> (string * hol_type, [> `NotAVar of term ]) result
val destruct_const : term -> (string * hol_type, [> `NotAConst of term ]) result
val destruct_app : term -> (term * term, [> `NotAnApp of term ]) result
val destruct_lam : term -> (term * term, [> `NotALam of term ]) result

val frees : term -> term list
(** Free variables of a term, sorted and deduplicated. *)

val frees_in_list : term list -> term list
(** Free variables across a list of terms. *)

val all_frees_within : term list -> term -> bool
(** [all_frees_within bound t] is [true] if every free variable of [t] appears
    in [bound]. *)

val var_free_in : term -> term -> bool
(** [var_free_in v t] is [true] if [v] occurs free in [t]. *)

val type_vars_in_term :
  term -> (hol_type list, [> `UnexpectedLambdaForm of term ]) result

val variant :
  term list ->
  term ->
  (term, [> `CantCreateVariantForNonVariable of term ]) result
(** [variant avoid v] returns a variable with the same type as [v] whose name
    does not clash with any free variable of [avoid], by appending primes. *)

val rev_assoc_default : 'a -> ('b * 'a) list -> default:'b -> 'b
val is_valid_subst_pair : term * term -> bool
val is_valid_substitution : (term * term) list -> bool
val map_results : ('a -> ('b, 'c) result) -> 'a list -> ('b list, 'c) result

val vsubst :
  (term * term) list ->
  term ->
  ( term,
    [> `BadSubstitutionList of (term * term) list
    | `CantCreateVariantForNonVariable of term ] )
  result
(** Capture-avoiding substitution on terms. The substitution is given as
    [(replacement, target)] pairs, where each [target] must be a variable with
    the same type as its [replacement]. *)

val needs_renaming : term -> term -> (term * term) list -> bool

val rator : term -> (term, [> `NotAnApplication of term ]) result
(** Operator of an application: [rator (App (f, x)) = Ok f]. *)

val rand : term -> (term, [> `NotAnApplication of term ]) result
(** Operand of an application: [rand (App (f, x)) = Ok x]. *)

val safe_make_eq :
  term ->
  term ->
  ( term,
    [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm of term ] )
  result
(** Builds the equality [l = r] at the inferred type of [l]. *)

val destruct_eq :
  term -> (term * term, [> `CantDestructEquality of term ]) result

val alpha_compare_var : ('a * 'a) list -> 'a -> 'a -> int
val alpha_compare : (term * term) list -> term -> term -> int

val alphaorder : term -> term -> int
(** Total order on terms modulo alpha-equivalence. *)

val term_union : term list -> term list -> term list
(** Union of two assumption lists, kept sorted by [alphaorder]. *)

val term_remove : term -> term list -> term list
val term_map : (term -> term) -> term list -> term list

(** {1 Sequents} *)

val destruct_thm : thm -> term list * term
(** Returns the assumptions and conclusion of a sequent. *)

val hyp : thm -> term list
(** Assumptions of a sequent. *)

val concl : thm -> term
(** Conclusion of a sequent. *)

(** {1 Primitive Inference Rules}

    The ten rules below are the trusted core of the kernel; every theorem is
    built from these together with axioms and definitions. *)

val refl :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm of term ] )
  result
(** Reflexivity. [refl t] returns [⊢ t = t]. *)

val trans : thm -> thm -> (thm, [> `RuleTrans of thm * thm ]) result
(** Transitivity. From [Γ ⊢ s = t] and [Δ ⊢ t = u], returns [Γ ∪ Δ ⊢ s = u]. *)

val mk_comb :
  thm ->
  thm ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotBothEquations of thm * thm
    | `TypesDontAgree of hol_type * hol_type
    | `UnexpectedLambdaForm of term ] )
  result
(** Congruence for application. From [Γ ⊢ f = g] and [Δ ⊢ x = y], returns
    [Γ ∪ Δ ⊢ f x = g y]. *)

val lam :
  term ->
  thm ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `LamRuleCantApply of term * thm
    | `UnexpectedLambdaForm of term ] )
  result
(** Congruence for abstraction (HOL Light's [ABS]). From [Γ ⊢ s = t], returns
    [Γ ⊢ (λv. s) = (λv. t)], provided [v] is a variable not free in [Γ]. *)

val beta :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotTrivialBetaRedex of term
    | `UnexpectedLambdaForm of term ] )
  result
(** Beta reduction. [beta ((λv. t) v)] returns [⊢ (λv. t) v = t]. Only the
    trivial case where the argument is exactly the bound variable is handled. *)

val assume :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotAProposition of term
    | `UnexpectedLambdaForm of term ] )
  result
(** Assumption. [assume p] returns [{p} ⊢ p]. Fails if [p] is not of type
    [bool]. *)

val eq_mp : thm -> thm -> (thm, [> `EqMp of thm * thm ]) result
(** Equality modus ponens. From [Γ ⊢ p = q] and [Δ ⊢ p], returns [Γ ∪ Δ ⊢ q]. *)

val deduct_antisym_rule :
  thm ->
  thm ->
  ( thm,
    [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm of term ] )
  result
(** From [Γ ⊢ p] and [Δ ⊢ q], returns [(Γ \ {q}) ∪ (Δ \ {p}) ⊢ p = q]. The
    standard idiom is to apply this to [{p} ⊢ q] and [{q} ⊢ p], yielding
    [⊢ p = q]. *)

val type_inst :
  (hol_type * hol_type) list ->
  term ->
  ( term,
    [> `BadSubstitutionList of (term * term) list
    | `CantCreateVariantForNonVariable of term
    | `Clash of term
    | `NotAVar of term ] )
  result
(** Applies a type substitution to every type annotation in a term, renaming
    bound variables when necessary to avoid clashes. *)

val inst_type :
  (hol_type * hol_type) list ->
  thm ->
  ( thm,
    [> `BadSubstitutionList of (term * term) list
    | `CantCreateVariantForNonVariable of term
    | `Clash of term
    | `NotAVar of term ] )
  result
(** Type instantiation (HOL Light's [INST_TYPE]). Applies a type substitution
    throughout the assumptions and conclusion of a theorem. *)

val inst :
  (term * term) list ->
  thm ->
  ( thm,
    [> `BadSubstitutionList of (term * term) list
    | `CantCreateVariantForNonVariable of term ] )
  result
(** Term instantiation (HOL Light's [INST]). Substitutes terms for free
    variables in a theorem. The substitution is given as [(replacement, target)]
    pairs. *)

(** {1 Axioms and Definitions} *)

val new_axiom :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NewAxiomNotAProp of term
    | `UnexpectedLambdaForm of term ] )
  result
(** Postulates a new axiom. The argument must be of type [bool]. The resulting
    theorem is added to [the_axioms]. *)

val subset : 'a list -> 'a list -> bool

val new_basic_definition :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `ConstantTermAlreadyDeclared of string
    | `DefinitionError of string
    | `NewBasicDefinition of term
    | `NewBasicDefinitionAlreadyDefined of string
    | `UnexpectedLambdaForm of term ] )
  result
(** Defines a new constant from an equation [c = t], where [c] is a variable,
    [t] is closed, and the type variables of [t] all appear in the type of [c].
    Declares the constant and returns the defining theorem [⊢ c = t]. *)

val new_basic_type_definition :
  string ->
  string * string ->
  thm ->
  ( thm * thm,
    [> `CantApplyNonFunctionType of term
    | `ConstantTermAlreadyDeclared of string
    | `NotAnApp of term
    | `TypeAlreadyDeclared of string
    | `TypeDefinitionError of string
    | `UnexpectedLambdaForm of term ] )
  result
(** [new_basic_type_definition tyname (abs, rep) (⊢ P x)] introduces a new type
    [tyname] in bijection with the subset of the existing type inhabited by [P],
    along with constants [abs] and [rep] for the two directions. Returns the
    pair

    {[
      ⊢ abs (rep a) = a
      ⊢ P r = (rep (abs r) = r)
    ]} *)

(** {1 Helpers} *)

val make_fun_ty : hol_type -> hol_type -> hol_type
(** [make_fun_ty a b] returns the function type [a -> b]. *)

val type_of_var : term -> hol_type
(** Type of a variable. Raises if the term is not a [Var]. *)

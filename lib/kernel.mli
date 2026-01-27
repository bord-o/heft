type hol_type = TyVar of string | TyCon of string * hol_type list

val pp_hol_type :
  Ppx_deriving_runtime.Format.formatter -> hol_type -> Ppx_deriving_runtime.unit

val show_hol_type : hol_type -> Ppx_deriving_runtime.string

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | App of term * term
  | Lam of term * term

val pp_term :
  Ppx_deriving_runtime.Format.formatter -> term -> Ppx_deriving_runtime.unit

val show_term : term -> Ppx_deriving_runtime.string

type thm

val pp_thm :
  Ppx_deriving_runtime.Format.formatter -> thm -> Ppx_deriving_runtime.unit

val show_thm : thm -> Ppx_deriving_runtime.string

type constructor_spec = { name : string; arg_types : hol_type list }

val pp_constructor_spec :
  Ppx_deriving_runtime.Format.formatter ->
  constructor_spec ->
  Ppx_deriving_runtime.unit

val show_constructor_spec : constructor_spec -> Ppx_deriving_runtime.string

type inductive_def = {
  ty : hol_type;
  constructors : (string * term) list;
  induction : thm;
  recursion : thm;
  distinct : thm list;
  injective : thm list;
}

val pp_inductive_def :
  Ppx_deriving_runtime.Format.formatter ->
  inductive_def ->
  Ppx_deriving_runtime.unit

val show_inductive_def : inductive_def -> Ppx_deriving_runtime.string

type kernel_error =
  [ `BadSubstitutionList
  | `CantApplyNonFunctionType of term
  | `CantCreateVariantForNonVariable of term
  | `CantDestructEquality
  | `Clash of term
  | `ConstantTermAlreadyDeclared of string
  | `ConstructorsAlreadyExist
  | `DefinitionError of string
  | `Eq_MP of term
  | `InvariantViolation of string
  | `LamRuleCantApply
  | `MakeAppTypesDontAgree of hol_type * hol_type
  | `MakeLamNotAVariable of term
  | `NameMappingError of string
  | `NewAxiomNotAProp
  | `NewBasicDefinition of term
  | `NewBasicDefinitionAlreadyDefined of string
  | `NoBaseCase
  | `NotAConst
  | `NotAConstantName of string
  | `NotALam
  | `NotAProposition
  | `NotAVar
  | `NotAnApp
  | `NotAnApplication of term
  | `NotBothEquations
  | `NotFreshConstructor
  | `NotPositive
  | `NotTrivialBetaRedex
  | `RuleTrans
  | `Todo
  | `TypeAlreadyDeclared of string
  | `TypeAlreadyExists
  | `TypeConstructorNotAVariable of string
  | `TypeDefinitionError of string
  | `TypeEquivalenceNotImplemented
  | `TypeNotDeclared of string
  | `TypeVariableNotAConstructor of string
  | `TypesDontAgree
  | `UnexpectedLambdaForm
  | `WrongNumberOfTypeArgs of string ]

val pp_kernel_error :
  Ppx_deriving_runtime.Format.formatter ->
  kernel_error ->
  Ppx_deriving_runtime.unit

val show_kernel_error : kernel_error -> Ppx_deriving_runtime.string
val the_type_constants : (string, int) Hashtbl.t
val the_term_constants : (string, hol_type) Hashtbl.t
val the_inductives : (string, inductive_def) Hashtbl.t
val the_specifications : (string, thm) Hashtbl.t
val the_axioms : thm list ref
val the_definitions : thm list ref
val bool_ty : hol_type
val aty : hol_type
val get_type_arity : string -> int option

val new_type :
  string -> int -> (unit, [> `TypeAlreadyDeclared of string ]) result

val make_type :
  string ->
  hol_type list ->
  ( hol_type,
    [> `TypeNotDeclared of string | `WrongNumberOfTypeArgs of string ] )
  result

val make_vartype : string -> hol_type

val destruct_type :
  hol_type ->
  (string * hol_type list, [> `TypeVariableNotAConstructor of string ]) result

val destruct_vartype :
  hol_type -> (string, [> `TypeConstructorNotAVariable of string ]) result

val is_type : hol_type -> bool
val is_vartype : hol_type -> bool
val type_vars : hol_type -> hol_type list
val type_substitution : (hol_type, hol_type) Hashtbl.t -> hol_type -> hol_type
val get_const_term_type : string -> hol_type option

val new_constant :
  string ->
  hol_type ->
  (unit, [> `ConstantTermAlreadyDeclared of string ]) result

val type_of_term :
  term ->
  ( hol_type,
    [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm ] )
  result

val is_var : term -> bool
val is_const : term -> bool
val is_lam : term -> bool
val is_app : term -> bool
val make_var : string -> hol_type -> term

val make_const :
  string ->
  (hol_type, hol_type) Hashtbl.t ->
  (term, [> `NotAConstantName of string ]) result

val make_lam : term -> term -> (term, [> `MakeLamNotAVariable of term ]) result

val make_app :
  term ->
  term ->
  ( term,
    [> `CantApplyNonFunctionType of term
    | `MakeAppTypesDontAgree of hol_type * hol_type
    | `UnexpectedLambdaForm ] )
  result

val destruct_var : term -> (string * hol_type, [> `NotAVar ]) result
val destruct_const : term -> (string * hol_type, [> `NotAConst ]) result
val destruct_app : term -> (term * term, [> `NotAnApp ]) result
val destruct_lam : term -> (term * term, [> `NotALam ]) result
val frees : term -> term list
val frees_in_list : term list -> term list
val all_frees_within : term list -> term -> bool
val var_free_in : term -> term -> bool

val type_vars_in_term :
  term -> (hol_type list, [> `UnexpectedLambdaForm ]) result

val variant :
  term list ->
  term ->
  (term, [> `CantCreateVariantForNonVariable of term ]) result

val rev_assoc_default : 'a -> ('b * 'a) list -> default:'b -> 'b
val is_valid_subst_pair : term * term -> bool
val is_valid_substitution : (term * term) list -> bool
val map_results : ('a -> ('b, 'c) result) -> 'a list -> ('b list, 'c) result

val vsubst :
  (term * term) list ->
  term ->
  ( term,
    [> `BadSubstitutionList | `CantCreateVariantForNonVariable of term ] )
  result

val needs_renaming : term -> term -> (term * term) list -> bool
val rator : term -> (term, [> `NotAnApplication of term ]) result
val rand : term -> (term, [> `NotAnApplication of term ]) result

val safe_make_eq :
  term ->
  term ->
  (term, [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm ]) result

val destruct_eq : term -> (term * term, [> `CantDestructEquality ]) result
val alpha_compare_var : ('a * 'a) list -> 'a -> 'a -> int
val alpha_compare : (term * term) list -> term -> term -> int
val alphaorder : term -> term -> int
val term_union : term list -> term list -> term list
val term_remove : term -> term list -> term list
val term_map : (term -> term) -> term list -> term list
val destruct_thm : thm -> term list * term
val hyp : thm -> term list
val concl : thm -> term

val refl :
  term ->
  (thm, [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm ]) result

val trans : thm -> thm -> (thm, [> `RuleTrans ]) result

val mk_comb :
  thm ->
  thm ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotBothEquations
    | `TypesDontAgree
    | `UnexpectedLambdaForm ] )
  result

val lam :
  term ->
  thm ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `LamRuleCantApply
    | `UnexpectedLambdaForm ] )
  result

val beta :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotTrivialBetaRedex
    | `UnexpectedLambdaForm ] )
  result

val assume :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NotAProposition
    | `UnexpectedLambdaForm ] )
  result

val eq_mp : thm -> thm -> (thm, [> `Eq_MP of term ]) result

val deduct_antisym_rule :
  thm ->
  thm ->
  (thm, [> `CantApplyNonFunctionType of term | `UnexpectedLambdaForm ]) result

val inst_type :
  (hol_type, hol_type) Hashtbl.t ->
  thm ->
  ( thm,
    [> `BadSubstitutionList
    | `CantCreateVariantForNonVariable of term
    | `Clash of term
    | `NotAVar ] )
  result

val inst :
  (term * term) list ->
  thm ->
  ( thm,
    [> `BadSubstitutionList | `CantCreateVariantForNonVariable of term ] )
  result

val new_axiom :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `NewAxiomNotAProp
    | `UnexpectedLambdaForm ] )
  result

val subset : 'a list -> 'a list -> bool

val new_basic_definition :
  term ->
  ( thm,
    [> `CantApplyNonFunctionType of term
    | `ConstantTermAlreadyDeclared of string
    | `DefinitionError of string
    | `NewBasicDefinition of term
    | `NewBasicDefinitionAlreadyDefined of string
    | `UnexpectedLambdaForm ] )
  result

val new_basic_type_definition :
  string ->
  string * string ->
  thm ->
  ( thm * thm,
    [> `CantApplyNonFunctionType of term
    | `ConstantTermAlreadyDeclared of string
    | `NotAnApp
    | `TypeAlreadyDeclared of string
    | `TypeDefinitionError of string
    | `UnexpectedLambdaForm ] )
  result

val make_fun_ty : hol_type -> hol_type -> hol_type
val type_of_var : term -> hol_type

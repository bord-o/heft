(* lib/printing.ml *)
open Kernel

let rec pretty_print_hol_type = function
  | TyVar name -> name
  | TyCon ("fun", arg_tys) ->
      let args = arg_tys |> List.map pretty_print_hol_type in
      let separated = String.concat " -> " args in
      Format.sprintf "(%s)" separated
  | TyCon (name, []) -> name
  | TyCon (name, arg_tys) ->
      let args = arg_tys |> List.map pretty_print_hol_type in
      let separated = String.concat " " args in
      Format.sprintf "(%s %s)" separated name

(* Precedence levels for smart parenthesization *)
type prec =
  | PrecAtom (* Variables, constants - never need parens *)
  | PrecApp (* Application - needs parens in some contexts *)
  | PrecQuant (* Forall, exists - low precedence *)
  | PrecImp (* Implication - lowest precedence *)

let get_prec = function
  | Var _ | Const _ -> PrecAtom
  | App (Const ("!", _), Lam _) -> PrecQuant
  | App (Const ("?", _), Lam _) -> PrecQuant
  | App (App (Const ("==>", _), _), _) -> PrecImp
  | App _ -> PrecApp
  | Lam _ -> PrecQuant

let rec pretty_print_hol_term ?(with_type = false) ?(parent_prec = PrecImp) term
    =
  let my_prec = get_prec term in
  let aux ?(parent_prec = PrecImp) t =
    pretty_print_hol_term ~with_type ~parent_prec t
  in

  (* Decide if we need parens based on precedence *)
  let needs_parens =
    match (parent_prec, my_prec) with
    | PrecAtom, PrecApp -> true (* App needs parens when used as atomic arg *)
    | PrecAtom, (PrecQuant | PrecImp) -> true
    | PrecApp, (PrecQuant | PrecImp) -> true
    | _, PrecAtom -> false (* Atoms never need parens *)
    | (PrecQuant | PrecImp | PrecApp), _ ->
        false (* Everything else: no parens *)
  in
  let wrap s = if needs_parens then Format.sprintf "(%s)" s else s in

  match term with
  (* Special cases for logical connectives *)
  | App (App (Const ("=", _), l), r) ->
      Format.sprintf "%s = %s"
        (aux ~parent_prec:PrecApp l)
        (aux ~parent_prec:PrecApp r)
  | App (Const ("~", _), p) ->
      Format.sprintf "¬%s" (aux ~parent_prec:PrecAtom p)
  | App (App (Const ("/\\", _), p), q) ->
      Format.sprintf "%s ∧ %s"
        (aux ~parent_prec:PrecApp p)
        (aux ~parent_prec:PrecApp q)
  | App (App (Const ("\\/", _), p), q) ->
      Format.sprintf "%s ∨ %s"
        (aux ~parent_prec:PrecApp p)
        (aux ~parent_prec:PrecApp q)
  | App (App (Const ("==>", _), p), q) ->
      wrap
        (Format.sprintf "%s ==> %s"
           (aux ~parent_prec:PrecApp p)
           (* Force parens on left if it's complex *)
           (aux ~parent_prec:PrecImp q))
  | App (Const ("!", _), Lam (v, body)) ->
      wrap
        (Format.sprintf "∀%s. %s"
           (aux ~parent_prec:PrecAtom v)
           (aux ~parent_prec:PrecQuant body))
  | App (Const ("?", _), Lam (v, body)) ->
      wrap
        (Format.sprintf "∃%s. %s"
           (aux ~parent_prec:PrecAtom v)
           (aux ~parent_prec:PrecQuant body))
  (* Regular cases *)
  | Var (name, ty) when with_type ->
      Format.sprintf "%s:%s" name (pretty_print_hol_type ty)
  | Var (name, _) -> name
  | Const (name, ty) when with_type ->
      Format.sprintf "%s:%s" name (pretty_print_hol_type ty)
  | Const (name, _) -> name
  | App (f, x) ->
      let f_str = aux ~parent_prec:PrecApp f in
      let x_str = aux ~parent_prec:PrecAtom x in
      (* Args need atomic precedence *)
      wrap (f_str ^ " " ^ x_str)
  | Lam (Var (name, ty), body) ->
      let ty_str = if with_type then ":" ^ pretty_print_hol_type ty else "" in
      wrap
        (Format.sprintf "λ%s%s. %s" name ty_str
           (aux ~parent_prec:PrecQuant body))
  | Lam (bind, body) ->
      wrap
        (Format.sprintf "λ%s. %s"
           (aux ~parent_prec:PrecAtom bind)
           (aux ~parent_prec:PrecQuant body))

let pretty_print_thm ?(with_type = false) (Sequent (assm, concl)) =
  let bar = String.make 40 '=' in
  match assm with
  | [] -> Format.sprintf "%s\n%s" bar (pretty_print_hol_term ~with_type concl)
  | _ ->
      let assms =
        List.map (pretty_print_hol_term ~with_type) assm |> String.concat "\n"
      in
      Format.sprintf "%s\n%s\n%s" assms bar
        (pretty_print_hol_term ~with_type concl)

let print_thm th = print_newline @@ print_endline @@ pretty_print_thm th
let print_term trm = print_newline @@ print_endline @@ pretty_print_hol_term trm

let print_error = function
  | `BadSubstitutionList -> "BadSubstitutionList"
  | `CantApplyNonFunctionType _ -> "CantApplyNonFunctionType"
  | `CantCreateVariantForNonVariable _ -> "CantCreateVariantForNonVariable"
  | `CantDestructEquality -> "CantDestructEquality"
  | `Clash _ -> "Clash"
  | `ConstantTermAlreadyDeclared _ -> "ConstantTermAlreadyDeclared"
  | `ConstructorsAlreadyExist -> "ConstructorsAlreadyExist"
  | `DefinitionError _ -> "DefinitionError"
  | `Eq_MP _ -> "Eq_MP"
  | `InvariantViolation _ -> "InvariantViolation"
  | `LamRuleCantApply -> "LamRuleCantApply"
  | `MakeAppTypesDontAgree _ -> "MakeAppTypesDontAgree"
  | `MakeLamNotAVariable _ -> "MakeLamNotAVariable"
  | `NameMappingError _ -> "NameMappingError"
  | `NewAxiomNotAProp -> "NewAxiomNotAProp"
  | `NewBasicDefinition _ -> "NewBasicDefinition"
  | `NewBasicDefinitionAlreadyDefined _ -> "NewBasicDefinitionAlreadyDefined"
  | `NoBaseCase -> "NoBaseCase"
  | `NotAConst -> "NotAConst"
  | `NotAConstantName _ -> "NotAConstantName"
  | `NotALam -> "NotALam"
  | `NotAProposition -> "NotAProposition"
  | `NotAVar -> "NotAVar"
  | `NotAnApp -> "NotAnApp"
  | `NotAnApplication _ -> "NotAnApplication"
  | `NotBothEquations -> "NotBothEquations"
  | `NotFreshConstructor -> "NotFreshConstructor"
  | `NotPositive -> "NotPositive"
  | `NotTrivialBetaRedex -> "NotTrivialBetaRedex"
  | `RuleTrans -> "RuleTrans"
  | `Todo -> "Todo"
  | `TypeAlreadyDeclared _ -> "TypeAlreadyDeclared"
  | `TypeAlreadyExists -> "TypeAlreadyExists"
  | `TypeConstructorNotAVariable _ -> "TypeConstructorNotAVariable"
  | `TypeDefinitionError _ -> "TypeDefinitionError"
  | `TypeEquivalenceNotImplemented -> "TypeEquivalenceNotImplemented"
  | `TypeNotDeclared _ -> "TypeNotDeclared"
  | `TypeVariableNotAConstructor _ -> "TypeVariableNotAConstructor"
  | `TypesDontAgree -> "TypesDontAgree"
  | `UnexpectedLambdaForm -> "UnexpectedLambdaForm"
  | `WrongNumberOfTypeArgs _ -> "WrongNumberOfTypeArgs"
  | `OperationDoesntMatch _ -> "OperationDoesntMatch"
  | `NotAForall -> "NotAForall"
  | `NotANegation -> "NotANegation"
  | `NotAConj -> "NotAConj"
  | `NotADisj -> "NotADisj"
  | `NotAnImp -> "NotAnImp"

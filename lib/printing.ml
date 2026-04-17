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
  | App (Const ("@", _), Lam _) -> PrecQuant
  | App (App (Const ("==>", _), _), _) -> PrecImp
  | App _ -> PrecApp
  | Lam _ -> PrecQuant

(* Try to read a term as a nat numeral: Suc (Suc ... Zero) -> Some n *)
let rec read_nat = function
  | Const ("Zero", _) -> Some 0
  | App (Const ("Suc", _), t) -> Option.map (fun n -> n + 1) (read_nat t)
  | _ -> None

(* Try to read a term as a list: cons x (cons y ... nil) -> Some [x; y; ...] *)
let rec read_list = function
  | Const ("Nil", _) -> Some []
  | App (App (Const ("Cons", _), x), rest) ->
      Option.map (fun xs -> x :: xs) (read_list rest)
  | _ -> None

let rec pretty_print_hol_term ?(with_type = false) ?(pretty = false)
    ?(parent_prec = PrecImp) term =
  let my_prec = get_prec term in
  let aux ?(parent_prec = PrecImp) t =
    pretty_print_hol_term ~with_type ~pretty ~parent_prec t
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

  (* Try pretty-printing rules for nats and lists *)
  if pretty then
    match read_nat term with
    | Some n -> string_of_int n
    | None -> (
        match read_list term with
        | Some elems ->
            let strs = List.map (aux ~parent_prec:PrecImp) elems in
            Format.sprintf "[%s]" (String.concat ", " strs)
        | None ->
            pretty_print_hol_term_inner ~with_type ~pretty ~parent_prec ~wrap
              ~aux term)
  else
    pretty_print_hol_term_inner ~with_type ~pretty ~parent_prec:PrecImp ~wrap
      ~aux term

and pretty_print_hol_term_inner ~with_type ~pretty:_ ~parent_prec:_ ~wrap ~aux
    term =
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
  | App (Const ("@", _), Lam (v, body)) ->
      wrap
        (Format.sprintf "@%s. %s"
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

let pretty_print_thm ?(pretty = false) ?(with_type = false) thm =
  let assm, concl = destruct_thm thm in
  let bar = String.make 40 '=' in
  match assm with
  | [] ->
      Format.sprintf "%s\n%s" bar
        (pretty_print_hol_term ~pretty ~with_type concl)
  | _ ->
      let assms =
        List.map (pretty_print_hol_term ~pretty ~with_type) assm
        |> String.concat "\n"
      in
      Format.sprintf "%s\n%s\n%s" assms bar
        (pretty_print_hol_term ~pretty ~with_type concl)

let print_thm ?(pretty = false) th =
  print_newline @@ print_endline @@ pretty_print_thm ~pretty th

let print_term ?(pretty = false) trm =
  print_newline @@ print_endline @@ pretty_print_hol_term ~pretty trm

let fmt_term = pretty_print_hol_term
let fmt_type = pretty_print_hol_type

let fmt_thm thm =
  let _, c = destruct_thm thm in
  fmt_term c

let print_error = function
  | `BadSubstitutionList pairs ->
      let pp_pair (repl, target) =
        Printf.sprintf "  %s / %s" (fmt_term repl) (fmt_term target)
      in
      Printf.sprintf "BadSubstitutionList:\n%s"
        (String.concat "\n" (List.map pp_pair pairs))
  | `CantApplyNonFunctionType t ->
      Printf.sprintf "CantApplyNonFunctionType: %s" (fmt_term t)
  | `CantCreateVariantForNonVariable t ->
      Printf.sprintf "CantCreateVariantForNonVariable: %s" (fmt_term t)
  | `CantDestructEquality t ->
      Printf.sprintf "CantDestructEquality: %s is not an equality" (fmt_term t)
  | `Clash t -> Printf.sprintf "Clash: %s" (fmt_term t)
  | `ConstantTermAlreadyDeclared s ->
      Printf.sprintf "ConstantTermAlreadyDeclared: %s" s
  | `ConstructorsAlreadyExist names ->
      Printf.sprintf "ConstructorsAlreadyExist: %s" (String.concat ", " names)
  | `DefinitionError s -> Printf.sprintf "DefinitionError: %s" s
  | `EqMp (th1, th2) ->
      Printf.sprintf "EqMp: cannot apply\n  %s\nto\n  %s" (fmt_thm th1)
        (fmt_thm th2)
  | `InvariantViolation s -> Printf.sprintf "InvariantViolation: %s" s
  | `LamRuleCantApply (v, th) ->
      Printf.sprintf "LamRuleCantApply: variable %s in theorem %s" (fmt_term v)
        (fmt_thm th)
  | `MakeAppTypesDontAgree (ty1, ty2) ->
      Printf.sprintf "MakeAppTypesDontAgree: %s != %s" (fmt_type ty1)
        (fmt_type ty2)
  | `MakeLamNotAVariable t ->
      Printf.sprintf "MakeLamNotAVariable: %s" (fmt_term t)
  | `NameMappingError s -> Printf.sprintf "NameMappingError: %s" s
  | `NewAxiomNotAProp t -> Printf.sprintf "NewAxiomNotAProp: %s" (fmt_term t)
  | `NewBasicDefinition t ->
      Printf.sprintf "NewBasicDefinition: %s" (fmt_term t)
  | `NewBasicDefinitionAlreadyDefined s ->
      Printf.sprintf "NewBasicDefinitionAlreadyDefined: %s" s
  | `NoBaseCase tyname ->
      Printf.sprintf "NoBaseCase: type %s has no base case" tyname
  | `NotAConst t -> Printf.sprintf "NotAConst: %s" (fmt_term t)
  | `NotAConstantName s -> Printf.sprintf "NotAConstantName: %s" s
  | `NotALam t -> Printf.sprintf "NotALam: %s" (fmt_term t)
  | `NotAProposition t -> Printf.sprintf "NotAProposition: %s" (fmt_term t)
  | `NotAVar t -> Printf.sprintf "NotAVar: %s" (fmt_term t)
  | `NotAnApp t -> Printf.sprintf "NotAnApp: %s" (fmt_term t)
  | `NotAnApplication t -> Printf.sprintf "NotAnApplication: %s" (fmt_term t)
  | `NotBothEquations (th1, th2) ->
      Printf.sprintf "NotBothEquations:\n  %s\n  %s" (fmt_thm th1) (fmt_thm th2)
  | `NotFreshConstructor names ->
      Printf.sprintf "NotFreshConstructor: %s" (String.concat ", " names)
  | `NotPositive tyname ->
      Printf.sprintf "NotPositive: type %s is not strictly positive" tyname
  | `NotTrivialBetaRedex t ->
      Printf.sprintf "NotTrivialBetaRedex: %s" (fmt_term t)
  | `RuleTrans (th1, th2) ->
      Printf.sprintf "RuleTrans: cannot chain\n  %s\nwith\n  %s" (fmt_thm th1)
        (fmt_thm th2)
  | `TypeAlreadyDeclared s -> Printf.sprintf "TypeAlreadyDeclared: %s" s
  | `TypeAlreadyExists tyname -> Printf.sprintf "TypeAlreadyExists: %s" tyname
  | `TypeConstructorNotAVariable s ->
      Printf.sprintf "TypeConstructorNotAVariable: %s" s
  | `TypeDefinitionError s -> Printf.sprintf "TypeDefinitionError: %s" s
  | `TypeEquivalenceNotImplemented (ty1, ty2) ->
      Printf.sprintf "TypeEquivalenceNotImplemented: %s vs %s" (fmt_type ty1)
        (fmt_type ty2)
  | `TypeNotDeclared s -> Printf.sprintf "TypeNotDeclared: %s" s
  | `TypeVariableNotAConstructor s ->
      Printf.sprintf "TypeVariableNotAConstructor: %s" s
  | `TypesDontAgree (ty1, ty2) ->
      Printf.sprintf "TypesDontAgree: %s != %s" (fmt_type ty1) (fmt_type ty2)
  | `UnexpectedLambdaForm t ->
      Printf.sprintf "UnexpectedLambdaForm: %s" (fmt_term t)
  | `WrongNumberOfTypeArgs s -> Printf.sprintf "WrongNumberOfTypeArgs: %s" s
  | `OperationDoesntMatch op -> Printf.sprintf "OperationDoesntMatch: %s" op
  | `NotAForall t -> Printf.sprintf "NotAForall: %s" (fmt_term t)
  | `NotANegation t -> Printf.sprintf "NotANegation: %s" (fmt_term t)
  | `NotAConj t -> Printf.sprintf "NotAConj: %s" (fmt_term t)
  | `NotADisj t -> Printf.sprintf "NotADisj: %s" (fmt_term t)
  | `NotAnImp t -> Printf.sprintf "NotAnImp: %s" (fmt_term t)
  | `NotAnExists t -> Printf.sprintf "NotAnExists: %s" (fmt_term t)
  | `NoRewriteMatch (rule, tm) ->
      Printf.sprintf "NoRewriteMatch: rule %s does not match %s" (fmt_thm rule)
        (fmt_term tm)
  | `EtaVarFreeInTerm (x, f) ->
      Printf.sprintf "EtaVarFreeInTerm: %s is free in %s" (fmt_term x)
        (fmt_term f)

let rec leaf_type = function
  | TyCon ("fun", [ _; rest ]) -> leaf_type rest
  | ty -> ty

let constructor_arg_types ?(tysub = []) name =
  match get_const_term_type name with
  | Some ty ->
      let rec get_args = function
        | TyCon ("fun", [ arg; rest ]) -> arg :: get_args rest
        | _ -> []
      in
      let args = get_args ty in
      if tysub = [] then args else List.map (type_substitution tysub) args
  | None -> failwith ("Unknown constructor: " ^ name)

let primrec_rec_info ?(tysub = []) con_name ind_ty ret_ty pat_var_names =
  let arg_tys = constructor_arg_types ~tysub con_name in
  let combined = List.combine pat_var_names arg_tys in
  List.filter_map
    (fun (name, ty) ->
      if ty = ind_ty then Some (name, make_var ("_r_" ^ name) ret_ty) else None)
    combined

let wrap_case_lambdas pat_vars r_var_terms non_rec_vars body =
  let lam v acc =
    match make_lam v acc with
    | Ok l -> l
    | Error _ -> failwith "wrap_case_lambdas"
  in
  let term = List.fold_right lam non_rec_vars body in
  let term = List.fold_right lam r_var_terms term in
  List.fold_right lam pat_vars term

let unwrap_term = function
  | Ok (t : term) -> t
  | Error e -> failwith (print_error e)

let unwrap_type = function
  | Ok (t : hol_type) -> t
  | Error e -> failwith (print_error e)

let unwrap_thm = function
  | Ok (t : thm) -> t
  | Error e -> failwith (print_error e)

(* Goal display *)

let () = Fmt_tty.setup_std_outputs ()
let is_auto_name name = String.length name >= 1 && name.[0] = '_'

let hline n =
  let unit = "\xe2\x94\x80" in
  let buf = Buffer.create (n * 3) in
  for _ = 1 to n do
    Buffer.add_string buf unit
  done;
  Buffer.contents buf

let display_goal ?(pretty = false) ((asms, concl) : (string * term) list * term)
    =
  let ppf = Format.std_formatter in
  let pp_term t = pretty_print_hol_term ~pretty t in
  match asms with
  | [] -> Fmt.pf ppf "  %a@." Fmt.(styled `Bold string) (pp_term concl)
  | _ ->
      let max_name_len =
        List.fold_left (fun acc (n, _) -> max acc (String.length n)) 0 asms
      in
      let pad = max max_name_len 1 in
      List.iter
        (fun (name, tm) ->
          let padded = Printf.sprintf "%-*s" pad name in
          if is_auto_name name then
            Fmt.pf ppf "  %a  %s@."
              Fmt.(styled `Faint string)
              padded (pp_term tm)
          else
            Fmt.pf ppf "  %a  %s@."
              Fmt.(styled `Cyan string)
              padded (pp_term tm))
        asms;
      let concl_str = pp_term concl in
      let bar_len = max (pad + 6 + String.length concl_str) 40 in
      Fmt.pf ppf "  %a@." Fmt.(styled `Faint string) (hline bar_len);
      Fmt.pf ppf "  %a@." Fmt.(styled `Bold string) concl_str

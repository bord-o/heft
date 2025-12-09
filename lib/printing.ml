open Kernel

let rec pretty_print_hol_type = function
  | TyVar name -> name
  | TyCon ("fun", arg_tys) ->
      let args = arg_tys |> List.map (fun ty -> pretty_print_hol_type ty) in
      let separated = Util.intercalate " -> " args |> List.fold_left ( ^ ) "" in
      Format.sprintf "(%s)" separated
  | TyCon (name, arg_tys) ->
      let args = arg_tys |> List.map (fun ty -> pretty_print_hol_type ty) in
      let separated = Util.intercalate " " args |> List.fold_left ( ^ ) "" in
      Format.sprintf "%s %s" separated name

let rec pretty_print_hol_term ?(with_type = false) term =
  let aux t = pretty_print_hol_term ~with_type t in
  match (with_type, term) with
  | _, App (App (Const ("=", _), l), r) ->
      Format.sprintf "%s = %s"
        (pretty_print_hol_term ~with_type l)
        (pretty_print_hol_term ~with_type r)
  | true, Var (name, ty) ->
      Format.sprintf "%s : %s" name (pretty_print_hol_type ty)
  | false, Var (name, _ty) -> Format.sprintf "%s" name
  | true, Const (name, ty) ->
      Format.sprintf "%s : %s" name (pretty_print_hol_type ty)
  | false, Const (name, _ty) -> Format.sprintf "%s" name
  | true, App (f, x) -> Format.sprintf "(%s %s)" (aux f) (aux x)
  | false, App (f, x) -> Format.sprintf "(%s %s)" (aux f) (aux x)
  | true, Lam (bind, bod) -> Format.sprintf "(λ%s. %s)" (aux bind) (aux bod)
  | false, Lam (bind, bod) -> Format.sprintf "(λ%s. %s)" (aux bind) (aux bod)

let pretty_print_thm ?(with_type = false) (Sequent (assm, concl)) =
  let bar = "================================" in
  let assms =
    List.map (pretty_print_hol_term ~with_type) assm
    |> Util.intercalate "\n" |> List.fold_left ( ^ ) ""
  in
  let concls = pretty_print_hol_term ~with_type concl in
  Format.sprintf "%s\n\n%s\n\n%s\n" assms bar concls

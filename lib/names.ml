open Kernel

let rec avoid_asms asms n =
  if not (List.mem n asms) then n
  else
    let rec loop i =
      let candidate = n ^ string_of_int i in
      if List.mem candidate asms then loop (i + 1) else candidate
    in
    loop 1

let name_hint (tm : term) : string =
  match tm with
  | App (App (Const ("/\\", _), _), _) -> "conj"
  | App (App (Const ("\\/", _), _), _) -> "disj"
  | App (App (Const ("==>", _), _), _) -> "imp"
  | App (App (Const ("=", _), _), _) -> "eq"
  | App (App (Const (t, _), _), _) -> t
  | App (Const ("~", _), _) -> "neg"
  | App (Const ("!", _), _) -> "all"
  | App (Const ("?", _), _) -> "ex"
  | App (Const (t, _), _) -> t
  | Const (t, _) -> t
  | _ -> ""

let name_asm ?(prefix = "h") ?name (tm : term) (asms : string list) : string =
  match name with Some n -> n | None -> avoid_asms asms (prefix ^ name_hint tm)

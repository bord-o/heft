open Kernel
(* Tactic uses this to initialize rules with different tactics *)

let definitions : (string * thm list) list ref = ref []
let simps : (string * thm list) list ref = ref []
let proven : (string * thm) list ref = ref []

let add_simp name thm =
  match Rewrite.rules_of_def thm with
  | Ok thms -> simps := (name, thms) :: !simps
  | Error _e -> ()

let add_def name thm =
  match Rewrite.rules_of_def thm with
  | Ok thms -> definitions := (name, thms) :: !definitions
  | Error _e -> ()

let add_proven name thm = proven := (name, thm) :: !proven
let get_proven name = List.assoc_opt name !proven
let get_def name = List.assoc_opt name !definitions

let remove_def name =
  definitions := List.filter (fun (n, _) -> n <> name) !definitions

let remove_proven name = proven := List.filter (fun (n, _) -> n <> name) !proven

let find_thm name (asms : (string * term) list) =
  let asm = List.find_opt (fun (n, _) -> n = name) asms in
  match asm with
  | Some (_, asm) -> assume asm |> Result.to_option
  | None -> get_proven name

let find_thms name (asms : (string * term) list) =
  let asm = List.find_opt (fun (n, _) -> n = name) asms in
  match asm with
  | Some (_, asm) -> assume asm |> Result.map List.singleton |> Result.to_option
  | None -> (
      match get_proven name with
      | Some thm -> Some [ thm ]
      | None -> get_def name)

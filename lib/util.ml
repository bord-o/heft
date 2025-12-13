open Result.Syntax

let unwrap = Result.get_ok
let unwrap2 e = e |> Result.get_ok |> Result.get_ok
let unwrap3 e = e |> Result.get_ok |> Result.get_ok |> Result.get_ok

let rec intercalate sep = function
  | [] -> []
  | [ x ] -> [ x ]
  | x :: xs -> x :: sep :: intercalate sep xs

let rec result_of_results acc = function
  | [] -> Ok acc
  | Ok x :: xs -> result_of_results (x :: acc) xs
  | Error e :: _ -> Error e

let rec fold_left_result f acc = function
  | [] -> Ok acc
  | x :: xs ->
      let* acc' = f acc x in
      fold_left_result f acc' xs

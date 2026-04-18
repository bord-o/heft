open Result.Syntax

let rec result_of_results acc = function
  | [] -> Ok acc
  | Ok x :: xs -> result_of_results (x :: acc) xs
  | Error e :: _ -> Error e

let rec fold_left_result f acc = function
  | [] -> Ok acc
  | x :: xs ->
      let* acc' = f acc x in
      fold_left_result f acc' xs

open Sexplib

let () =
  let open In_channel in
  let args = Sys.argv in
  if Array.length args <> 2 then failwith "holinone <FILE>"
  else
    with_open_text (Array.get args 1) @@ fun ic ->
    let text = input_all ic in
    let sexps = Sexp.of_string_many text in
    sexps |> List.iter @@ fun s -> Sexp.pp Format.std_formatter s

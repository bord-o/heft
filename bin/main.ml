open Holinone

let () =
  let open In_channel in
  let args = Sys.argv in
  if Array.length args <> 2 then failwith "holinone <FILE>"
  else
    with_open_text (Array.get args 1) @@ fun ic ->
    let text = input_all ic in
    elaborate text

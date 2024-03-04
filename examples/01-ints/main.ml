external get_int : unit -> int = "caml_get_int"
external print_int : int -> unit = "caml_my_print_int"

let () =
  let x = get_int () in
  Printf.printf "from ml: %d\n" x;
  print_int x

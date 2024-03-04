type c_pair

external mkpair : unit -> c_pair = "caml_mkpair"
external set_x : c_pair -> int -> unit = "caml_set_x"
external set_y : c_pair -> int -> unit = "caml_set_y"
external get_x : c_pair -> int = "caml_get_x"
external get_y : c_pair -> int = "caml_get_y"

let () =
  let p = mkpair () in
  set_x p 1; set_y p 2;
  assert (get_x p = 1);
  assert (get_y p = 2);
  print_endline "OK"

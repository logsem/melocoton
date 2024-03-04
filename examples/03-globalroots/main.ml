(* this is an ugly API *)
external init_storage : unit -> unit = "caml_init_storage"
external store_string : string -> unit = "caml_store_string"
external retrieve_string : unit -> string = "caml_retrieve_string"

let () =
  init_storage ();
  assert (retrieve_string () = "");
  (* make s a dynamically allocated string *)
  let s = Bytes.to_string (Bytes.of_string "abcdef") in
  Gc.finalise (fun _ -> print_endline "string got GC'd") s;
  store_string s;
  Gc.full_major ();
  print_endline (retrieve_string ())

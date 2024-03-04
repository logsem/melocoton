external twice : ('a -> unit) -> 'a -> unit = "caml_twice"
external twice_catch : ('a -> unit) -> 'a -> unit = "caml_twice_catch"

exception MyExn

let () =
  Callback.register_exception "myexn" MyExn

let () =
  twice print_endline "hello";
  (* with caml_callback, exceptions skip over the C code *)
  (try twice (fun _ -> raise Exit) 0
   with Exit -> print_endline "raised Exit");
  (* caml_callback_exn allows catching exceptions in the C code *)
  twice_catch (
    let r = ref false in
    fun _ ->
      if !r then raise Exit
      else (r := true; raise MyExn)
  ) 0

(*
  let swap_pair (a, b) = (b, a)
*)
external swap_pair : ('a * 'b) -> ('b * 'a) = "caml_swap_pair"

let () =
  let (b, a) = swap_pair ("a", "b") in
  Printf.printf "(a, b) -> (%s, %s)\n" b a

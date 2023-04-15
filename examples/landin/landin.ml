
external callk : ('a -> 'b) ref -> 'a -> 'b = "callk"
let knot (f : ('a -> 'b) -> ('a -> 'b)) =
  let l = ref (fun _ -> assert false) in
  l := (fun x -> f (fun y -> (callk l y)) x);
  (fun x -> callk l x)
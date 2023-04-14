
external callk : ('a -> 'b) ref -> 'a -> 'b = "callk"
let knot (f : ('a -> 'b) -> ('a -> 'b)) =
  let l = ref (fun x -> Obj.magic x) in (* use of Obj.magic here is to quiet the type checker -- it is never executed *)
  l := (fun x -> f (fun y -> (callk l y)) x);
  (fun x -> callk l x)
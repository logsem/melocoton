type t

val init : (int (* index *) -> int (* byte *)) -> int (* length *) -> t
val free : t -> unit

(* returns [None] if the underlying buffer has been deallocated using [free],
   and [Some hash] otherwise. *)
val hash : t -> int option

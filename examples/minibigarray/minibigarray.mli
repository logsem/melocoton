type t

val init : (int (* index *) -> int (* byte *)) -> int (* length *) -> t
val free : t -> unit

(* Returns [Ok hash] or [Error ()] if the underlying buffer has been deallocated
   using [free]. *)
val hash : t -> (int, unit) Result.t

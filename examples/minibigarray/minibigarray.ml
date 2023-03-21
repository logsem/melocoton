(* Abstract type representing the foreign blocks created in C pointing to the C
   buffer. Manipulating those requires knowing their length on the side; thus
   they are type unsafe in general, and will not be exposed to the user
   directly. *)
type buffer

external buffer_init : (int (* index *) -> int (* byte *)) -> int (* length *) -> buffer
  = "caml_miniba_init"

external buffer_free : buffer -> unit
  = "caml_miniba_free"

external buffer_hash : buffer -> int (* length *) -> int option (* hash *)
  = "caml_miniba_hash"



(* Type-safe API built on top of unsafe buffers *)
(* NB: if we additionally want slices then we need to add an "offset" parameter
   to [buffer_hash]. *)

type t = { buf : buffer; len : int }

let init f len =
  let buf = buffer_init f len in
  { buf; len }

let free ba =
  buffer_free ba.buf

let hash ba =
  buffer_hash ba.buf ba.len

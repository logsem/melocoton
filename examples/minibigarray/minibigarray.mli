type buf


val buf_alloc  : int -> buf
val buf_free   : buf -> unit
val buf_get    : buf -> int -> char
val buf_upd    : int -> int -> (int -> char) -> buf -> unit

val wrap_compress               : buf -> buf -> bool
val wrap_max_len  : int -> int

val is_compressible : char array -> bool

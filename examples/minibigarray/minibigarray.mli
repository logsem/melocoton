type buf


val buf_alloc  : int -> buf   
val buf_free   : buf -> unit                             
val buf_get    : buf -> int -> char                      
val buf_upd    : int -> int -> (int -> char) -> buf -> unit 

val snappy_compress               : buf -> buf -> bool     
val snappy_max_compressed_length  : int -> int            

val is_compressible : char array -> bool

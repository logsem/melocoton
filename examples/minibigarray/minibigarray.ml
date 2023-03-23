
type bytes
type buf = { contents: bytes; mutable used: int; cap : int }
external buf_alloc     : int -> buf                                   = "buf_alloc"
external buf_free      : buf -> unit                                  = "buf_free"
(* external buf_get       : buf -> int -> char                           = "buf_get" *)
external buf_upd       : int -> int -> (int -> char) -> buf -> unit   = "buf_upd"
external buf_compress  : buf -> buf -> bool                           = "buf_compress"

let is_compressable (xs: char array) =
  let len = Array.length xs in let (inp, outp) = (buf_alloc len, buf_alloc len) in
  buf_upd 0 (len - 1) (fun i -> Array.get xs i) inp;
  let succ = buf_compress inp outp in let shrink = succ && (outp.used < inp.used) in
  buf_free inp; buf_free outp; shrink

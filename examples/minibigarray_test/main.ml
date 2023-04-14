module Ba = Minibigarray
module La = Landin
open Char
let fib fibr n = if n < 2 then n else fibr (n-1) + fibr (n-2)
let () =
  let iscomp1 = Ba.is_compressible (Array.init 255 (fun _ -> chr 0)) in
  Printf.printf "\n\ncompressible 1 > %b\n" iscomp1;
  let iscomp2 = Ba.is_compressible (Array.init 255 (fun x -> chr x)) in
  Printf.printf "compressible 2 > %b\n" iscomp2;
  let iscomp3 = Ba.is_compressible (Array.init 1 (fun x -> chr x)) in
  Printf.printf "compressible 3 > %b\n" iscomp3;
  let fib10 = La.knot fib 10 in
  Printf.printf "fib 10 = %d\n" fib10;
  ()
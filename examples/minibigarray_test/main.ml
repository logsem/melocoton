module Ba = Minibigarray
open Char
let () =
  let iscomp1 = Ba.is_compressable (Array.init 255 (fun _ -> chr 0)) in
  Printf.printf "\n\ncompressible 1 > %b\n" iscomp1;
  let iscomp2 = Ba.is_compressable (Array.init 255 (fun x -> chr x)) in
  Printf.printf "compressible 2 > %b\n" iscomp2;
  let iscomp3 = Ba.is_compressable (Array.init 1 (fun x -> chr x)) in
  Printf.printf "compressible 3 > %b\n" iscomp3;
  ()
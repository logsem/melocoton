module Ba = Minibigarray

let () =
  (* [1; 2; ...] *)
  let ba = Ba.init (fun i -> i+1) 10 in
  begin match Ba.hash ba with
  | None -> Printf.printf "<deallocated>\n"
  | Some h -> Printf.printf "hash> %d\n" h
  end;
  Ba.free ba;
  begin match Ba.hash ba with
  | None -> Printf.printf "<deallocated>\n"
  | Some h -> Printf.printf "hash> %d\n" h
  end

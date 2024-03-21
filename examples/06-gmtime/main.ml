external gmtime  : float -> Unix.tm = "caml_gmtime"

let () =
  let my_res : Unix.tm = gmtime (Unix.time ()) in
  Format.printf "Custom gmtime : %d/%d/%d %d:%d:%d\n"
  my_res.tm_year my_res.tm_mon my_res.tm_mday
  my_res.tm_hour my_res.tm_min my_res.tm_sec;

  let res : Unix.tm = Unix.gmtime (Unix.time ()) in
  Format.printf "Unix.gmtime   : %d/%d/%d %d:%d:%d\n"
  res.tm_year res.tm_mon res.tm_mday
  res.tm_hour res.tm_min res.tm_sec

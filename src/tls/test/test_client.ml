(* Main driver for interop tests *)

let _ =
  if (Array.length Sys.argv <> 3) then
     TestClient.main "openssl.org" 443
  else 
     TestClient.main Sys.argv.(1) (int_of_string Sys.argv.(2))

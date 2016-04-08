(* Main driver for interop tests *)

let _ =
  if (Array.length Sys.argv <> 4) then
     print_string "Usage: ./client.out <1.2|1.3> <host> <port>\n"
  else 
     if (Sys.argv.(1) = "1.3") then
        TestClient13.main Sys.argv.(2) (int_of_string Sys.argv.(3))
     else 
        TestClient.main Sys.argv.(2) (int_of_string Sys.argv.(3))

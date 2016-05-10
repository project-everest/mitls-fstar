(* Main driver for interop tests *)

let _ =
  if (Array.length Sys.argv <> 4) then
     print_string "Usage: ./server.out <1.2|1.3> <binding> <port>\n"
  else 
     if (Sys.argv.(1) = "1.3") then
       TestServer13.main Sys.argv.(2) (int_of_string Sys.argv.(3))
     else
       TestServer.main Sys.argv.(2) (int_of_string Sys.argv.(3))

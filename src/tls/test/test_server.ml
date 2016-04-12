(* Main driver for interop tests *)

let _ =
  if (Array.length Sys.argv <> 3) then
     print_string "Usage: ./server.out <binding> <port>\n"
  else 
     TestServer.main Sys.argv.(1) (int_of_string Sys.argv.(2))

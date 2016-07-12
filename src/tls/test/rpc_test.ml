open RPC

let args = ref []

let role = ref Client

let fork = ref true

let help = "An RPC test application.\n\n"

let _ =
  Arg.parse [
      ("-fork", Arg.Unit (fun () -> fork := true), "run client and server");
      ("-c", Arg.Unit (fun () -> role := Client), "run as client");
      ("-s", Arg.Unit (fun () -> role := Server), "run as server");
    ] (fun s -> args := s :: !args) help;;

  let (host, port) = match List.rev !args with
    | _ -> "127.0.0.1", 6666 in

  let client, server = start () in
  if !fork then
    let pid = Unix.fork () in
    if pid = 0 then
      RPC.run Client client host port
    else
      RPC.run Server server host port
  else
    match !role with
    | Client -> RPC.run Client client host port
    | Server -> RPC.run Server server host port

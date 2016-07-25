type callbacks = int
external ocaml_send_tcp: callbacks -> string -> int = "ocaml_send_tcp"
external ocaml_recv_tcp: callbacks -> string -> int = "ocaml_recv_tcp"

(*module FFICallbacks = struct *)
  let recvcb sock maxlen =
      let str = Bytes.create maxlen in
      let recvlen = ocaml_recv_tcp sock str in
      if recvlen < 0 then 
        (0, "")
      else
        let str = String.sub str 0 recvlen in
        (1, str)
(* end *)

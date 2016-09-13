type callbacks = Z.t
external _ocaml_send_tcp: callbacks -> string -> int = "ocaml_send_tcp"
external _ocaml_recv_tcp: callbacks -> string -> int = "ocaml_recv_tcp"

let ocaml_send_tcp cb b = _ocaml_send_tcp cb b |> Z.of_int
let ocaml_recv_tcp cb b = _ocaml_recv_tcp cb b |> Z.of_int

(*module FFICallbacks = struct *)
  let recvcb sock maxlen =
      let str = Bytes.create (Z.to_int maxlen) in
      let recvlen = _ocaml_recv_tcp sock str in
      if recvlen < 0 then
        (false, "")
      else
        let str = String.sub str 0 recvlen in
        (true, str)
(* end *)

type callbacks = int
external ocaml_send_tcp2: callbacks -> string -> int = "ocaml_send_tcp"
external ocaml_recv_tcp2: callbacks -> string -> int = "ocaml_recv_tcp"

let ocaml_send_tcp callbacks b = ocaml_send_tcp2 callbacks b
let ocaml_recv_tcp callbacks b = ocaml_recv_tcp2 callbacks b


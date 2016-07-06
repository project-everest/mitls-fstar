type cookie = int
external ocaml_send_tcp2: cookie -> string -> int = "ocaml_send_tcp"
external ocaml_recv_tcp2: cookie -> string -> int = "ocaml_recv_tcp"

let ocaml_send_tcp cookie b = ocaml_send_tcp2 cookie b
let ocaml_recv_tcp cookie b = ocaml_recv_tcp2 cookie b


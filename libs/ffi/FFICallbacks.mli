type callbacks = int64

val ocaml_ticket_cb: callbacks -> callbacks -> string -> string -> string -> unit
val ocaml_send_tcp: callbacks -> string -> Z.t
val ocaml_recv_tcp: callbacks -> string -> Z.t

val recvcb: callbacks -> Z.t -> (bool * string)

type callbacks = Z.t
val ocaml_send_tcp: callbacks -> string -> Z.t
val ocaml_recv_tcp: callbacks -> string -> Z.t

val recvcb: callbacks -> Z.t -> (bool * string)

type callbacks = int64

val ocaml_ticket_cb: callbacks -> callbacks -> string -> string -> string -> unit

val ocaml_cert_select_cb: callbacks -> callbacks -> string -> string -> (callbacks * int) option
val ocaml_cert_format_cb: callbacks -> callbacks -> callbacks -> string
val ocaml_cert_sign_cb: callbacks -> callbacks -> callbacks -> int -> string -> string option
val ocaml_cert_verify_cb: callbacks -> callbacks -> string -> int -> string*string -> bool

val ocaml_send_tcp: callbacks -> string -> Z.t
val ocaml_recv_tcp: callbacks -> string -> Z.t

val recvcb: callbacks -> Z.t -> (bool * string)

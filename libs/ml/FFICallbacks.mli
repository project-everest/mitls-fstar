type callbacks = int
val ocaml_send_tcp: callbacks -> string -> int
val ocaml_recv_tcp: callbacks -> string -> int

val recv: callbacks -> int -> (string, Platform.Bytes.bytes) Platform.Error.optResult 

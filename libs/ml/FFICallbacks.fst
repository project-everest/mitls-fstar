module FFICallbacks

open Platform.Bytes

type cookie = Prims.int

assume val ocaml_send_tcp: cookie -> cbytes -> Tot int
assume val ocaml_recv_tcp: cookie -> cbytes -> Tot int

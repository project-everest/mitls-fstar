module FFICallbacks

open Platform.Bytes

type callbacks = Prims.int

assume val ocaml_send_tcp: callbacks -> cbytes -> Tot int
assume val ocaml_recv_tcp: callbacks -> cbytes -> Tot int

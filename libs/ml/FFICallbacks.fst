module FFICallbacks

open Platform.Bytes

type callbacks = Prims.int

assume val ocaml_send_tcp: callbacks -> cbytes -> Tot int
assume val ocaml_recv_tcp: callbacks -> cbytes -> Tot int

(* under the covers, recv invokes String.Substring, which may throw an exception
   due to invalid parameters.  But the recv codepath never does that.  However,
   The F* compiler does not know that.  So implement FFI recv in ML to avoid
   exposing the String.Substring call to effects checking.  Same as
   Platform.Tcp.recv *)
assume val recvcb: callbacks -> max:nat -> Platform.Tcp.EXT (result:nat * b:cbytes {length (abytes b) <= max})

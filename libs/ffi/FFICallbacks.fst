module FFICallbacks

open FStar.Bytes

type callbacks = UInt64.t

type cb_state = callbacks
type cb_fun_ptr = callbacks

type sigalg = FStar.UInt16.t
type cert_ptr = callbacks

assume val ocaml_send_tcp: cb_state -> string -> Tot int
assume val ocaml_recv_tcp: cb_state -> string -> Tot int

// Ticket callback
assume val ocaml_ticket_cb: cb_state -> cb_fun_ptr -> string -> bytes -> bytes -> EXT unit

// Certificate callbacks
assume val ocaml_cert_select_cb: cb_state -> cb_fun_ptr -> pv:int -> sni:string * alpn:bytes -> sigalgs:bytes -> EXT (option (cert_ptr * sigalg))
assume val ocaml_cert_format_cb: cb_state -> cb_fun_ptr -> cert_ptr -> EXT bytes
assume val ocaml_cert_sign_cb: cb_state -> cb_fun_ptr -> cert_ptr -> sigalg -> tbs:bytes -> EXT (option bytes)
assume val ocaml_cert_verify_cb: cb_state -> cb_fun_ptr -> bytes -> sigalg -> tbs:bytes * sigv:bytes -> EXT bool

(* under the covers, recv invokes String.Substring, which may throw an exception
   due to invalid parameters.  But the recv codepath never does that.  However,
   The F* compiler does not know that.  So implement FFI recv in ML to avoid
   exposing the String.Substring call to effects checking.  Same as
   Platform.Tcp.recv *)
assume val recvcb: callbacks -> max:nat -> EXT (result:bool * b:string {length (bytes_of_string b) <= max})

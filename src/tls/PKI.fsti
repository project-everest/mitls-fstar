module PKI

// This module is implemented natively

open FStar.HyperStack.ST
open TLS.Callbacks
val init: 
  cafile:string -> 
  server_certs:list (string * string * bool) -> context
val tls_callbacks: context -> St cert_cb
val free: context -> St unit

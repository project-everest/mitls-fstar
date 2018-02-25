module PKI

// This module is implemented natively

open TLSConstants

val init: cafile:string -> server_certs:list (string * string * bool) -> St FStar.Dyn.dyn
val tls_callbacks: FStar.Dyn.dyn -> St cert_cb
val free: FStar.Dyn.dyn -> St unit

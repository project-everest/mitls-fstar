let init (_: string) (_: (string * string * bool) list): FStar_Dyn.dyn =
  failwith "Not implemented: PKI.init"

let tls_callbacks (_: FStar_Dyn.dyn): TLSConstants.cert_cb =
  failwith "Not implemented: PKI.tls_callbacks"

let free (_: FStar_Dyn.dyn): unit =
  failwith "Not implemented: PKI.free"

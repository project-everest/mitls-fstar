type callbacks = int64

external ocaml_ticket_cb: callbacks -> callbacks -> string -> string -> string -> unit = "ocaml_ticket_cb"

external ocaml_cert_select_cb: callbacks -> callbacks -> string -> string -> (callbacks * int) option = "ocaml_cert_select_cb"
external ocaml_cert_format_cb: callbacks -> callbacks -> callbacks -> string = "ocaml_cert_format_cb"
external ocaml_cert_sign_cb: callbacks -> callbacks -> callbacks -> int -> string -> string option = "ocaml_cert_sign_cb"
external ocaml_cert_verify_cb: callbacks -> callbacks -> string -> int -> string*string -> bool = "ocaml_cert_verify_cb"

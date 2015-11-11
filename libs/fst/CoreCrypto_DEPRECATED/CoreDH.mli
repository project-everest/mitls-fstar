(* -------------------------------------------------------------------- *)
open Bytes
open CoreKeys

(* -------------------------------------------------------------------- *)
type skey = dhskey
type pkey = dhpkey

(* -------------------------------------------------------------------- *)
val check_element: bytes -> bytes -> bytes -> bool
val check_params: bytes -> bytes -> bool
val gen_params : unit -> CoreKeys.dhparams
val gen_key    : dhparams -> skey * pkey
val agreement  : dhparams -> dhsbytes -> dhpbytes -> bytes

(* -------------------------------------------------------------------- *)
val save_params_to_file   : string -> dhparams -> bool
val load_params_from_file : string -> dhparams option
val load_default_params   : unit -> dhparams

module CoreCrypto.DH

open Platform.Bytes
open Platform.Error
open CoreCrypto.Keys
open CoreCrypto.DHDB

assume val defaultPQMinLength: nat * nat

(* ------------------------------------------------------------------------ *)
assume val check_p_g: nat -> nat -> nat -> bytes -> bytes -> optResult string bytes 
assume val check_p_g_q: nat -> nat -> nat -> bytes -> bytes -> bytes -> optResult string bool

(* ------------------------------------------------------------------------ *)
assume val check_params :  dhdb -> nat -> (nat * nat) -> bytes -> bytes -> optResult string (dhdb*dhparams)
assume val check_element: dhparams -> bytes -> bool
assume val gen_key      : dhparams -> (dhskey * dhpkey)
// less efficient implementation, in case q is not available
assume val gen_key_pg   : bytes -> bytes -> (dhskey * dhpkey)
assume val agreement    : bytes -> dhskey -> dhpkey -> bytes

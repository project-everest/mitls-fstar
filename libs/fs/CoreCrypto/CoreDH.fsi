(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreDH

open Bytes
open Error
open CoreKeys
open DHDB

val defaultPQMinLength: (nat*nat)

(* ------------------------------------------------------------------------ *)
val check_p_g: nat -> nat -> nat -> bytes -> bytes -> optResult<string,bytes>
val check_p_g_q: nat -> nat -> nat -> bytes -> bytes -> bytes -> optResult<string,bool>

(* ------------------------------------------------------------------------ *)
val check_params : dhdb -> nat -> nat * nat -> bytes -> bytes -> optResult<string,dhdb*dhparams>
val check_element: dhparams -> bytes -> bool
val gen_key      : dhparams -> dhskey * dhpkey
// less efficient implementation, in case q is not available
val gen_key_pg   : bytes -> bytes -> dhskey * dhpkey
val agreement    : bytes -> dhskey -> dhpkey -> bytes

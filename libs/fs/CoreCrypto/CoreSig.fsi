(* STATUS : JK : removed effects to be able to compile in F# *)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreSig
open Bytes

(* ------------------------------------------------------------------------ *)
type sighash =
| SH_MD5
| SH_SHA1
| SH_SHA256
| SH_SHA384

type sigalg =
| CORE_SA_RSA
| CORE_SA_DSA
| CORE_SA_ECDSA

(* ------------------------------------------------------------------------ *)
type sigskey =
| SK_RSA of CoreKeys.rsaskey
| SK_DSA of CoreKeys.dsaskey
| SK_ECDH of CoreKeys.ecdhskey

type sigpkey =
| PK_RSA of CoreKeys.rsapkey
| PK_DSA of CoreKeys.dsapkey
| PK_ECDH of CoreKeys.ecdhpkey

val sigalg_of_skey : sigskey -> sigalg
val sigalg_of_pkey : sigpkey -> sigalg

(* ------------------------------------------------------------------------ *)
type text = bytes
type sigv = bytes

val gen    : sigalg -> (sigpkey * sigskey) //Dv (sigpkey * sigskey)
val sign   : sighash option -> sigskey -> text -> sigv //Dv sigv (* FIXME! *)
val verify : sighash option -> sigpkey -> text -> sigv -> bool //Tot bool

(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Sig

open Bytes
open TLSConstants

(* ------------------------------------------------------------------------ *)
type alg   = sigHashAlg //MK: now defined in TLSConstants.fs7: sigAlg * hashAlg

type text = bytes
type sigv = bytes 

(* ------------------------------------------------------------------------ *)
type skey
type pkey

val strong : alg -> bool // JK : removed Tot effect for F# compilation 
val honest: alg -> pkey -> bool

val create_pkey: alg -> CoreSig.sigpkey -> pkey

//MK: why are these functions needed, alg is known from the index?
val sigalg_of_skeyparams : CoreSig.sigskey -> sigAlg 
val sigalg_of_pkeyparams : CoreSig.sigpkey -> sigAlg

(* ------------------------------------------------------------------------ *)
                        
val gen    : alg -> pkey * skey
val sign   : alg -> skey -> text -> sigv
val verify : alg -> pkey -> text -> sigv -> bool
val coerce : alg -> pkey -> CoreSig.sigskey -> skey
val leak   : alg -> skey -> CoreSig.sigskey

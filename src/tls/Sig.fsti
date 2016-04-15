(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Sig

open Platform.Bytes
open TLSConstants

(* ------------------------------------------------------------------------ *)
type alg   = sigHashAlg //MK: now defined in TLSConstants.fst: sigAlg * hashAlg'

type text = bytes
type sigv = bytes 

(* ------------------------------------------------------------------------ *)
type skey
type pkey

val strong: alg -> Tot bool 
val honest: alg -> pkey -> bool

val create_pkey: alg -> CoreCrypto.Sig.sigpkey -> pkey

//MK: why are these functions needed, alg is known from the index?
val sigalg_of_skeyparams : CoreCrypto.Sig.sigskey -> sigAlg 
val sigalg_of_pkeyparams : CoreCrypto.Sig.sigpkey -> sigAlg

(* ------------------------------------------------------------------------ *)
                        
val gen    : alg -> pkey * skey
val sign   : alg -> skey -> text -> sigv
val verify : alg -> pkey -> text -> sigv -> bool
val coerce : alg -> pkey -> CoreCrypto.Sig.sigskey -> skey
val leak   : alg -> skey -> CoreCrypto.Sig.sigskey

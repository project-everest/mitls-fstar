(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Sig

open Platform.Bytes
open CoreCrypto

open TLSConstants

(* ------------------------------------------------------------------------ *)
type alg = sigHashAlg //defined in TLSConstants 

type text = bytes
type sigv (a:alg) = bytes



type pkey (a:alg) = { pkey : pkeyparams * hashAlg } (* private type *)
type skey (a:alg) = { skey : skeyparams * hashAlg; pub : pkey a } (*private type*)



(*MK: also defined in TLSConstants.fst, but not for ECDH
let sigalg_of_skeyparams sk =
    match sk with
    | SK_RSA (_,_) -> SA_RSA
    | SK_DSA (_,_) -> SA_DSA
    | SK_ECDH _ -> SA_ECDSA

let sigalg_of_pkeyparams pk =
    match pk with
    | PK_RSA (_,_) -> SA_RSA
    | PK_DSA (_,_) -> SA_DSA
    | PK_ECDH _ -> SA_ECDSA
 *)

let strong = function
  | SA_DSA,SHA384 -> true
  | _ -> false

let honest (a:alg) (pk:pkey a) : bool = false

let sign (a: alg) (sk: skey a) (t: text): sigv a =
    let asig, ahash = a in
    let (kparams, khash) = sk.skey in

    if ahash <> khash then
        Error.unexpected "Sig.sign: key requires different sig-algo"
//            (sprintf "Sig.sign: requested sig-hash = %A, but key requires %A"
//                ahash khash)

    else
    if asig <> TLSConstants.sigalg_of_skeyparams kparams then

        Error.unexpected "Sig.sign: key requires different sig-algo"
//            (sprintf "Sig.sign: requested sig-algo = %A, but key requires %A"
//                asig (sigalg_of_skeyparams kparams))


    else
    let signature =

        match khash with
        | NULL -> CoreSig.sign None kparams (t)
        | MD5 -> CoreSig.sign (Some CoreSig.SH_MD5) kparams (t)
        | SHA -> CoreSig.sign (Some CoreSig.SH_SHA1 ) kparams (t)
        | SHA256 -> CoreSig.sign (Some CoreSig.SH_SHA256) kparams (t)
        | SHA384 -> CoreSig.sign (Some CoreSig.SH_SHA384) kparams (t)
        | MD5SHA1 ->
            let t = HASH.hash MD5SHA1 t in
            CoreSig.sign None kparams (t)
    in




    signature

let verify (a : alg) (pk : pkey a) (t : text) (s : sigv a) =
    let asig, ahash = a in
    let (kparams, khash) = pk.pkey in

    if ahash <> khash then



        Error.unexpected "Sig.verify: key requires different sig-algo"
 //           (sprintf "Sig.verify: requested sig-hash = %A, but key requires %A"
 //               ahash khash)

    else
        if asig <> sigalg_of_pkeyparams kparams then

            Error.unexpected "Sig.verify: key requires different sig-algo"
//                (sprintf "Sig.verify: requested sig-algo = %A, but key requires %A"
//                    asig (sigalg_of_pkeyparams kparams))

        else
            let result =
                match khash with
                | NULL -> CoreSig.verify None kparams t s
                | MD5 -> CoreSig.verify (Some CoreSig.SH_MD5) kparams t s
                | SHA -> CoreSig.verify (Some CoreSig.SH_SHA1 ) kparams t s
                | SHA256 -> CoreSig.verify (Some CoreSig.SH_SHA256) kparams t s
                | SHA384 -> CoreSig.verify (Some CoreSig.SH_SHA384) kparams t s
                | MD5SHA1 ->
                    let t = HASH.hash MD5SHA1 t in
                    CoreSig.verify None kparams (t) s
            in
            result

type pred =
  | Honest : a:alg -> pkey a -> pred

let gen (a:alg) : pkey a * skey a =
    let asig, ahash = a in
    let (pkey, skey) =
        match asig with
        | SA_RSA -> CoreSig.gen CoreSig.CORE_SA_RSA
        | SA_DSA -> CoreSig.gen CoreSig.CORE_SA_DSA
        | _ -> Error.unexpected "[gen] invoked on unsupported algorithm"
    in
    let p = Mkpkey #a (pkey, ahash) in
    let s = Mkskey #a (skey, ahash) p in
    (p,s)

let leak (a:alg) (s:skey a) : CoreSig.sigskey =
    let (sk, ahash) = s.skey in
    sk

let create_pkey (a : alg) (p : CoreSig.sigpkey) : pkey a =
    let (_,ahash)=a in
    Mkpkey #a (p, ahash)

let coerce (a:alg) (p:pkey a) (csk:CoreSig.sigskey) : skey a =
    let (_,ahash)=a in
    Mkskey #a (csk, ahash) p

(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Sig 

open Bytes
open TLSConstants
open CoreSig

(* ------------------------------------------------------------------------ *)
type alg = sigHashAlg //defined in TLSConstants 

type text = bytes
type sigv = bytes 

(* ------------------------------------------------------------------------ *)
type pkey = { pkey : sigpkey * hashAlg }
type skey = { skey : sigskey * hashAlg; pub : pkey }

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

#if ideal
// We maintain two logs:
// - a log of honest public keys (a,pk), not necessarily with strong crypto
// - a log of (a,pk,t) entries for all honestly signed texts
// CF We could also implement it on top of ideal non-agile Sigs.

type entry = alg * pkey * text 
//in F7: type entry = a:alg * pk:(;a) pk * t:text * s:(;a) sigv { Msg(a,pk,t) } 

type honest_entry = alg * skey * pkey
let honest_log = ref ([]: list<honest_entry>)
let log        = ref ([]: list<entry>)

let rec has_mac (a : alg) (pk : pkey) (t : text) (l:list<entry>) = 
  match l with
      [] -> false
    | (a',pk',t')::r when a = a' && pk = pk' && t = t' -> true
    | h::r -> has_mac a pk t r

let rec has_pk (a:alg) (pk:pkey) (l:list<(alg * skey * pkey)>) = 
    match l with
      | [] -> false
      | (a',_,pk')::t when a = a' && pk = pk' -> true
      | (a',_,pk')::t when a <> a' || pk <> pk' -> has_pk a pk t
      | _ -> Error.unexpected "[has_pk] unreachable pattern match"

let pk_of (a:alg) (sk:skey) =  sk.pub
let consHonestLog (a:alg) (sk:skey) (pk:pkey) log =  (a, sk, pk)::log
let consLog (a:alg) (pk:pkey) (t:text) log =  (a, pk, t)::log

let honest (a:alg) (pk:pkey) : bool = 
#if verify
  failwith "only used in ideal implementation, unverified"
#else
  has_pk a pk (!honest_log)
#endif
let strong a = if a=(SA_DSA ,SHA384) then true else false
#else //ideal
let honest (a:alg) (pk:pkey) : bool = false
let strong a = if a=(SA_DSA ,SHA384) then true else false // JK : needed to compile OCaml, needs checking
#endif

(* ------------------------------------------------------------------------ *)
let sign (a: alg) (sk: skey) (t: text): sigv =
    let asig, ahash = a in
    let (kparams, khash) = sk.skey in

    if ahash <> khash then
        #if verify
        Error.unexpected ("Sig.sign")
        #else
        Error.unexpected "Sig.sign"
            (* (sprintf "Sig.sign: requested sig-hash = %A, but key requires %A"
                ahash khash) *)
        #endif
    else
    if asig <> sigalg_of_skeyparams kparams then
        #if verify
        Error.unexpected("Sig.sign")
        #else
        Error.unexpected "Sig.sign" (*
            (sprintf "Sig.sign: requested sig-algo = %A, but key requires %A"
                asig (sigalg_of_skeyparams kparams)) *)
        #endif
    else
    let signature =
        
        match khash with
        | NULL    -> CoreSig.sign None                     kparams (t)
        | MD5     -> CoreSig.sign (Some CoreSig.SH_MD5)    kparams (t)
        | SHA     -> CoreSig.sign (Some CoreSig.SH_SHA1  ) kparams (t)
        | SHA256  -> CoreSig.sign (Some CoreSig.SH_SHA256) kparams (t)
        | SHA384  -> CoreSig.sign (Some CoreSig.SH_SHA384) kparams (t)
        | MD5SHA1 ->
            let t = HASH.hash MD5SHA1 t in
            CoreSig.sign None kparams (t)
    in
    #if ideal
    let pk = pk_of a sk in
    log := consLog a pk t (!log);
    #endif
    signature

(* ------------------------------------------------------------------------ *)
let verify (a : alg) (pk : pkey) (t : text) (s : sigv) =
    let asig, ahash = a in
    let (kparams, khash) = pk.pkey in

    if ahash <> khash then
        #if verify
        Error.unexpected("Sig.verify")
        #else
        Error.unexpected "Sig.verify"
            (* (sprintf "Sig.verify: requested sig-hash = %A, but key requires %A"
                ahash khash) *)
        #endif
    else
        if asig <> sigalg_of_pkeyparams kparams then
            #if verify
            Error.unexpected("Sig.verify")
            #else
            Error.unexpected ("Sig.verify") (*
                (sprintf "Sig.verify: requested sig-algo = %A, but key requires %A"
                    asig (sigalg_of_pkeyparams kparams)) *)
            #endif
        else
            let result =
                match khash with
                | NULL    -> CoreSig.verify None                     kparams t s
                | MD5     -> CoreSig.verify (Some CoreSig.SH_MD5)    kparams t s
                | SHA     -> CoreSig.verify (Some CoreSig.SH_SHA1  ) kparams t s
                | SHA256  -> CoreSig.verify (Some CoreSig.SH_SHA256) kparams t s
                | SHA384  -> CoreSig.verify (Some CoreSig.SH_SHA384) kparams t s
                | MD5SHA1 ->
                    let t = HASH.hash MD5SHA1 t in
                    CoreSig.verify None kparams (t) s
            in
    #if ideal 
    //#begin-idealization
            let s = strong a in
            let h = honest a pk in
            if s then 
              if h then 
                let m  = has_mac a pk t !log in
                  if result then m
                  else false
              else result
            else
            #endif //#end-idealization
            result

(* ------------------------------------------------------------------------ *)
type pred = | Honest of alg * pkey
let gen (a:alg) : pkey * skey =
    let asig, ahash  = a in
    let (pkey, skey) =
        match asig with
        | SA_RSA -> CoreSig.gen CoreSig.CORE_SA_RSA
        | SA_DSA -> CoreSig.gen CoreSig.CORE_SA_DSA
        | _      -> Error.unexpected "[gen] invoked on unsupported algorithm"
    in
    let p =    { pkey = (pkey, ahash) } in     
    let s =    { skey = (skey, ahash); pub = p } in
    #if ideal
    Pi.assume(Honest(a,p));  
    honest_log := (a,s,p)::!honest_log;
    #endif
    (p,s)

let leak (a:alg) (s:skey) : CoreSig.sigskey = 
    let (sk, ahash) = s.skey in
    sk

let create_pkey (a : alg) (p : CoreSig.sigpkey) : pkey = 
    let (_,ahash)=a in
    { pkey = (p, ahash) }

let coerce (a:alg)  (p:pkey)  (csk:CoreSig.sigskey) : skey =
    let (_,ahash)=a in
    { skey = (csk, ahash); pub = p}


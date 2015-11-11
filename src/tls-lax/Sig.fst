(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Sig 

open Platform.Bytes
open TLSConstants
open CoreCrypto

(* ------------------------------------------------------------------------ *)
type alg = sigHashAlg //defined in TLSConstants 

type text = bytes
type sigv = bytes 

type skey = 
    | SK_RSA of rsa_key * hashAlg
    | SK_DSA of dsa_key * hashAlg
    | SK_ECDSA of ec_key * hashAlg

type pkey = 
    | PK_RSA of rsa_key * hashAlg
    | PK_DSA of dsa_key * hashAlg
    | PK_ECDSA of ec_key * hashAlg

(* ------------------------------------------------------------------------ *)
let sigHashAlg_of_skey sk =
    match sk with
    | SK_RSA (k,a) -> RSASIG,a
    | SK_DSA (k,a) -> DSA, a
    | SK_ECDSA (k,a) -> ECDSA, a

let sigHashAlg_of_pkey pk =
    match pk with
    | PK_RSA (k,a) -> RSASIG,a
    | PK_DSA (k,a) -> DSA,a
    | PK_ECDSA (k,a) -> ECDSA,a

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
      | _ -> Platform.Error.unexpected "[has_pk] unreachable pattern match"

let pk_of (a:alg) (sk:skey) =  sk.pub
let consHonestLog (a:alg) (sk:skey) (pk:pkey) log =  (a, sk, pk)::log
let consLog (a:alg) (pk:pkey) (t:text) log =  (a, pk, t)::log

let honest (a:alg) (pk:pkey) : bool = 
#if verify
  failwith "only used in ideal implementation, unverified"
#else
  has_pk a pk (!honest_log)
#endif
let strong a = if a=(DSA ,Hash SHA384) then true else false
#else //ideal
let honest (a:alg) (pk:pkey) : bool = false
let strong a = if a=(DSA ,Hash SHA384) then true else false // JK : needed to compile OCaml, needs checking
#endif

(* ------------------------------------------------------------------------ *)
let sign (a: alg) (sk: skey) (t: text): sigv =
    let asig, ahash = a in
    let ksig, khash = sigHashAlg_of_skey sk in
    if ahash <> khash then
       #if verify
       Platform.Error.unexpected ("Sig.sign")
       #else
       Platform.Error.unexpected "Sig.sign"
           (* (sprintf "Sig.sign: requested sig-hash = %A, but key requires %A"
               ahash khash) *)
       #endif
     else
     if asig <> RSASIG then
       #if verify
       Platform.Error.unexpected("Sig.sign")
       #else
       Platform.Error.unexpected "Sig.sign" (*
           (sprintf "Sig.sign: requested sig-algo = %A, but key requires %A"
               asig ksig) *)
       #endif
    else
    let (t,ho) : (text * option hash_alg)= 
        match khash with
        | Hash h -> t,Some h
        | MD5SHA1 -> HASH.hash MD5SHA1 t,None 
        | NULL -> Platform.Error.unexpected "Sig.sign" , None
    in 
    let signature =      
        match sk with
        | SK_RSA (k,h) -> CoreCrypto.rsa_sign ho k t
        | SK_DSA (k,h) -> CoreCrypto.dsa_sign k t
        | SK_ECDSA (k,h) -> CoreCrypto.ecdsa_sign ho k t
    in
    #if ideal
    let pk = pk_of a sk in
    log := consLog a pk t (!log);
    #endif
    signature

(* ------------------------------------------------------------------------ *)
let verify (a : alg) (pk : pkey) (t : text) (s : sigv) =
    let asig, ahash = a in
    let ksig, khash = sigHashAlg_of_pkey pk in
    if ahash <> khash then
       #if verify
       Platform.Error.unexpected ("Sig.verify")
       #else
       Platform.Error.unexpected "Sig.verify"
       #endif
     else
     if asig <> RSASIG then
       #if verify
       Platform.Error.unexpected("Sig.verify")
       #else
       Platform.Error.unexpected "Sig.verify" 
       #endif
    else
    let t,ho : (text * option hash_alg) = 
        match khash with
        | Hash h -> t,Some h
        | MD5SHA1 -> HASH.hash MD5SHA1 t,None 
        | NULL -> Platform.Error.unexpected "Sig.verify" 
    in 
    let result =      
        match pk with
        | PK_RSA (k,h) -> CoreCrypto.rsa_verify ho k t s
        | PK_DSA (k,h) -> CoreCrypto.dsa_verify k t s
        | PK_ECDSA (k,h) -> CoreCrypto.ecdsa_verify ho k t s
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
    let pkey,skey =
        match asig with
        | RSASIG -> 
           let k = CoreCrypto.rsa_gen_key 2048 in
           PK_RSA (k,ahash), SK_RSA ({k with rsa_prv_exp=None},ahash)
        | DSA -> 
           let k = CoreCrypto.dsa_gen_key 1024 in  
           PK_DSA (k,ahash), SK_DSA ({k with dsa_private=None},ahash)
        | _      -> Platform.Error.unexpected "[gen] invoked on unsupported algorithm"
    in
    #if ideal
    Pi.assume(Honest(a,pkey));  
    honest_log := (a,skey,pkey)::!honest_log;
    #endif
    (pkey,skey)

let leak_rsa_key (a:alg) (s:skey) : rsa_key = 
    match s with SK_RSA(k,h) -> k

let leak_dsa_key (a:alg) (s:skey) : dsa_key = 
    match s with SK_DSA(k,h) -> k
    
let coerce_rsa_key (a:alg) (p:pkey) (csk:rsa_key) : skey =
    let (_,ahash)=a in
    SK_RSA(csk,ahash)

let coerce_dsa_key (a:alg) (p:pkey) (csk:dsa_key) : skey =
    let (_,ahash)=a in
    SK_DSA(csk,ahash)

let create_pkey (a:alg) (p:pkey) = 
    let (_,ahash)=a in
    match p with
    | PK_RSA(k,x) -> PK_RSA(k,ahash)
    | PK_DSA(k,x) -> PK_DSA(k,ahash)
    | _  -> failwith "unimplemented"

let coerce (a:alg) (p:skey) = 
    let (_,ahash)=a in
    match p with
    | SK_RSA(k,x) -> SK_RSA(k,ahash)
    | SK_DSA(k,x) -> SK_DSA(k,ahash)
    | _  -> failwith "unimplemented"



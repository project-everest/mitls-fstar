module HMAC

open Platform.Bytes
open TLSConstants
open CoreCrypto

type key = bytes
type data = bytes
type mac = bytes

(* SSL/TLS constants *)

let ssl_pad1_md5  = createBytes 48 0x36uy
let ssl_pad2_md5  = createBytes 48 0x5cuy
let ssl_pad1_sha1 = createBytes 40 0x36uy
let ssl_pad2_sha1 = createBytes 40 0x5cuy

(* SSL3 keyed hash *)

val sslKeyedHashPads: hashAlg -> bytes * bytes
let sslKeyedHashPads alg = 
  match alg with
    | Hash MD5 -> (ssl_pad1_md5, ssl_pad2_md5)
    | Hash SHA1 -> (ssl_pad1_sha1, ssl_pad2_sha1)
    | _   -> Platform.Error.unexpected "[sslKeyedHashPads] invoked on unsupported algorithm"

val sslKeyedHash: hashAlg -> key -> data -> mac
let sslKeyedHash alg key data =
    let (pad1, pad2) = sslKeyedHashPads alg in
    let dataStep1 = key @| pad1 @| data in
    match alg with
    | NULL -> Platform.Error.unexpected "[sslKeyedHash] invoked on NULL algorithm"
    | _ ->
      let step1 = HASH.hash alg dataStep1 in
      let dataStep2 = key @| pad2 @| step1 in
      HASH.hash alg dataStep2

val sslKeyedHashVerify: hashAlg -> key -> data -> mac -> bool
let sslKeyedHashVerify alg key data expected =
    let result = sslKeyedHash alg key data in
    equalBytes result expected

(* Parametric keyed hash *)

let hmac alg key data =
    match alg with
    | Hash h  -> (CoreCrypto.hmac h key data)
    | NULL    -> Platform.Error.unexpected "[HMAC] Invalid hash (NULL) for HMAC"
    | MD5SHA1 -> Platform.Error.unexpected "[HMAC] Invalid hash (MD5SHA1) for HMAC"

val hmacVerify: hashAlg -> key -> data -> mac -> bool 
let hmacVerify alg key data expected =
    let result = hmac alg key data in
    equalBytes result expected

(* Top level MAC function *)

let tls_mac a k d =
    match a with
    | HMAC(alg) -> 
        let h = hmac (Hash alg) k d in 
        let l = length h in
        let exp = macSize a in
          if l = exp then h 
          else Platform.Error.unexpected "CoreCrypto.HMac returned a MAC of unexpected size"
    | SSLKHASH(alg) -> 
        let h = sslKeyedHash (Hash alg) k d in
        let l = length h in
        let exp = macSize a in
          if l = exp then h 
          else Platform.Error.unexpected "sslKeyedHash returned a MAC of unexpected size"

let tls_macVerify a k d t =
    match a with
    | HMAC(alg) -> hmacVerify (Hash alg) k d t
    | SSLKHASH(alg) -> sslKeyedHashVerify (Hash alg) k d t

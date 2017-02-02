module HashMAC

open Platform.Bytes
open TLSConstants
open Hashing.Spec // for the algorithm names, instead of CoreCrypto

type key = bytes
type data = bytes
type mac (a:macAlg) = lbytes (macSize a)


(* Parametric keyed HMAC; could be coded up from two HASH calls. *)


val hmac: a:alg -> k:hkey a -> m:bytes -> 
  ST (t:tag a {t == Hashing.Spec.hmac a k m})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hmac a k m = Hashing.OpenSSL.hmac a k m

// consider providing it only in UFCMA
val hmacVerify: a:alg -> k:hkey a -> m:data -> t:tag a -> ST (b:bool {b <==> (t == Hashing.Spec.hmac a k m)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hmacVerify a k p t =
    let result = hmac a k p in
    equalBytes result t


(* Historical constructions from SSL, still used in TLS 1.0, not that different from HMAC *)

(* SSL/TLS constants *)

private let ssl_pad1_md5  = createBytes 48 0x36z
private let ssl_pad2_md5  = createBytes 48 0x5cz
private let ssl_pad1_sha1 = createBytes 40 0x36z
private let ssl_pad2_sha1 = createBytes 40 0x5cz

(* SSL3 keyed hash *)
type sslHashAlg = h:hashAlg { h = Hash MD5 \/ h = Hash SHA1 }
val sslKeyedHashPads: sslHashAlg -> Tot(bytes * bytes)
let sslKeyedHashPads = function
    | Hash MD5 -> (ssl_pad1_md5, ssl_pad2_md5)
    | Hash SHA1 -> (ssl_pad1_sha1, ssl_pad2_sha1)

private val sslKeyedHash: a:alg {a = MD5 \/ a = SHA1} -> k:hkey a -> bytes -> ST (tag a)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let sslKeyedHash a k p =
    let (inner, outer) = 
      match a with 
      | MD5 -> ssl_pad1_md5, ssl_pad2_md5
      | SHA1 -> ssl_pad1_sha1, ssl_pad2_sha1 in
    let h = Hashing.compute a (k @| inner @| p) in
    Hashing.compute a (k @| outer @| h)

private val sslKeyedHashVerify: a:alg {a = MD5 \/ a = SHA1} -> k:hkey a -> bytes -> t:tag a -> ST bool 
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let sslKeyedHashVerify a k p t =
    let res = sslKeyedHash a k p in
    equalBytes res t


(* Agile MAC function *)

val tls_mac: a:macAlg -> k:lbytes (macKeySize a) -> bytes -> ST bytes
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let tls_mac a k d : mac a =
    match a with
    | HMAC     a -> hmac a  k d  
    | SSLKHASH a -> sslKeyedHash a k d 

val tls_macVerify: a:macAlg -> k:lbytes (macKeySize a) -> msg:bytes -> t:lbytes (macSize a) -> ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let tls_macVerify (a:tls_macAlg) k d t =
    match a with
    | HMAC alg -> hmacVerify alg k d t
    | SSLKHASH alg -> sslKeyedHashVerify alg k d t

 

module MiTLS.HMAC

open MiTLS.Hashing.Spec // for the algorithm names, instead of CoreCrypt
open MiTLS.Mem

open FStar.HyperStack.ST

let ha = a:EverCrypt.HMAC.supported_alg{Spec.Hash.Definitions.is_md a}

(* Parametric keyed HMAC; could be coded up from two HASH calls. *)

val hmac:
  a:ha ->
  k:hkey a ->
  m:macable a ->
  Stack (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 ->
    modifies_none h0 h1 /\
    t = Hashing.Spec.hmac a k m)

val hmacVerify: a:ha -> k:hkey a -> m:macable a -> t: tag a -> ST (b:bool {b <==> (t == Hashing.Spec.hmac a k m)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

(*** Old TLS 1.2 HMAC ***)

/// Agile bytes-friendly MAC function

type macable = b:Bytes.bytes {Bytes.length b + 128 < pow2 32} // [==> pre of hmac for all algorithms]

let tls_mac: a:
  tls_macAlg ->
  k: hkey a  ->
  msg:macable ->
  ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1) =
  hmac

let tls_macVerify:
  a:tls_macAlg ->
  k: hkey a  ->
  msg:macable ->
  tag a ->
  ST bool
  (requires fun h0 -> True)
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1)) =
  hmacVerify

module Hashing.OpenSSL
module HS = FStar.HyperStack //Added automatically

// Multiplexing between hacl-star [Crypto] and external [CoreCrypto]
// implementations for HMAC and hash algorithms. We still rely on an
// external provider for legacy algorithms (MD5, SHA1) but otherwise
// only use verified implementations
// (TODO: separate interface and implementations; align specs)

open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Bytes
open Hashing.Spec


(* shared, stateful interface, still quite high level *)

val compute: a:alg -> b:bytes -> ST (t:tag a {t == hash a b})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))

assume type hash_ctx (a:alg) (r:rid): Type0 // externally-allocated

assume val accT: #a:alg -> #r:rid -> hash_ctx a r -> mem -> GTot bytes
// getting the internal-state out, e.g. the whole input bytestring

assume val accInv: #a:alg -> #r:rid -> v:hash_ctx a r -> h0:mem -> h1:mem ->
  Lemma(
    // TBC h0 `on` r == h1 `on` r  ==> 
    accT v h0 == accT v h1)

(*
val alloc: a:alg -> parent:rid -> ST (r:rid & hash_ctx a r)
  (requires (fun h -> True))
  (ensures (fun h0 (r,v) h1 -> 
    modifies Set.empty h0 h1 /\
    extends r parent /\
    HS.fresh_region r h0 h1 /\
    accT v h1 == empty_bytes))

val update: #a:alg -> #r:rgn -> v:hash_ctx a r -> b:bytes -> ST unit 
  (requires (fun h -> True))
  (ensures (fun h0 () h1 ->
    modifies_one r h0 h1 /\
    accT v h1 == accT v h0 @| b))

val finalize: #a:alg -> #r:rgn -> v:hash_ctx a r -> ST (tag a)
  (requires (fun h -> True))
  (ensures (fun h0 t h1 -> 
    modifies_one r h0 h1 /\
    t = hash a (accT v h0))) // not specifying the post accT makes v non-reusable
*)

val hmac: a:alg -> k:hkey a -> m:bytes -> ST (t:tag a {t == Hashing.Spec.hmac a k m})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))

(* OpenSSL implementation via CoreCrypto *)

let toCC = function 
  | MD5 -> CoreCrypto.MD5 
  | SHA1 -> CoreCrypto.SHA1 
  | SHA224 -> CoreCrypto.SHA224 
  | SHA256 -> CoreCrypto.SHA256 
  | SHA384 -> CoreCrypto.SHA384 
  | SHA512 -> CoreCrypto.SHA512


let compute a b = CoreCrypto.hash (toCC a) b // for now claimed to be pure --- fix as we remove an indirection
let hmac a k b =  CoreCrypto.hmac (toCC a) k b

(* 18-02-06 TODO gain access to more Hacl* modules... 

(* Hacl* implementation via Crypto.* without support for legacy algorithms. *)

let toCrypto = function 
  | SHA256 -> Some Crypto.Hash.SHA256 
  | SHA384 -> Some Crypto.Hash.SHA384 
  | SHA512 -> Some Crypto.Hash.SHA512
  | _      -> None

// *** by using this file, we assume CoreCrypto is functionally correct and safe ***
#reset-options "--lax" 
let compute a b = 
  match toCrypto a with 
  | None -> 
      CoreCrypto.hash (toCC a) b // for now claimed to be pure --- fix as we remove an indirection
  | Some a' -> (
      push_frame(); 
      let len = length b in 
      let input = BufferBytes.from_bytes b in // stack allocate instead? 
      let output = Buffer.create 0uy (Crypto.hash_size a') in
      Crypto.Hash.agile_hash a output input len;
      Buffer.rfree input; 
      let tag = to_bytes (Crypto.hash_size a') output in
      pop_frame();  
      tag )

let hmac a k b = 
  match toCrypto a with 
  | None -> 
      CoreCrypto.hmac (toCC a) k m
  | Some a' -> (
      push_frame(); 
      let inputlen = length b in 
      let input = BufferBytes.from_bytes b in // stack allocate instead? 
      let keylen = len k in 
      let key = Buffer.create 0uy keylen in
      let output = Buffer.create 0uy (Crypto.hash_size a') in
      Crypto.HMAC.hmac a output key keylen input inputlen;
      Buffer.rfree input; 
      let tag = to_bytes (Crypto.hash_size a') output in
      pop_frame();  
      tag )
*)


(*
let alloc a parent = CoreCrypto.digest_create (toCC a) 
let update #a #r v b = CoreCrypto.digest_update v  b
let finalize #a #r v b = CoreCrypto.digest_final v 
*)


(* WAS, for a long while: 

(* Parametric hash algorithm (implements interface) *)
val hash': hashAlg -> bytes -> Tot bytes
let hash' alg data: bytes =
    match alg with
    | NULL    -> data
    | MD5SHA1 -> (CoreCrypto.hash MD5 data) @| (CoreCrypto.hash SHA1 data)
    | Hash h  -> (CoreCrypto.hash h  data)

val hash: hashAlg -> bytes -> Tot bytes
let hash alg data: bytes =
  let h = hash' alg data in
  let l = length h in
    h
(*
  let exp = hashSize alg in
  if l = exp then h
  else FStar.Error.unexpected "CoreCrypto.Hash returned a hash of an unexpected size"
*)
*)


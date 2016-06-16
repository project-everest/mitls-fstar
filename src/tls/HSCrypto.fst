module HSCrypto

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set  

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range
open StatefulLHAE

(* CRYPTO sub-module *)
(* To be moved to other modules, linked with CoreCrypto, and idealized *)

val hkdf_extract: CoreCrypto.hash_alg -> bytes -> bytes -> Tot bytes
let hkdf_extract ha salt secret = CoreCrypto.hmac ha salt secret

val hkdf_expand_int: CoreCrypto.hash_alg -> int -> int -> int -> bytes -> bytes -> bytes -> Tot bytes
let rec hkdf_expand_int ha count curr len secret prev info = 
    if (curr < len) then
      let count = count + 1 in
      let prev = CoreCrypto.hmac ha secret (prev @| info @| (bytes_of_int count 1)) in 
      let curr = curr + CoreCrypto.hashSize ha in
      let next = hkdf_expand_int ha count curr len secret prev info in
      prev @| next
    else empty_bytes

(* TODO: AR: subtyping check failed *)

val hkdf_expand_label: CoreCrypto.hash_alg -> bytes -> string -> bytes -> int -> Tot bytes
let hkdf_expand_label ha secret label hv len = 
  let info = (bytes_of_int 2 len) @| 
	     (vlbytes 1 (abytes ("TLS 1.3, "^label))) @|
	     (vlbytes 1 hv) in
  let prev = empty_bytes in
  let res = hkdf_expand_int ha 0 0 len secret prev info in
  let (sp1,sp2) = split res len in
  sp1

type ms = bytes // -> abstract

val dh_keygen: CommonDH.group -> Tot CommonDH.key
let dh_keygen = CommonDH.keygen

val dh_shared_secret1: CommonDH.key -> CommonDH.key -> Tot CommonDH.secret
let dh_shared_secret1 = CommonDH.dh_initiator

val dh_shared_secret2: CommonDH.key -> Tot (CommonDH.key * CommonDH.secret)
let dh_shared_secret2 = CommonDH.dh_responder

(* TLS <= 1.2 *)
assume val derive_keys: gxy:CommonDH.secret -> cr:random -> sr:random -> log:bytes ->
	                rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


(* TLS 1.3 *)

assume val derive_handshake_keys: gxy:CommonDH.secret -> log: bytes ->
				  rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

assume val derive_finished_keys: gxs:CommonDH.secret -> gxy:CommonDH.secret -> log: bytes -> Tot (ts:ms * cf:ms * sf:ms)

assume val derive_traffic_keys: ts:ms -> log: bytes -> 
				rd:rid -> wr:rid -> i:id -> ST (both i)     
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

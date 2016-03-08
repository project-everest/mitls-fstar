(*--build-config
  options:--codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib SeqProperties --codegen-lib HyperHeap  --admit_fsi FStar.Char --admit_fsi FStar.HyperHeap --admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.Seq --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --admit_fsi Handshake --lax;
  other-files:FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fsi stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.fst FStar.ListProperties.fst seq.fsi FStar.SeqProperties.fst /home/jkz/dev/FStar/contrib/Platform/fst/Bytes.fst /home/jkz/dev/FStar/contrib/Platform/fst/Date.fst /home/jkz/dev/FStar/contrib/Platform/fst/Error.fst /home/jkz/dev/FStar/contrib/Platform/fst/Tcp.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/CoreCrypto.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/DHDB.fst TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst TLSExtensions.p.fst Range.p.fst DataStream.fst TLSPRF.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fsti StatefulLHAE.fst PRF.p.fst;
  --*)

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
open HandshakeMessages
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
      
val hkdf_expand_label: CoreCrypto.hash_alg -> bytes -> string -> bytes -> int -> Tot bytes
let hkdf_expand_label ha secret label hv len = 
  let info = (bytes_of_int len 2 ) @| 
	     (vlbytes 1 (abytes ("TLS 1.3, "^label))) @|
	     (vlbytes 1 hv) in
  let prev = empty_bytes in
  let res = hkdf_expand_int ha 0 0 len secret prev info in
  let (sp1,sp2) = split res len in
  sp1

assume val get_signing_cert: string -> option sigAlg -> list sigHashAlg -> Tot Cert.chain
assume val cert_sign: Cert.chain -> option sigAlg -> list sigHashAlg -> bytes -> Tot (Result (b:bytes{length b < 65536}))
assume val cert_verify: Cert.chain -> option sigAlg -> list sigHashAlg -> bytes -> bytes -> Tot (Result unit)

type ff_all_groups =
  | FF_2048
  | FF_4096
  | FF_8192
  | FF_arbitrary of CoreCrypto.dh_params
  
type dh_group = 
  | FFDH of ff_all_groups
  | ECDH of ECGroup.ec_all_curve

type dh_key = 
  | FFKey of CoreCrypto.dh_key
  | ECKey of CoreCrypto.ec_key

type dh_secret = bytes // -> abstract
type ms = bytes // -> abstract

assume val dh_keygen: g:dh_group -> Tot (x:dh_key)
assume val dh_shared_secret1: y:dh_key -> gx:dh_key -> Tot (gxy:dh_secret)
assume val dh_shared_secret2: gy:dh_key -> Tot (x:dh_key * gxy:dh_secret)

(* TLS <= 1.2 *)
assume val derive_keys: gxy:dh_secret -> cr:random -> sr:random -> log:bytes -> 
	                rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


(* TLS 1.3 *)
assume val derive_handshake_keys: gxy:dh_secret -> log: bytes ->
				  rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

assume val derive_finished_keys: gxs:dh_secret -> gxy:dh_secret -> log: bytes -> Tot (ts:ms * cf:ms * sf:ms)

assume val derive_traffic_keys: ts:ms -> log: bytes -> 
				rd:rid -> wr:rid -> i:id -> ST (both i)     
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))



(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module CommonDH

open FStar.HyperStack
open Platform.Bytes
open Platform.Error
open Parse
open TLSError
open FStar.ST

val group: t:Type0{hasEq t}
val is_ec: group -> Tot bool

val pre_keyshare (g:group) : Tot (t:Type0{hasEq t})
val pre_share (g:group) : Tot (t:Type0{hasEq t})

// DH secret
type secret (g:group) = bytes

val namedGroup_of_group: g:group -> Tot (option namedGroup)
val group_of_namedGroup: ng:namedGroup -> Tot (option group)
val default_group: group

type id = g:group & s:pre_share g
val dh_region : rgn
val registered: id -> GTot Type0
val honest_share: id -> GTot Type0
val dishonest_share: id -> GTot Type0

val pre_pubshare: #g:group -> pre_keyshare g -> Tot (pre_share g)
type share (g:group) = s:pre_share g{registered (|g, s|)}
type keyshare (g:group) = s:pre_keyshare g{registered (|g, pre_pubshare s|)}
val pubshare: #g:group -> keyshare g -> Tot (share g)

val is_honest: i:id -> ST bool
  (requires (fun h -> registered i))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 /\
    (if Flags.ideal_KEF then
      (b ==> honest_share i) /\ (not b ==> dishonest_share i)
    else b = false)))

val keygen: g:group -> ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1 /\
      honest_share (|g, pubshare s|)
     else
      modifies_none h0 h1)))

val dh_initiator: #g:group -> keyshare g -> share g -> ST (secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

val dh_responder: #g:group -> share g -> ST (share g * secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 (ks,s) h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1 /\
      honest_share (|g, ks|)
     else
      modifies_none h0 h1)))

val register: #g:group -> gx:pre_share g -> ST (share g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1
     else
      modifies_none h0 h1)))

val parse: g:group -> bytes -> Tot (option (pre_share g))
val parse_partial: bool -> bytes -> Tot (result ((g:group & pre_share g) * bytes))
val serialize: #g:group -> pre_share g -> Tot bytes
val serialize_raw: #g:group -> pre_share g -> Tot bytes

// TODO: replace "bytes" by either DH or ECDH parameters
// should that go elsewhere? YES.
(** KeyShare entry definition *)
type keyShareEntry =
  | Share: g:group{Some? (namedGroup_of_group g)} -> pre_share g -> keyShareEntry
  | UnknownShare:
    ng:namedGroup { None? (group_of_namedGroup ng)} ->
    b:bytes{repr_bytes (length b) <= 2} -> keyShareEntry

(** ClientKeyShare definition *)
type clientKeyShare = l:list keyShareEntry{List.Tot.length l < 65536/4}

(** ServerKeyShare definition *)
type serverKeyShare = keyShareEntry

(** KeyShare definition *)
noeq type keyShare =
  | ClientKeyShare of clientKeyShare
  | ServerKeyShare of serverKeyShare

// the parsing/formatting moves to the private part of Extensions
(** Serializing function for a KeyShareEntry *)
val keyShareEntryBytes: keyShareEntry -> Tot (b:bytes{4 <= length b})
val parseKeyShareEntry: pinverse_t keyShareEntryBytes
val keyShareEntriesBytes: list keyShareEntry -> Tot (b:bytes{2 <= length b /\ length b < 65538})
val parseKeyShareEntries: pinverse_t keyShareEntriesBytes
val clientKeyShareBytes: clientKeyShare -> Tot (b:bytes{ 2 <= length b /\ length b < 65538 })
val parseClientKeyShare: b:bytes{2 <= length b /\ length b < 65538} -> Tot (result clientKeyShare)
val serverKeyShareBytes: serverKeyShare -> Tot (b:bytes{ 4 <= length b })
val parseServerKeyShare: pinverse_t serverKeyShareBytes
val keyShareBytes: ks:keyShare -> Tot (b:bytes{
  ClientKeyShare? ks ==> (2 <= length b /\ length b < 65538) /\
  ServerKeyShare? ks ==> (4 <= length b)})
val parseKeyShare: bool -> bytes -> Tot (result keyShare)

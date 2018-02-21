module CommonDH

open FStar.HyperStack
open FStar.Bytes
open FStar.Error
open Parse
open TLSError
open FStar.HyperStack.ST

include Format.NamedGroup
module FNGL = Format.NamedGroupList

let namedGroups = Format.NamedGroupList.namedGroupList
let namedGroupList = Format.NamedGroupList.namedGroupList

let namedGroupBytes x = namedGroup_serializer32 x
let parseNamedGroup x = namedGroup_parser32 x
let namedGroupsBytes x = FNGL.namedGroupList_serializer32 x
let parseNamedGroups x = FNGL.namedGroupList_parser32 x

// was "valid", not "supported"; should probably be defined from the crypto provider.
let is_supported_group x = List.Tot.mem x 
  [ SECP256R1; SECP384R1; SECP521R1; X25519; X448; 
    FFDHE2048; FFDHE3072; FFDHE4096; FFDHE6144; FFDHE8192 ]
type supportedNamedGroup = x:namedGroup{is_supported_group x}
type supportedNamedGroups = xs:namedGroups{List.Tot.for_all is_supported_group xs} 

val group: t:Type0{hasEq t}
val is_ec: group -> Tot bool
val string_of_group: group -> Tot string

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
  | HRRKeyShare of namedGroup
/// 3 cases, depending on the enclosing message.
/// Do we ever benefit from bundling them?

// the parsing/formatting moves to the private part of Extensions
(** Serializing function for a KeyShareEntry *)
val keyShareEntryBytes: keyShareEntry -> Tot (b:bytes{4 <= length b})
val parseKeyShareEntry: pinverse_t keyShareEntryBytes
val keyShareEntriesBytes: list keyShareEntry -> Tot (b:bytes{2 <= length b /\ length b < 65538})
val parseKeyShareEntries: pinverse_t keyShareEntriesBytes
val clientKeyShareBytes: clientKeyShare -> Tot (b:bytes{2 <= length b /\ length b < 65538})
val parseClientKeyShare: b:bytes{2 <= length b /\ length b < 65538} -> Tot (result keyShare)
val serverKeyShareBytes: serverKeyShare -> Tot (b:bytes{4 <= length b})
val parseServerKeyShare: bytes -> Tot (result keyShare)
val helloRetryKeyShareBytes: keyShare -> Tot (b:bytes)
val parseHelloRetryKeyShare: bytes -> Tot (result keyShare)

val keyShareBytes: ks:keyShare -> Tot (b:bytes{
  ClientKeyShare? ks ==> (2 <= length b /\ length b < 65538) /\
  ServerKeyShare? ks ==> (4 <= length b) /\
  HRRKeyShare? ks ==> (2 = length b)})



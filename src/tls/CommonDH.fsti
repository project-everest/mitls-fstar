(**
An abstract interface for Diffie-Hellman operations

When the key extraction stack is idealized (ideal_KEF), this module
records the honesty of shares using two layers of types

[pre_share] is for syntactically valid shares (used in parsing modules);
[share] is for registered shares (for which is_honest is defined).
*)
module CommonDH

open FStar.HyperStack
open Platform.Bytes
open Platform.Error
open Parse
open TLSError
open FStar.HyperStack.ST

/// Groups named in the RFC

include Format.NamedGroup // QD-generated interface, so that we get the constructors

let namedGroups = list namedGroup
// to be replaced with QD-generated vector
// let namedGroups = NamedGroupList.namedGroupList 

// to be rewritten defensively; was "valid", not "supported"; 
// should probably be defined from the crypto provider.
let is_supported_group = function 
  | FFDHE_PRIVATE_USE _
  | ECDHE_PRIVATE_USE _
  | UNKNOWN _ -> false
  | _ -> true
type supportedNamedGroup = x:namedGroup{is_supported_group x}
type supportedNamedGroups = xs:namedGroups //{List.Tot.forall is_supported_group xs} 


/// Public key shares and private exponents are indexed by an abstract
/// group descriptor (including its generator), ranging over both
/// prime fields and elliptic curves for cryptographic agility.
///
/// DHGroup and ECGroup provide their concrete implementations.

val group: t:Type0{hasEq t}
val is_ec: group -> bool
val string_of_group: group -> string

val pre_keyshare (g:group) : t:Type0{hasEq t}
val pre_share (g:group) : t:Type0{hasEq t}
val pre_pubshare: #g:group -> pre_keyshare g -> pre_share g

type secret (g:group) = bytes

val namedGroup_of_group: g:group -> Tot (option namedGroup)
val group_of_namedGroup: ng:namedGroup -> Tot (option group)
val default_group: group

/// We index ODH instances using public shares.  This enables us to
/// retrieve (conditionally idealized, stateful) instances after
/// parsing their wire format. This requires checking for collisions
/// between honestly-generated shares.

type pre_dhi = g:group & s:pre_share g
type pre_dhr (i:pre_dhi) = s:pre_share (dfst i)
val dh_region : rgn

val registered_dhi: pre_dhi -> GTot Type0
val fresh_dhi: pre_dhi -> mem -> GTot Type0
val honest_dhi: pre_dhi -> GTot Type0
val corrupt_dhi: pre_dhi -> GTot Type0
val is_honest_dhi: i:pre_dhi -> ST bool
  (requires fun h -> registered_dhi i)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> honest_dhi i) /\ (not b <==> corrupt_dhi i))
type dhi = i:pre_dhi{registered_dhi i}

type share (g:group) = pre_share g
type ishare (g:group) = s:pre_share g{registered_dhi (| g, s |)}
type ikeyshare (g:group) = s:pre_keyshare g{registered_dhi (|g, pre_pubshare s|)}
val ipubshare: #g:group -> i:ikeyshare g -> Tot (s:ishare g{s == pre_pubshare i})

val registered_dhr: #i:dhi -> j:pre_dhr i -> GTot Type0
val fresh_dhr: #i:dhi -> j:pre_dhr i -> mem -> GTot Type0
val honest_dhr: #i:dhi -> j:pre_dhr i -> GTot Type0
val corrupt_dhr: #i:dhi -> j:pre_dhr i -> GTot Type0
val lemma_honest_corrupt_dhr: #i:dhi -> j:pre_dhr i{registered_dhr j} -> Lemma (honest_dhr j <==> ~(corrupt_dhr j))
val is_honest_dhr: #i:dhi -> j:pre_dhr i -> ST bool
  (requires fun h -> registered_dhr j)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> honest_dhr j) /\ (not b <==> corrupt_dhr j))

type dhr (i:dhi) = j:pre_dhr i{registered_dhr j}
type rshare (g:group) (gx:ishare g) = dhr (| g, gx |)

/// Correct Ephemeral Diffie-Hellman exchanges go as follows:
///
///       initiator           responder
/// --------------------------------------------
///   x, gx <- keygen g
///              ----g, gx---->
///                         gy, gx^y <- dh_responder gx
///              <----gy-------
///   gy^x <- dh_initiator x gy
///

val keygen: g:group -> ST (ikeyshare g)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> modifies_one dh_region h0 h1 /\
    (Flags.model ==>
      (fresh_dhi (| g, ipubshare s |) h0
      /\ honest_dhi (| g, ipubshare s |))))

// dh_initiator is used within dh_responder,
// hence this definition ordering.

val dh_initiator: g:group -> gx:ikeyshare g -> gy:rshare g (ipubshare gx) -> ST (secret g)
  (requires fun h0 -> True)
  (ensures (fun h0 _ h1 -> modifies_one dh_region h0 h1))

val dh_responder: g:group -> gx:ishare g -> ST (rshare g gx * secret g)
  (requires fun h0 -> True)
  (ensures fun h0 (gy, gxy) h1 -> modifies_one dh_region h0 h1 /\
    (Flags.model ==>
      ((honest_dhi (| g, gx |) ==> (fresh_dhr gy h0 /\ honest_dhr gy))
      /\ (corrupt_dhi (| g, gx |) ==> corrupt_dhr gy))))

/// When parsing gx, and unless gx is already registered,
/// we register it as dishonest.
/// The registration property is captured in the returned type.
/// Still missing details, e.g. functional correctness.
///
val register_dhi: #g:group -> gx:pre_share g -> ST (ishare g)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> modifies_one dh_region h0 h1)

val register_dhr: #g:group -> gx:ishare g -> gy:pre_share g -> ST (rshare g gx)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> modifies_one dh_region h0 h1)

/// Parsing and formatting
///
val parse: g:group -> bytes -> Tot (option (pre_share g))
val parse_partial: bool -> bytes -> Tot (result ((g:group & pre_share g) * bytes))
val serialize: #g:group -> pre_share g -> Tot bytes
val serialize_raw: #g:group -> pre_share g -> Tot bytes // used for printing

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
val parseClientKeyShare: b:bytes{2 <= length b /\ length b < 65538} -> Tot (result clientKeyShare)
val serverKeyShareBytes: serverKeyShare -> Tot (b:bytes{ 4 <= length b })
val parseServerKeyShare: pinverse_t serverKeyShareBytes
val keyShareBytes: ks:keyShare -> Tot (b:bytes{
  ClientKeyShare? ks ==> (2 <= length b /\ length b < 65538) /\
  ServerKeyShare? ks ==> (4 <= length b) /\
  HRRKeyShare? ks ==> (2 = length b)})
type ks_msg = | KS_ClientHello | KS_ServerHello | KS_HRR
val parseKeyShare: ks_msg -> bytes -> Tot (result keyShare)

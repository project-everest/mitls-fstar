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

/// Public key shares and private exponents are indexed by an abstract
/// group descriptor (including its generator), ranging over both
/// prime fields and elliptic curves for cryptographic agility.
///
/// DHGroup and ECGroup provide their concrete implementations.

val group: t:Type0{hasEq t}
val is_ec: group -> Tot bool
val string_of_group: group -> Tot string

val pre_keyshare (g:group) : Tot (t:Type0{hasEq t})
val pre_share (g:group) : Tot (t:Type0{hasEq t})

type secret (g:group) = bytes

val namedGroup_of_group: g:group -> Tot (option namedGroup)
val group_of_namedGroup: ng:namedGroup -> Tot (option group)
val default_group: group

/// We index ODH instances using public shares.  This enables us to
/// retrieve (conditionally idealized, stateful) instances after
/// parsing their wire format. This requires checking for collisions
/// between honestly-generated shares.

type id = g:group & s:pre_share g
val dh_region : rgn
val registered: id -> GTot Type0
val honest_share: id -> GTot Type0
val dishonest_share: id -> GTot Type0

val pre_pubshare: #g:group -> pre_keyshare g -> Tot (pre_share g)
type share (g:group) = s:pre_share g{registered (|g, s|)}

/// private keys (hiding the ephemeral secret exponent)
/// 
type keyshare (g:group) = s:pre_keyshare g{registered (|g, pre_pubshare s|)}
val pubshare: #g:group -> keyshare g -> Tot (share g)

val is_honest: i:id -> ST bool
  (requires (fun h -> registered i))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 /\
    (if Flags.ideal_KEF then
      (b ==> honest_share i) /\ (not b ==> dishonest_share i)
    else b = false)))


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
val keygen: g:group -> ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1 /\
      honest_share (|g, pubshare s|)
     else
      modifies_none h0 h1)))
// TODO: we need the abstract stateful property of being freshly registered, 
// with a lemma [registered h0 v /\ freshly_registered h0 w h1 ==> v <> w] 


// dh_initiator is used within dh_responder, 
// hence this definition ordering.

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

/// When parsing gx, and unless gx is already registered,
/// we register it as dishonest.
/// The registration property is captured in the returned type.
/// Still missing details, e.g. functional correctness.
/// 
val register: #g:group -> gx:pre_share g -> ST (share g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1
     else
      modifies_none h0 h1)))


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

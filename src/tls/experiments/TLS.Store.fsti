module TLS.Store

/// Host state (shared between all connections in the process),
/// holding auxiliary authenticated-encryption algorithms and keys
/// used to protect PSKs and cookies. Actual storage of encrypted
/// materials is provided by the application relying on callbacks.
///
/// We extend the pattern used to protect tickets in TLS messages to
/// also protect PSKs, cookies, and received tickets. We rely on AEAD
/// with random explicit IVs, fine for low-frequency encryptions.
/// 
/// The key values are private to this module. They are set by default
/// to local, volatile, fresh secrets that can be overwritten by the
/// application to enable their re-use between hosts.
///
/// We try to follow the calling conventions of EverCrypt.fsti

module B = LowStar.Buffer

open FStar.Integers
open FStar.HyperStack.ST
open Spec.AEAD
open EverCrypt.AEAD
open EverCrypt.Error 

// Adapted from the beginning of Ticket.fst 

type usage = 
  | WrapPSK      // used by clients and servers to protect application PSKs and their pskInfo
  | ServerCookie // used by servers to protect HRR contents echoed back in ClientHello2 
  | ServerTicket // user by servers to protect ticketInfo, yields tickets 
  | ClientSeal   // used by clients to protect received ticketInfo

// a simplification for length computations 

type alg = a:supported_alg { iv_length a 12 /\ tag_length a = 16 } 
noextract let overhead = 12 + 16

let default_alg: alg = AES256_GCM 

// a reasonable but arbitrary bound on serialized plaintexts, large
// enough to be RFC-compliant (larger than max serialized lengths for
// ticketInfo, pskInfo, plain-cookie) and still small enough for all
// algorithms.
let max_length = 1234 + 65535 

type plain_p = p:B.buffer UInt8.t{ B.length p <= max_length }
type cipher_p = p:B.buffer UInt8.t{ overhead <= B.length p /\ B.length p <= overhead + max_length }

/// TLS API 

/// We use some initialization to set up our invariant, then pass it
/// around forever after as part of the global TLS invariant. Also
/// useful for scrubbing the old keys.

val inv: FStar.HyperStack.mem -> Type0

val frame:
  h: FStar.HyperStack.mem ->
  l: B.loc ->
  h': FStar.HyperStack.mem ->
  Lemma
  (requires (B.modifies l h h' /\ inv h /\ B.loc_disjoint l (Mem.loc_store_region ())))
  (ensures (inv h'))
  [SMTPat (inv h'); SMTPat (B.modifies l h h')]

val reset: unit -> ST error_code 
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> r = Success ==> inv h1)

val set_key: 
  u: usage -> 
  a: alg -> 
  key: B.buffer UInt8.t { B.length key = key_length a } -> 
  ST error_code 
  (requires fun h0 -> B.live h0 key /\ inv h0)
  (ensures fun h0 r h1 -> B.modifies (Mem.loc_store_region ()) h0 h1 /\ inv h1)

/// The other functions are ad hoc and internal to TLS, making the use
/// of the global keys implicit. They all operate on (serialized)
/// bytes. We could use slices for additional robustness at the
/// API. We could use separate functions that encapsulate parsing and
/// serialization to facilitate their idealization by table lookups.

val encrypt: 
  u: usage -> 
  plain: plain_p -> 
  plain_len: UInt32.t { B.length plain = v plain_len } ->
  cipher: cipher_p { B.length cipher = overhead + v plain_len } ->
  Stack error_code 
  (requires fun h0 -> 
    inv h0 /\ // other EverCrypt.AEAD pre/inv follow from this module's invariant
    B.loc_disjoint (B.loc_buffer plain `B.loc_union` B.loc_buffer cipher) (Mem.loc_store_region ()) /\
    LowStar.Monotonic.Buffer.(all_live h0 [ buf plain; buf cipher ]) /\ 
    B.disjoint plain cipher)
  (ensures fun h0 r h1 -> 
    inv h1 /\ 
    // no need for concrete functional correctness 
    B.(modifies (loc_buffer cipher `loc_union` Mem.loc_store_region ()) h0 h1)) 

val decrypt:
  u: usage ->
  plain: plain_p -> 
  plain_len: UInt32.t { B.length plain = v plain_len } -> 
  cipher: cipher_p { B.length cipher = overhead + v plain_len } ->
  Stack error_code 
  (requires fun h0 -> 
    inv h0 /\ // other EverCrypt.AEAD pre/inv follow from this module's invariant
    B.loc_disjoint (B.loc_buffer plain `B.loc_union` B.loc_buffer cipher) (Mem.loc_store_region ()) /\
    LowStar.Monotonic.Buffer.(all_live h0 [ buf plain; buf cipher ]) /\
    B.disjoint plain cipher)
  (ensures fun h0 r h1 -> 
    inv h1 /\ 
    // no need for concrete functional correctness 
    B.(modifies (loc_buffer plain) h0 h1)) 
  
// TODO stateful concrete invariant

// TODO early idealization of these keys; not entirely clear how to
// deal with their conditional security.  A useful but non-urgent
// "unit test" for security verification.

// TODO in RFC: parsers for plain_cookie, pskInfo||pskrepr, and two
// flavors of ticketInfo (actually hard to accomodate).

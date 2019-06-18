module PSK

(*
This module idealizes the creation of application PSKs as
globally unique. Because the soundness of cryptographic indexes
depends on the uniqueness of PSKs, the model flag is used as
the idealization flag for this interface (allowing for simpler
extraction - representation of the abstract index is the PSK
itself when model is off).
*)

open FStar.Bytes
open FStar.Error

open Mem
open TLSError
open TLSConstants

module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module DT = DefineTable
module U32 = FStar.UInt32

module M = LowStar.Modifies
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

(* Main RFC data types for PSKs *)
include Parsers.PskIdentity
include Parsers.PskIdentity_identity
include Parsers.OfferedPsks

// The type of PSK identifiers (labels used in TLS messages)
type pskName = pskIdentity_identity

// The information associated with a PSK, i.e. time created,
// usage (PSK+DHE or PSK only), hash, and AEAD (for 0-RTT)
type pskInfo = TLS.Callbacks.pskInfo

// We rule out all PSK that do not have at least one non-null byte
// thus avoiding possible confusion with non-PSK for all possible hash algs
type non_zero (b:bytes) = exists i.{:pattern b.[i]} b.[i] <> 0z
val is_valid_psk: k:bytes -> (b:bool{b ==> non_zero k})

// The type of PSK indexes is abstract, but reveals equality
// When model is off, the representation of the index it the PSK
// itself, so we need to enforce confidentiality by type abstraction
inline_for_extraction noextract
val pskid: eqtype

val coerce:
  k:bytes{non_zero k} ->
  ST pskid
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> M.modifies loc_psk_region h0 h1)

val leak: i:pskid{not model} -> bytes
val name: pskid -> pskName

// FIXME turn abstract for confidentiality?
type ticket_age = UInt32.t
type obfuscated_ticket_age = UInt32.t

let default_obfuscated_age = 0ul

val encode_age: ticket_age -> UInt32.t -> obfuscated_ticket_age
val decode_age: obfuscated_ticket_age -> UInt32.t -> ticket_age

val lemma_age_encode_decode: t:ticket_age -> m:UInt32.t ->
  Lemma (decode_age (encode_age t m) m = t)


module PSK

open FStar.Bytes
open FStar.Error

open Mem
open TLSError
open TLS.Callbacks // now defining psk_identifier, pskInfo, tickets... 
open TLSConstants

module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module DT = DefineTable
module U32 = FStar.UInt32

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

(* Main RFC data types for PSKs *)
include Parsers.PskIdentity
include Parsers.PskIdentity_identity
include Parsers.OfferedPsks

// Concrete test to reject invalid PSKs
let is_valid_psk (k:bytes) : (b:bool{b ==> non_zero k}) =
  let rec aux (i:U32.t{U32.v i <= length k})
    : Tot (b:bool{b ==> non_zero k}) (decreases (length k - U32.v i))=
    if i = len k then false
    else (if k.[i] <> 0z then true else aux U32.(i +^ 1ul))
  in aux 0ul

type app_psk_entry (i:psk_identifier) =
  k:bytes{non_zero k} * pskInfo * bool

type psk_table_invariant (m:MDM.partial_dependent_map psk_identifier app_psk_entry) = True

/// Ideal table for application PSKs

noextract
private let psk_region:rgn = new_region tls_tables_region
private let app_psk_table : MDM.t psk_region psk_identifier app_psk_entry psk_table_invariant =
  MDM.alloc ()

type registered_psk (i:psk_identifier) =
  witnessed (MDM.defined app_psk_table i)

let valid_app_psk (ctx:pskInfo) (i:psk_identifier) (h:mem) =
  match MDM.sel (HS.sel h app_psk_table) i with
  | Some (_, c, _) -> b2t (c = ctx)
  | _ -> False

type pskid = i:psk_identifier{registered_psk i}

let coerce k =
  assume False; k

let leak k = k

// Temporary, to disentangle concrete identifier and crypto index
let name k =
  assume False; k

(*
Provisional support for the PSK extension
https://tlswg.github.io/tls13-spec/#rfc.section.4.2.10

The PSK table should include (at least for tickets)

  time_created: UInt32.t // the server's viewpoint
  time_accepted: UInt32.t // the client's viewpoint
  mask: UInt32.t
  livetime: UInt32.t

The authenticated property of the binder should includes

  ClientHello[ nonce, ... pskid, obfuscated_ticket_age] /\
  psk = lookup pskid
  ==>
  exists client.
    client.nonce = nonce /\
    let age = client.time_connected - psk.time_created in
    age <= psk.livetime /\
    obfuscated_ticket_age = encode_age age

Hence, the server authenticates age, and may filter 0RTT accordingly.

*)

let encode_age age mask = U32.(age +%^ mask)
let decode_age age mask = U32.(age -%^ mask)
let lemma_age_encode_decode t mask = ()

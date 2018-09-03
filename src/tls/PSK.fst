module PSK

open FStar.Bytes
open FStar.Error

open Mem
open TLSError
open TLSConstants

module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

// Has been moved to TLSConstants as it appears in config for ticket callbacks
type pskInfo = TLSConstants.pskInfo

// SESSION TICKET DATABASE (TLS 1.3)
// Note that the associated PSK are stored in the PSK table defined below in this file
let hostname : eqtype = string

let tlabel (h:hostname) = bytes

noextract
private let tregion:rgn = new_region tls_tables_region
private let tickets : MDM.t tregion hostname tlabel (fun _ -> True) =
  MDM.alloc ()

let lookup (h:hostname) = MDM.lookup tickets h
let extend (h:hostname) (t:tlabel h) = MDM.extend tickets h t

// SESSION TICKET DATABASE (TLS 1.2)
// Note that this table also stores the master secret
type session12 (tid:bytes) = protocolVersion * cipherSuite * ems:bool * ms:bytes
private let sessions12 : MDM.t tregion bytes session12 (fun _ -> True) =
  MDM.alloc ()

let s12_lookup (tid:bytes) = MDM.lookup sessions12 tid
let s12_extend (tid:bytes) (s:session12 tid) = MDM.extend sessions12 tid s

// *** PSK ***

// The constraints for PSK indexes are:
//  - must be public (as psk index appears in hsId, msId and derived keys)
//  - must support application-provided PSK as well as RMS-based PSK
//  - must support dynamic compromise; we want to prove KI of 1RT keys in PSK_DHE
//    even for leaked PSK (but not PSK-based auth obivously)
// Implementation style:
//  - pskid is the TLS PSK identifier, an internal index to the PSK table
//  - for tickets, the encrypted serialized state is the PSK identifier
//  - we store in the table the PSK context and compromise status

// The pskInfo type has been moved to TLSConstants as it appears in config
// for the new ticket callback API

let pskInfo_hash pi = pi.early_hash
let pskInfo_ae pi = pi.early_ae

// We rule out all PSK that do not have at least one non-null byte
// thus avoiding possible confusion with non-PSK for all possible hash algs
type app_psk (i:psk_identifier) =
  b:bytes{exists i.{:pattern b.[i]} b.[i] <> 0z}

type app_psk_entry (i:psk_identifier) =
  (app_psk i) * pskInfo * bool

// Global invariant on the PSK idealization table
// No longer necessary now that FStar.Monotonic.DependentMap uses eqtype
//type app_psk_injective (m:MDM.map' psk_identifier app_psk_entry) =
//  forall i1 i2.{:pattern (MDM.sel m i1); (MDM.sel m i2)}
//      Seq.equal i1 i2 <==> (match MDM.sel m i1, MDM.sel m i2 with
//                  | Some (psk1, pski1, h1), Some (psk2, pski2, h2) -> Seq.equal psk1 psk2 /\ h1 == h2
//                  | _ -> True)
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

let psk_value (i:pskid) : ST (app_psk i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  recall app_psk_table;
  testify (MDM.defined app_psk_table i);
  match MDM.lookup app_psk_table i with
  | Some (psk, _, _) -> psk

let psk_info (i:pskid) : ST (pskInfo)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  recall app_psk_table;
  testify (MDM.defined app_psk_table i);
  match MDM.lookup app_psk_table i with
  | Some (_, ctx, _) -> ctx

let psk_lookup (i:psk_identifier) : ST (option pskInfo)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    modifies_none h0 h1
    /\ (Some? r ==> registered_psk i)))
  =
  recall app_psk_table;
  match MDM.lookup app_psk_table i with
  | Some (_, ctx, _) ->
    assume(stable_on_t app_psk_table (MDM.defined app_psk_table i));
    mr_witness app_psk_table (MDM.defined app_psk_table i);
    Some ctx
  | None -> None

type honest_st (i:pskid) (h:mem) =
  (MDM.defined app_psk_table i h /\
  (let (_,_,b) = MDM.value_of app_psk_table i h in b = true))

type honest_psk (i:pskid) = witnessed (honest_st i)

// Generates a fresh PSK identity
val fresh_psk_id: unit -> ST psk_identifier
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    modifies_none h0 h1 /\
    MDM.fresh app_psk_table i h1))
let rec fresh_psk_id () =
  let id = Random.sample32 8ul in
  match MDM.lookup app_psk_table id with
  | None -> id
  | Some _ -> fresh_psk_id ()

// "Application PSK" generator (enforces empty session context)
// Usual caveat of random producing pairwise distinct keys (TODO)
let gen_psk (i:psk_identifier) (ctx:pskInfo)
  : ST unit
  (requires (fun h -> MDM.fresh app_psk_table i h))
  (ensures (fun h0 r h1 ->
    modifies_one psk_region h0 h1 /\
    registered_psk i /\
    honest_psk i))
  =
  let rand = Random.sample32 32ul in
  let h = get () in
  assume(MDM.fresh app_psk_table i h); // Frame new stateful RNG call
  recall app_psk_table;
  let psk = (abyte 1z) @| rand in
  assume(psk.[0ul] = 1z);
  let add : app_psk_entry i = (psk, ctx, true) in
  MDM.extend app_psk_table i add;
  MDM.contains_stable app_psk_table i add;
  let h = get () in
  cut(MDM.sel (HS.sel h app_psk_table) i == Some add);
  assume(stable_on_t app_psk_table (MDM.defined app_psk_table i));
  mr_witness app_psk_table (MDM.defined app_psk_table i);
  assume(stable_on_t app_psk_table (honest_st i));
  mr_witness app_psk_table (honest_st i)

let coerce_psk (i:psk_identifier) (ctx:pskInfo) (k:app_psk i)
  : ST unit
  (requires (fun h -> MDM.fresh app_psk_table i h))
  (ensures (fun h0 _ h1 ->
    modifies_one psk_region h0 h1 /\
    registered_psk i /\
    ~(honest_psk i)))
  =
  recall app_psk_table;
  let add : app_psk_entry i = (k, ctx, false) in
  MDM.extend app_psk_table i add;
  MDM.contains_stable app_psk_table i add;
  let h = get () in
  cut(MDM.sel (HS.sel h app_psk_table) i == Some add);
  admit()

let compatible_hash_ae_st (i:pskid) (ha:hash_alg) (ae:aeadAlg) (h:mem) =
  (MDM.defined app_psk_table i h /\
  (let (_,ctx,_) = MDM.value_of app_psk_table i h in
  ha = pskInfo_hash ctx /\ ae = pskInfo_ae ctx))

let compatible_hash_ae (i:pskid) (h:hash_alg) (a:aeadAlg) =
  witnessed (compatible_hash_ae_st i h a)

let compatible_info_st (i:pskid) (c:pskInfo) (h:mem) =
  (MDM.defined app_psk_table i h /\
  (let (_,ctx,_) = MDM.value_of app_psk_table i h in c = ctx))

let compatible_info (i:pskid) (c:pskInfo) =
  witnessed (compatible_info_st i c)

let verify_hash_ae (i:pskid) (ha:hash_alg) (ae:aeadAlg) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    b ==> compatible_hash_ae i ha ae))
  =
  recall app_psk_table;
  testify (MDM.defined app_psk_table i);
  match MDM.lookup app_psk_table i with
  | Some x ->
    let h = get() in
    cut(MDM.contains app_psk_table i x h);
    cut(MDM.value_of app_psk_table i h = x);
    let (_, ctx, _) = x in
    if pskInfo_hash ctx = ha && pskInfo_ae ctx = ae then
     begin
      cut(compatible_hash_ae_st i ha ae h);
      assume(stable_on_t app_psk_table (compatible_hash_ae_st i ha ae));
      mr_witness app_psk_table (compatible_hash_ae_st i ha ae);
      true
     end
    else false


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

type ticket_age = UInt32.t
type obfuscated_ticket_age = UInt32.t
let default_obfuscated_age = 0ul
open FStar.UInt32
let encode_age (t:ticket_age)  mask = t +%^ mask
let decode_age (t:obfuscated_ticket_age) mask = t -%^ mask

private let inverse_mask t mask: Lemma (decode_age (encode_age t mask) mask = t) = ()

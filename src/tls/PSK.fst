(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module PSK

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

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

type pskInfo = {
  time_created: int;
  allow_early_data: bool;      // New draft 13 flag
  allow_dhe_resumption: bool;  // New draft 13 flag
  allow_psk_resumption: bool;  // New draft 13 flag
  early_ae: aeadAlg;
  early_hash: Hashing.Spec.alg;  //CF could be more specific and use Hashing.alg
  identities: bytes * bytes;
}

let pskInfo_hash pi = pi.early_hash
let pskInfo_ae pi = pi.early_ae

type psk_identifier = identifier:bytes{length identifier < 65536}

// We rule out all PSK that do not have at least one non-null byte
// thus avoiding possible confusion with non-PSK for all possible hash algs
type app_psk (i:psk_identifier) =
  b:bytes{exists i.{:pattern index b i} index b i <> 0z}

type app_psk_entry (i:psk_identifier) =
  (app_psk i) * pskInfo * bool

// Global invariant on the PSK idealization table
// No longer necessary now that MonotoneMap uses eqtype
//type app_psk_injective (m:MM.map' psk_identifier app_psk_entry) =
//  forall i1 i2.{:pattern (MM.sel m i1); (MM.sel m i2)}
//      Seq.equal i1 i2 <==> (match MM.sel m i1, MM.sel m i2 with
//                  | Some (psk1, pski1, h1), Some (psk2, pski2, h2) -> Seq.equal psk1 psk2 /\ h1 == h2
//                  | _ -> True)
type psk_table_invariant (m:MM.map' psk_identifier app_psk_entry) = True

private let psk_region:rgn = new_region tls_tables_region
private let app_psk_table : MM.t psk_region psk_identifier app_psk_entry psk_table_invariant =
  MM.alloc #psk_region #psk_identifier #app_psk_entry #psk_table_invariant

type registered_psk (i:psk_identifier) =
  MR.witnessed (MM.defined app_psk_table i)

let valid_app_psk (ctx:pskInfo) (i:psk_identifier) (h:mem) =
  match MM.sel (MR.m_sel h app_psk_table) i with
  | Some (_, c, _) -> b2t (c = ctx)
  | _ -> False

type pskid = i:psk_identifier{registered_psk i}

let psk_value (i:pskid) : ST (app_psk i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  MR.m_recall app_psk_table;
  MR.testify (MM.defined app_psk_table i);
  match MM.lookup app_psk_table i with
  | Some (psk, _, _) -> psk

let psk_info (i:pskid) : ST (pskInfo)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  MR.m_recall app_psk_table;
  MR.testify (MM.defined app_psk_table i);
  match MM.lookup app_psk_table i with
  | Some (_, ctx, _) -> ctx

type honest_st (i:pskid) (h:mem) =
  (MM.defined app_psk_table i h /\
  (let (_,_,b) = MM.value app_psk_table i h in b = true))

type honest_psk (i:pskid) = MR.witnessed (honest_st i)

// Generates a fresh PSK identity
val fresh_psk_id: unit -> ST psk_identifier
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    modifies_none h0 h1 /\
    MM.fresh app_psk_table i h1))
let rec fresh_psk_id () =
  let id = CoreCrypto.random 8 in
  match MM.lookup app_psk_table id with
  | None -> id
  | Some _ -> fresh_psk_id ()

// "Application PSK" generator (enforces empty session context)
// Usual caveat of random producing pairwise distinct keys (TODO)
let gen_psk (i:psk_identifier) (ctx:pskInfo)
  : ST unit
  (requires (fun h -> MM.fresh app_psk_table i h))
  (ensures (fun h0 r h1 ->
    modifies_one psk_region h0 h1 /\
    registered_psk i /\
    honest_psk i))
  =
  MR.m_recall app_psk_table;
  let psk = (abyte 1z) @| CoreCrypto.random 32 in
  assume(index psk 0 = 1z);
  let add : app_psk_entry i = (psk, ctx, true) in
  MM.extend app_psk_table i add;
  MM.contains_stable app_psk_table i add;
  let h = ST.get () in
  cut(MM.sel (MR.m_sel h app_psk_table) i == Some add);
  assume(MR.stable_on_t app_psk_table (honest_st i));
  MR.witness app_psk_table (honest_st i)

let coerce_psk (i:psk_identifier) (ctx:pskInfo) (k:app_psk i)
  : ST unit
  (requires (fun h -> MM.fresh app_psk_table i h))
  (ensures (fun h0 _ h1 ->
    modifies_one psk_region h0 h1 /\
    registered_psk i /\
    ~(honest_psk i)))
  =
  MR.m_recall app_psk_table;
  let add : app_psk_entry i = (k, ctx, false) in
  MM.extend app_psk_table i add;
  MM.contains_stable app_psk_table i add;
  let h = ST.get () in
  cut(MM.sel (MR.m_sel h app_psk_table) i == Some add);
  admit()

let compatible_hash_st (i:pskid) (a:hash_alg) (h:mem) =
  (MM.defined app_psk_table i h /\
  (let (_,ctx,_) = MM.value app_psk_table i h in a = pskInfo_hash ctx))

let compatible_hash (i:pskid) (a:hash_alg) =
  MR.witnessed (compatible_hash_st i a)

let compatible_info_st (i:pskid) (c:pskInfo) (h:mem) =
  (MM.defined app_psk_table i h /\
  (let (_,ctx,_) = MM.value app_psk_table i h in c = ctx))

let compatible_info (i:pskid) (c:pskInfo) =
  MR.witnessed (compatible_info_st i c)

let verify_hash (i:pskid) (a:hash_alg) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    b ==> compatible_hash i a))
  =
  MR.m_recall app_psk_table;
  MR.testify (MM.defined app_psk_table i);
  match MM.lookup app_psk_table i with
  | Some x ->
    let h = ST.get() in
    cut(MM.contains app_psk_table i x h);
    cut(MM.value app_psk_table i h = x);
    let (_, ctx, _) = x in
    if pskInfo_hash ctx = a then
     begin
      cut(compatible_hash_st i a h);
      assume(MR.stable_on_t app_psk_table (compatible_hash_st i a));
      MR.witness app_psk_table (compatible_hash_st i a);
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

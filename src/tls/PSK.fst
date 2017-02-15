(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
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
  early_hash: hash_alg;  //CF could be more specific and use Hashing.alg
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

let psk_value (i:pskid) : St (app_psk i) =
  MR.m_recall app_psk_table;
  MR.testify (MM.defined app_psk_table i);
  match MM.lookup app_psk_table i with
  | Some (psk, _, _) -> psk

// Attacker interface
//let leak i:ex_app_psk =
//  let (v, _, l) = Some?.v (MM.lookup app_psk_table i) in
//  l := true; v

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
    registered_psk i))
  =
  MR.m_recall app_psk_table;
  let psk = (abyte 1z) @| CoreCrypto.random 32 in
  assume(index psk 0 = 1z);
  let add : app_psk_entry i = (psk, ctx, true) in
  MM.extend app_psk_table i add

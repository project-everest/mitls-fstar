module PSK

open FStar.Heap
open FStar.HyperHeap

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

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
  early_hash: CoreCrypto.hash_alg;
  identities: bytes * bytes;
}

let pskInfo_hash pi = pi.early_hash
let pskInfo_ae pi = pi.early_ae

type psk_identifier = identifier:bytes{length identifier < 65536}

// We rule out all PSK that do not have at least one non-null byte
// thus avoiding possible confusion with non-PSK for all possible hash algs
let app_psk (i:psk_identifier) =
  b:bytes{exists i.{:pattern index b i} index b i <> 0z}

type app_psk_entry (i:psk_identifier) =
  (app_psk i) * pskInfo * leaked:(rref tls_tables_region bool)


// ADL: not sure why b2t is required there
let app_psk_injective (m:MM.map' psk_identifier app_psk_entry) =
  forall i1 i2.{:pattern (MM.sel m i1); (MM.sel m i2)}
      Seq.equal i1 i2 <==> (match MM.sel m i1, MM.sel m i2 with
                  | Some (psk1, _, _), Some (psk2, _, _) -> Seq.equal psk1 psk2
                  | _ -> True)

private let app_psk_table : MM.t tls_tables_region psk_identifier app_psk_entry app_psk_injective =
  MM.alloc #TLSConstants.tls_tables_region #psk_identifier #app_psk_entry #app_psk_injective

let fresh_pskid i h =
  MM.sel (MR.m_sel h app_psk_table) i = None

let registered_app_psk (i:psk_identifier) (h:HH.t) =
  b2t (is_Some (MM.sel (MR.m_sel h app_psk_table) i))

let valid_app_psk (ctx:pskInfo) (i:psk_identifier) (h:HH.t) =
  match MM.sel (MR.m_sel h app_psk_table) i with
  | Some (_, c, _) -> b2t (c = ctx)
  | _ -> False

type ex_app_psk = i:psk_identifier{MR.witnessed (registered_app_psk i)}

let fresh_psk psk (h:HH.t) =
  forall i. match MM.sel (MR.m_sel h app_psk_table) i with
       | Some (psk', _, _) -> ~ (Seq.equal psk psk')
       | None -> True

let app_psk_value (i:ex_app_psk) : St (app_psk i) =
  let (psk, _, _) = Some.v (MM.lookup app_psk_table i) in psk

// Attacker interface
//let leak i:ex_app_psk =
//  let (v, _, l) = Some.v (MM.lookup app_psk_table i) in
//  l := true; v

// Generates a fresh PSK identity
val fresh_psk_id: unit -> ST psk_identifier
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    h1 = h0 /\ fresh_pskid i h1))
let rec fresh_psk_id () =
  let id = CoreCrypto.random 8 in
  match MM.lookup app_psk_table id with
  | None -> id
  | Some _ -> fresh_psk_id ()

// "Application PSK" generator (enforces empty session context)
// Usual caveat of random producing pairwise distinct keys (TODO)

let gen_psk (i:psk_identifier) (ctx:pskInfo)
  : ST unit
  (requires (fun h -> fresh_pskid i h))
  (ensures (fun h0 r h1 ->
    modifies (Set.singleton tls_tables_region) h0 h1
    /\ modifies_rref tls_tables_region !{HH.as_ref (MR.as_rref app_psk_table)} h0 h1
    /\ registered_app_psk i h1))
  =
  MR.m_recall app_psk_table;
  let psk : app_psk i = CoreCrypto.random 32 in
  let leaked = ralloc tls_tables_region false in
  let add : app_psk_entry i = (psk, ctx, leaked) in
  MM.extend app_psk_table i add



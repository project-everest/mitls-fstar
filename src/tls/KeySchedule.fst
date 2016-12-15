module KeySchedule
(*the top level key schedule module, it should not expose secrets to Handshake *)

(* the goal is to keep ephemerals like eph_s and eph_c as currently defined 
   in Handshake local *)

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.Set  

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range
open HandshakeMessages
open StatefulLHAE
open HKDF
open Negotiation // We only depend minimally on Nego
open Epochs	 // We only depend minimally on Epochs 
open PSK

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

(*
let secretLabel = function
  | EarlySecret _ _ -> "early traffic secret"
  | HandshakeSecret _ _ -> "handshake traffic secret"
  | ApplicationSecret _ _ -> "application traffic secret"
  | ResumptionSecret _ _ -> "resumption master secret"
  | ExporterSecret _ _ -> "exporter master secret"
*)

(* A flag for runtime debugging of computed keys.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false *)
inline_for_extraction let ks_debug = false

let print_share k : St bool =
  let kb = CommonDH.serialize_raw k in
  let kh = Platform.Bytes.hex_of_bytes kb in
  IO.debug_print_string ("Share: "^kh^"\n")

let keyLabel = function
  | EarlyTrafficKey -> "early traffic key expansion"
  | EarlyApplicationDataKey -> "early application data key expansion"
  | HandshakeKey -> "handshake key expansion"
  | ApplicationDataKey -> "application data key expansion"
  | ApplicationRekey -> "application data key expansion"

(***********************************************************
     Internal (resumption) PSKs, indexed by rmsId
************************************************************)


(********************************************
*    Resumption PSK is disabled for now     *
*********************************************

abstract type res_psk (i:rmsId) =
  b:bytes{exists i.{:pattern index b i} index b i <> 0z}

abstract type res_context (i:rmsId) =
  b:bytes{length b = CoreCrypto.hashSize (rmsId_hash i)}

private type res_psk_entry (i:rmsId) =
  (res_psk i) * (res_context i) * ctx:psk_context * leaked:(rref tls_tables_region bool)

let res_psk_injective (m:MM.map' rmsId res_psk_entry) =
  forall i1 i2.{:pattern (MM.sel m i1); (MM.sel m i2)}
       i1 = i2 <==> (match MM.sel m i1, MM.sel m i2 with
                  | Some (psk1, _, _, _), Some (psk2, _, _, _) -> b2t (equalBytes psk1 psk2)
                  | _ -> True)

let res_psk_table : MM.t tls_tables_region rmsId res_psk_entry res_psk_injective =
  MM.alloc #TLSConstants.tls_tables_region #rmsId #res_psk_entry #res_psk_injective

let registered_res_psk (i:rmsId) (h:HH.t) =
  b2t (Some? (MM.sel (MR.m_sel h res_psk_table) i))

let res_psk_context (i:rmsId{registered_res_psk i}) =
  let (_, _, c, _) = Some.v (MM.sel res_psk_table i) in c

private let res_psk_value (i:rmsId{registered_res_psk i}) =
  let (psk, _, _, _) = Some.v (MM.sel res_psk_table i) in psk


**)

// PSK (internal/external multiplex, abstract)
// Note that application PSK is externally defined but should
// be idealized together with KS
abstract let psk (i:esId) =
  b:bytes{length b = CoreCrypto.hashSize (esId_hash i)}

let get_psk_info (i:esId) =
  match i with
  | ResumptionPSK c _ -> c
  | ApplicationPSK c _ -> c
     

// Total by construction
private let get_psk (i:esId) =
  match i with
//  | ResumptionPSK i -> res_psk_value i
  | ApplicationPSK _ pskid ->
     let p : psk i = app_psk_value pskid in p

// Agile "0" hash
private let zH h =
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  CoreCrypto.hash h zeroes

#set-options "--lax"

// Resumption context
let esId_rc (i:esId) =
  match i with
//  | ResumptionPSK i ->
//    let (_, rc, _, _) = Some.v (MM.sel res_psk_table i) in rc
  | ApplicationPSK _ _ -> zH (esId_hash i)

let hsId_rc = function
  | HSID_DHE h _ _ -> zH h
  | HSID_PSK i | HSID_PSK_DHE i _ _ -> esId_rc i

let asId_rc = function
  | ASID hsId -> hsId_rc hsId

// miTLS 0.9:
// ==========
// PRF (type pms) -> TLSInfo (type id) -> KEF (extract pms)
//                     \ StatefulLHAE (coerce id) / 
// TODO rework old 1.2 types
type ms = bytes
type pms = bytes 

// Early secret (abstract)
abstract type es (i:esId) =
  b:bytes{length b = CoreCrypto.hashSize (esId_hash i)}

// Handshake secret (abstract)
abstract type hs (i:hsId) =
  b:bytes{length b = CoreCrypto.hashSize (hsId_hash i)}

abstract type fink (i:finishedId) =
  b:bytes{length b = CoreCrypto.hashSize (finishedId_hash i)}

// TLS 1.3 master secret (abstract)
abstract type ams (i:asId) =
  b:bytes{length b = CoreCrypto.hashSize (asId_hash i)}

abstract type expander (i:expandId) =
  b:bytes{length b = CoreCrypto.hashSize (expandId_hash i)}

abstract type rekey_secret (i:rekeyId) =
  b:bytes{length b = CoreCrypto.hashSize (rekeyId_hash i)}

abstract type rms (i:rmsId) =
  b:bytes{length b = CoreCrypto.hashSize (rmsId_hash i)}

type ems (i:exportId) =
  b:bytes{length b = CoreCrypto.hashSize (exportId_hash i)}

// TODO this is superseeded by StAE.state i
// but I'm waiting for it to be tester to switch over
// TODO use the newer index types
type recordInstance =
  | StAEInstance: #id:TLSInfo.id -> StAE.reader id -> StAE.writer id -> recordInstance

(* 2 choices - I prefer the second:
   (1) replace recordInstance in this module with Epochs.epoch, but that requires dependence on more than just $id
   (2) redefine recordInstance as follows, and then import epoch_region_inv over here from Epochs:
type recordInstance (rgn:rid) (n:TLSInfo.random) =
| RI: #id:StAE.id -> r:StAE.reader (peerId id) -> w:StAE.writer id{epoch_region_inv' rgn r w /\ I.nonce_of_id id = n} -> recordInstance rgn n

In (2) we would define Epochs.epoch as:
type epoch (hs_rgn:rgn) (n:TLSInfo.random) =
  | Epoch: h:handshake ->
           r:recordInstance hs_rgn n ->
           epich hs_rgn n
*)

// Note from old miTLS (in TLSInfo.fst)
// type id = {
//  msId   : msId;            // the index of the master secret used for key derivation
//  kdfAlg : kdfAlg_t;          // the KDF algorithm used for key derivation
//  pv     : protocolVersion; // should be part of aeAlg
//  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
//  csrConn: csRands;         // the client-server random of the connection
//  ext: negotiatedExtensions;// the extensions negotiated for the current session
//  writer : role             // the role of the writer
//  }

type ks_alpha12 = pv:protocolVersion * cs:cipherSuite * ems:bool
type ks_alpha13 = ae:aeadAlg * h:CoreCrypto.hash_alg

type ks_client_state =
| C_Init: cr:random -> ks_client_state
| C_12_Resume_CH: cr:random -> si:sessionInfo -> msId:TLSInfo.msId -> ms:ms -> ks_client_state
| C_12_Full_CH: cr:random -> ks_client_state
| C_12_wait_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.pmsId -> pms:pms -> ks_client_state
| C_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_client_state
| C_13_wait_CH: cr:random -> i:esId -> gs:list (namedGroup * CommonDH.key) -> ks_client_state
| C_13_wait_SH: cr:random -> es:option ( i:esId & es i ) -> cfk0:option ( i:finishedId & fink i ) -> gs:list (namedGroup * CommonDH.key) -> ks_client_state
| C_13_wait_SF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:finishedId & sfk:fink i ) -> ( i:asId & ams:ams i ) -> ks_client_state
| C_13_wait_CF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:asId & ams:ams i ) -> ( i:rekeyId & rekey_secret i ) -> ( i:finishedId & latecfk:fink i ) -> ks_client_state
| C_13_postHS: alpha:ks_alpha13 -> ( i:finishedId & fink i ) -> ( i:rekeyId & rekey_secret i ) -> ( i:rmsId & rms i ) -> ( i:exportId & ems i ) -> ks_client_state
| C_Done

type ks_server_state =
| S_Init: sr:random -> ks_server_state
| S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha12 -> our_share:CommonDH.key -> ks_server_state
| S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha12 -> ks_server_state
| S_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_server_state
| S_13_wait_SH: alpha:ks_alpha13 -> cr:random -> sr:random -> es:option ( i:esId & es i ) -> cfk0:option ( i:finishedId & fink i ) -> hs:( i:hsId & hs i ) -> ks_server_state
| S_13_wait_SF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:finishedId & sfk:fink i ) -> ( i:asId & ams:ams i ) -> ks_server_state
| S_13_wait_CF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:asId & ams i ) -> ( i:rekeyId & rekey_secret i ) -> ( i:finishedId & latecfk:fink i ) -> ks_server_state
| S_13_postHS: alpha:ks_alpha13 -> ( i:finishedId & fink i ) -> ( i:rekeyId & rekey_secret i ) -> ( i:rmsId & rms i ) -> ( i:exportId & ems i ) -> ks_server_state
| S_Done

// Reflecting state separation from HS
type ks_state =
| C: s:ks_client_state -> ks_state
| S: s:ks_server_state -> ks_state

// KeySchedule instances
(*
 * AR: changing state from rref to ref, with region captured in the refinement.
 *)
type ks =
| KS: #region:rid -> state:(ref ks_state){HS.MkRef?.id state = region} -> hsl:HandshakeLog.log -> ks

// Extract keys and IVs from a derived 1.3 secret
private let keygen_13 h secret phase ae : bytes * bytes * bytes * bytes =
  let kS = CoreCrypto.aeadKeySize ae in
  let iS = CoreCrypto.aeadRealIVSize ae in
  let f x y = HKDF.hkdf_expand_label h secret (phase ^ x) empty_bytes y in
  let cekb = f ", client write key" kS in
  let civb = f ", client write iv" iS in
  let sekb = f ", server write key" kS in
  let sivb = f ", server write iv" iS in
  (cekb, civb, sekb, sivb)

// Extract finished keys
private let finished_13 h secret : bytes*bytes =
  let hL = CoreCrypto.hashSize h in
  let cfk = HKDF.hkdf_expand_label h secret "client finished" empty_bytes hL in
  let sfk = HKDF.hkdf_expand_label h secret "server finished" empty_bytes hL in
  (cfk, sfk)

// Diffie-Hellman computation
private let s13_dh gn gxb =
  let gx = match gn with
    | SEC ec ->
      let g = CommonDH.ECP (ECGroup.params_of_group ec) in
      let Some gx = CommonDH.parse g gxb in gx
    | FFDHE ff ->
      let g = CommonDH.FFP (DHGroup.params_of_group (DHGroup.Named ff)) in
      let Some gx =  CommonDH.parse g gxb in gx
  in let gy, gxy = CommonDH.dh_responder gx in
  (gy, gx, gxy)

val ks_client_random: ks:ks -> ST random
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 _ h1 -> h0 = h1)
let ks_client_random ks =
  let KS #rid st hsl = ks in
  let C (C_Init cr) = !st in cr

val ks_server_random: ks:ks -> ST random
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss))
  (ensures fun h0 _ h1 -> h0 = h1)
let ks_server_random ks =
  let KS #rid st hsl = ks in
  let S (S_Init sr) = !st in sr

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> role -> hsl:HandshakeLog.log -> ST (ks * random)
  (requires fun h -> rid<>root)
  (ensures fun h0 (r,_) h1 ->
    let KS #ks_region state hsl = r in
    stronger_fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref state} (HS.HS?.h h0) (HS.HS?.h h1))

let create #rid r hsl =
  ST.recall_region rid;
  let ks_region = new_region rid in 
  let nonce = Nonce.mkHelloRandom r ks_region in
  let istate = match r with
    | Client -> C (C_Init nonce)
    | Server -> S (S_Init nonce) in
  (KS #ks_region (ralloc ks_region istate) hsl), nonce

val ks_client_13_1rtt_init: ks:ks -> list (g:namedGroup{SEC? g \/ FFDHE? g}) -> ST (list (namedGroup * bytes))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st hsl = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

val map_ST: ('a -> St 'b) -> list 'a -> St (list 'b)
let rec map_ST f x = match x with
  | [] -> []
  | a::tl -> f a :: map_ST f tl

let ks_client_13_1rtt_init ks groups =
  let KS #rid st hsl = ks in
  let C (C_Init cr) = !st in
  let kg x = x, (match x with
    | SEC ecg -> CommonDH.keygen (CommonDH.ECDH ecg)
    | FFDHE g -> CommonDH.keygen (CommonDH.FFDH (DHGroup.Named g))) in
  let gs = map_ST kg groups in
  st := C (C_13_wait_SH cr None None gs);
  let pub (x,y) = x, CommonDH.serialize_raw y in
  List.Tot.map pub gs

val ks_client_13_0rtt_init: ks:ks -> i:esId -> list (g:namedGroup{SEC? g \/ FFDHE? g}) -> ST (list (namedGroup * bytes))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st hsl = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_13_0rtt_init ks esId groups =
  let KS #rid st hsl = ks in
  let C (C_Init cr) = !st in
  let kg x = x, (match x with
    | SEC ecg -> CommonDH.keygen (CommonDH.ECDH ecg)
    | FFDHE g -> CommonDH.keygen (CommonDH.FFDH (DHGroup.Named g))) in
  let gs = map_ST kg groups in
  st := C (C_13_wait_CH cr esId gs);
  let pub (x,y) = x, CommonDH.serialize_raw y in
  List.Tot.map pub gs

// Derive the early keys from the early secret
let ks_client_13_0rtt_ch ks esId
  : ST (recordInstance * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st hsl = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1)) =
  let KS #rid st hsl = ks in
  let C (C_13_wait_CH cr esId gs) = !st in
  let psk = get_psk esId in
  let c = get_psk_info esId in
  let h, ae = c.early_hash, c.early_ae in

  let expandId = EarlySecretID esId in
  let loginfo = LogInfo_CH ({li_ch_cr = cr; li_ch_psk = c}) in
  let hashed_log = HandshakeLog.getHash hsl h in
  // TODO verify log_info loginfo hashed_log

  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let es : es esId = HKDF.hkdf_extract h zeroes psk in
  let sh_rctx = hashed_log @| (esId_rc esId) in
  let es_derived = HKDF.hkdf_expand_label h es "early traffic secret" sh_rctx hL in

  // Expand all keys from the derived early secret
  let (ck,civ, _, _) = keygen_13 h es_derived "early traffic key expansion" ae in
  let (ck',civ', _, _) = keygen_13 h es_derived "early application data key expansion" ae in

  let efId = FinishedID expandId EarlyFinished Client loginfo hashed_log in
  let (cfk0, _) = finished_13 h es_derived in
  let cfk0 : fink efId = cfk0 in

  let id = ID13 (KeyID expandId EarlyTrafficKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_hs = StAEInstance r rw in

  let id = ID13 (KeyID expandId EarlyApplicationDataKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck' in
  let civ: StreamAE.iv id  = civ' in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_d = StAEInstance r rw in

  st := C (C_13_wait_SH cr (Some (| esId, es |)) (Some (| efId, cfk0 |)) gs);
  (early_hs, early_d)

val ks_client_13_0rtt_finished: ks:ks -> ST (cvd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss))
  (ensures fun h0 r h1 -> h0 == h1)

// Compute 0-RTT finished
let ks_client_13_0rtt_finished ks =
  let KS #rid st hsl = ks in
  let C (C_13_wait_SH cr (Some (| esId, es |)) (Some (| finishedId, cfk |)) gs) = !st in
  let h = esId_hash esId in
  CoreCrypto.hmac h cfk ((HandshakeLog.getHash hsl h) @| (esId_rc esId))

// Called before sending client hello
// (the external style of resumption may become internal to protect ms abstraction)
val ks_client_12_init: ks:ks -> ST (option sessionInfo)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

// TODO resumption support
let ks_client_12_init ks =
  let KS #rid st _ = ks in
  let C (C_Init cr) = !st in
  let osi, ns = None, (C (C_12_Full_CH cr)) in
//    match cfg.resuming with
//    | None -> None, (KS_C_12_Full_CH cr)
//    | Some shard ->
//      (match DB.lookup shard with TODO
//      | Some (si, msId, ms) -> (Some si), (KS_C_12_Resume_CH cr si msId ms)
//      | None -> None, (KS_C_12_Full_CH cr)) in
  (KS?.state ks) := ns;
  osi

val ks_server_12_init_dh: ks:ks -> cr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> group:namedGroup -> ST CommonDH.key
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_12_init_dh ks cr pv cs ems group =
  let KS #region st _ = ks in
  let S (S_Init sr) = !st in
  let group = (match group with 
      	       | SEC c -> CommonDH.ECDH c
	       | FFDHE f -> CommonDH.FFDH (DHGroup.Named f)) in
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen group in
  let csr = cr @| sr in
  st := S (S_12_wait_CKE_DH csr (pv, cs, ems) our_share);
  our_share

val ks_server_13_0rtt_init: ks:ks -> cr:random -> i:esId -> cs:cipherSuite -> gn:namedGroup -> gxb:bytes -> ST (recordInstance * recordInstance * our_share:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs /\ (let CipherSuite kex _ _ = cs in
       (kex = Kex_PSK_DHE \/ kex = Kex_PSK_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_13_0rtt_init ks cr esId cs gn gxb =
  let KS #region st hsl = ks in
  let S (S_Init sr) = !st in
  let psk = get_psk esId in
  let c = get_psk_info esId in
  let h, ae = c.early_hash, c.early_ae in

  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let es : es esId = HKDF.hkdf_extract h zeroes psk in

  let expandId = EarlySecretID esId in
  let loginfo = LogInfo_CH ({li_ch_cr = cr; li_ch_psk = c}) in
  let hashed_log = HandshakeLog.getHash hsl h in
  // TODO verify log_info loginfo hashed_log

  let sh_rctx = hashed_log @| (esId_rc esId) in
  let es_derived = HKDF.hkdf_expand_label h es "early traffic secret" sh_rctx hL in
  let (ck,civ, _, _) = keygen_13 h es_derived "early traffic key expansion" ae in
  let (ck',civ', _, _) = keygen_13 h es_derived "early application data key expansion" ae in

  let efId = FinishedID expandId EarlyFinished Client loginfo hashed_log in
  let (cfk0, _) = finished_13 h es_derived in
  let cfk0 : fink efId = cfk0 in

  let id = ID13 (KeyID expandId EarlyTrafficKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_hs = StAEInstance r rw in

  let id = ID13 (KeyID expandId EarlyApplicationDataKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck' in
  let civ: StreamAE.iv id  = civ' in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_d = StAEInstance r rw in

  let our_share, peer_share, gxy = s13_dh gn gxb in
  let hsId = HSID_PSK_DHE esId (CommonDH.share_of_key peer_share) (CommonDH.share_of_key our_share) in
  let hs : hs hsId = HKDF.hkdf_extract h es gxy in
  st := S (S_13_wait_SH (ae, h) cr sr (Some (| esId, es |)) (Some (| efId, cfk0 |)) (| hsId, hs |));
  let ourshare = CommonDH.serialize_raw our_share in
  early_hs, early_d, ourshare

val ks_server_13_1rtt_psk_init: ks:ks -> cr:random -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_PSK)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

val ks_server_13_1rtt_init: ks:ks -> cr:random -> cs:cipherSuite -> gn:namedGroup -> gxb:bytes -> ST (our_share:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_13_1rtt_init ks cr cs gn gxb =
  let KS #region st _ = ks in
  let S (S_Init sr) = !st in
  let CipherSuite _ _ (AEAD ae h) = cs in
  let our_share, peer_share, gxy = s13_dh gn gxb in
  let hsId = HSID_DHE h (CommonDH.share_of_key peer_share) (CommonDH.share_of_key our_share) in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let es = HKDF.hkdf_extract h zeroes zeroes in
  let hs : hs hsId = HKDF.hkdf_extract h es gxy in
  st := S (S_13_wait_SH (ae, h) cr sr None None (| hsId, hs |));
  CommonDH.serialize_raw our_share

val ks_server_13_sh: ks:ks -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_13_sh ks =
  let KS #region st hsl = ks in
  let S (S_13_wait_SH (ae, h) cr sr _ _ (| hsId, hs |)) = !st in
  let expandId = HandshakeSecretID hsId in
  let loginfo = LogInfo_SH ({
    li_sh_cr = cr;
    li_sh_sr = sr;
    li_sh_ae = AEAD ae h;
  }) in
  let hashed_log = HandshakeLog.getHash hsl h in
  // TODO log_info loginfo hashed_log

  // Derived handshake secret
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let sh_rctx = hashed_log @| (hsId_rc hsId) in
  let hs_derived = HKDF.hkdf_expand_label h hs "handshake traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h hs_derived "handshake key expansion" ae in

  // Handshake traffic keys
  let id = ID13 (KeyID expandId HandshakeKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HyperHeap.root id (skv @| siv) in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in

  // Finished keys
  let cfkId = FinishedID expandId HandshakeFinished Client loginfo hashed_log in
  let sfkId = FinishedID expandId HandshakeFinished Server loginfo hashed_log in
  let (cfk1, sfk1) = finished_13 h hs_derived in
  let cfk1 : fink cfkId = cfk1 in
  let sfk1 : fink sfkId = sfk1 in

  // Replace handshake secret with application master secret
  let amsId = ASID hsId in
  let ams : ams amsId = HKDF.hkdf_extract h hs zeroes in

  st := S (S_13_wait_SF (ae, h) (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| amsId, ams |));
  StAEInstance r w

// log is the raw HS log, used for EMS derivation
val ks_server_12_cke_dh: ks:ks -> peer_share:bytes -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_12_wait_CKE_DH? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_12_cke_dh ks gxb =
  let KS #region st hsl = ks in
  let S (S_12_wait_CKE_DH csr alpha our_share) = !st in
  let dhp = CommonDH.key_params our_share in
  let Some gx = CommonDH.parse dhp gxb in
  let (pv, cs, ems) = alpha in
  let pmsb = CommonDH.dh_initiator our_share gx in
  let () =
    if ks_debug then
      let _ = print_share our_share in
      let _ = print_share gx in
      let _ = IO.debug_print_string ("PMS: "^(Platform.Bytes.print_bytes pmsb)^"\n") in
      ()
    else () in
  let pmsId = PMS.DHPMS(dhp, (CommonDH.share_of_key our_share), (CommonDH.share_of_key gx), PMS. ConcreteDHPMS(pmsb)) in
  let kef = kefAlg pv cs ems in
  let msId, ms =
    if ems then
      let Hash h = sessionHashAlg pv cs in // TODO TLS 1.0
      let log = HandshakeLog.getHash hsl h in
      let ms = TLSPRF.prf (pv,cs) pmsb (utf8 "extended master secret") log 48 in
      let msId = ExtendedMS pmsId log kef in
      (msId, ms)
    else
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS pmsId csr kef in
      (msId, ms) in
   let _ =
     if ks_debug then
      IO.debug_print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n")
     else false in
   st := S (S_12_has_MS csr alpha msId ms)

// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val ks_client_12_resume: ks:ks -> random -> pv:protocolVersion -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_12_Resume_CH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_resume ks sr pv cs =
  let KS #region st _ = ks in
  let C (C_12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extensions.ne_extended_ms in
  st := C (C_12_has_MS csr (pv, cs, ems) msId ms)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

val ks_client_13_sh: ks:ks -> cs:cipherSuite -> gy:(namedGroup * bytes) -> accept_early_data:bool -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss) /\ 
    // Ensure consistency of ae/h if 0-RTT data is accepted
    (let C_13_wait_SH _ ei _ _ = C?.s kss in
     match ei with | None -> True | Some (| id, _ |) ->
       let CipherSuite _ _ (AEAD ae h) = cs in
// TODO lift app_psk_hash, app_psk_ae to resumption PSK
//       let ctxt = get_psk_info id in
//       accept_early_data ==> ctxt.early_ae = ae /\ ctxt.early_hash = h
     True))
  (ensures fun h0 r h1 ->
    let KS #rid st hsl = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

// ServerHello log breakpoint (client)
let ks_client_13_sh ks cs (gs, gyb) accept_ed =
  let KS #region st hsl = ks in
  let C (C_13_wait_SH cr early_info early_fin gc) = !st in
  let Some (_, gx) = List.Tot.find (fun (gc,_) -> gc = gs) gc in
  let Some gy = CommonDH.parse (CommonDH.key_params gx) gyb in
  let gxy = CommonDH.dh_initiator gx gy in
  let CipherSuite _ _ (AEAD ae h) = cs in

  let loginfo = LogInfo_SH ({li_sh_cr = cr; li_sh_sr = cr; li_sh_ae = AEAD ae h;}) in // TODO
  let hashed_log = HandshakeLog.getHash hsl h in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  // Early secret: must derive zero here as hash is not known before
  let es =
    match early_info, accept_ed with
    | Some (| _, es |), true -> es
    | _ -> HKDF.hkdf_extract h zeroes zeroes
  in

  // Convert keys to share for public index
  let is = CommonDH.share_of_key gx in
  let rs = CommonDH.share_of_key gy in

  let hsId = match early_info with
    | None -> HSID_DHE h is rs
    | Some (| esId, _ |) -> HSID_PSK_DHE esId is rs in
  let hs : hs hsId = HKDF.hkdf_extract h es gxy in
  let expandId = HandshakeSecretID hsId in

  // Derived handshake secret
  let sh_rctx = hashed_log @| (hsId_rc hsId) in
  let hs_derived = HKDF.hkdf_expand_label h hs "handshake traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h hs_derived "handshake key expansion" ae in

  // Finished MAC keys (TODO coerce from HMAC)
  let cfkId = FinishedID expandId HandshakeFinished Client loginfo hashed_log in
  let sfkId = FinishedID expandId HandshakeFinished Server loginfo hashed_log in
  let (cfk, sfk) = finished_13 h hs_derived in
  let cfk1 : fink cfkId = cfk in
  let sfk1 : fink sfkId = sfk in

  // Application master secret
  let asId = ASID hsId in
  let ams : ams asId = HKDF.hkdf_extract h hs zeroes in

  let id = ID13 (KeyID expandId HandshakeKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let rw = StAE.coerce HyperHeap.root id (skv @| siv) in
  let r = StAE.genReader HyperHeap.root rw in
  st := C (C_13_wait_SF (ae, h) (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| asId, ams |));
  StAEInstance r w

(*************** FINISHED MAC COMPUTATION **********************)

let ks_client_13_server_finished ks
  : ST (svd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 -> h0 == h1)
  =
  let KS #region st hsl = ks in
  let C (C_13_wait_SF (_, h) _ (| _, sfk |) (| asId, _ |)) = !st in
  CoreCrypto.hmac h sfk ((HandshakeLog.getHash hsl h) @| (asId_rc asId))

let ks_client_13_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_CF? (C?.s kss))
  (ensures fun h0 r h1 -> h0 == h1)
  =
  let KS #region st hsl = ks in
  let C (C_13_wait_CF (_, h) (| _, cfk |) (| asId, _ |) _ _) = !st in
  CoreCrypto.hmac h cfk ((HandshakeLog.getHash hsl h) @| (asId_rc asId))

let ks_server_13_server_finished ks
  : ST (svd:bytes)
  (requires (fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SF? (S?.s kss)))
  (ensures (fun h0 _ h1 -> h0 = h1)) =
  let KS #region st hsl = ks in
  let S (S_13_wait_SF (ae, h) _ (| sfkId, sfk |) (| asId, _ |)) = !st in
  CoreCrypto.hmac h sfk ((HandshakeLog.getHash hsl h) @| (asId_rc asId))

let ks_server_13_client_finished ks
  : ST (cvd:bytes)
  (requires (fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_CF? (S?.s kss)))
  (ensures (fun h0 _ h1 -> h0 = h1)) =
  let KS #region st hsl = ks in
  let S (S_13_wait_CF (ae, h) (| _, cfk |) (| asId, _ |) _ _) = !st in
  CoreCrypto.hmac h cfk ((HandshakeLog.getHash hsl h) @| (asId_rc asId))

(******************************************************************)

// Handshake must call this when ServerFinished goes into log
let ks_client_13_sf ks
  : ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
  =
  let KS #region st hsl = ks in
  let C (C_13_wait_SF alpha cfk _ (| asId, ams |)) = !st in
  let (ae, h) = alpha in
  let (| FinishedID _ _ _ loginfo _, _ |) = cfk in // TODO loginfo

  let expandId = ApplicationSecretID asId in
  let hashed_log = HandshakeLog.getHash hsl h in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  // Derived applcation master secret
  let sh_rctx = hashed_log @| (asId_rc asId) in
  let ams_derived = HKDF.hkdf_expand_label h ams "application traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h ams_derived "application data key expansion" ae in

  // Post-handshake finished key
  let cfkId = FinishedID expandId LateFinished Client loginfo hashed_log in
  let (late_cfk, _) = finished_13 h ams_derived in
  let late_cfk: fink cfkId = late_cfk in

  // Rekeying secret
  let ri = RekeyID asId loginfo hashed_log 1 in
  let rk1 : rekey_secret ri = HKDF.hkdf_expand_label h ams_derived "application traffic secret" empty_bytes hL in

  let id = ID13 (KeyID expandId ApplicationDataKey Client loginfo hashed_log) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let rw = StAE.coerce HyperHeap.root id (skv @| siv) in
  let r = StAE.genReader HyperHeap.root rw in

  st := C (C_13_wait_CF alpha cfk (| asId, ams |) (| ri, rk1 |) (| cfkId, late_cfk |));
  StAEInstance r w

let ks_server_13_sf ks
  : ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
  =
  let KS #region st hsl = ks in
  let S (S_13_wait_SF alpha cfk _ (| asId, ams |)) = !st in
  let (| FinishedID _ _ _ loginfo _, _ |) = cfk in // TODO loginfo
  let (ae, h) = alpha in

  let expandId = ApplicationSecretID asId in
  let hashed_log = HandshakeLog.getHash hsl h in
  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in

  // Derived applcation master secret
  let sh_rctx = hashed_log @| (asId_rc asId) in
  let ams_derived = HKDF.hkdf_expand_label h ams "application traffic secret" sh_rctx hL in
  let (ck,civ,sk,siv) = keygen_13 h ams_derived "application data key expansion" ae in

  // Post-handshake finished key
  let cfkId = FinishedID expandId LateFinished Client loginfo hashed_log in
  let (late_cfk, _) = finished_13 h ams_derived in
  let late_cfk: fink cfkId = late_cfk in

  // Rekeying secret
  let ri = RekeyID asId loginfo hashed_log 1 in
  let rk1 : rekey_secret ri = HKDF.hkdf_expand_label h ams_derived "application traffic secret" empty_bytes hL in

  let id = ID13 (KeyID expandId ApplicationDataKey Server loginfo hashed_log) in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StAE.coerce HyperHeap.root id (skv @| siv) in
  let ckv: StreamAE.key (peerId id) = ck in
  let civ: StreamAE.iv (peerId id)  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in

  st := S (S_13_wait_CF alpha cfk (| asId, ams |) (| ri, rk1 |) (| cfkId, late_cfk |));
  StAEInstance r w

// Handshake must call this when ClientFinished goes into log
let ks_client_13_cf ks
  : ST ( i:exportId & ems i )
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_CF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
  =
  let KS #region st hsl = ks in
  let C (C_13_wait_CF alpha cfk (| asId, ams |) rekey_info latefin_info) = !st in
  let (ae, h) = alpha in
  let (| FinishedID _ _ _ loginfo _, _ |) = cfk in // TODO loginfo
  let hashed_log = HandshakeLog.getHash hsl h in
  let hL = CoreCrypto.hashSize h in
  let sh_rctx = hashed_log @| (asId_rc asId) in

  // Resumption Master Secret
  let rmsId = RMSID asId loginfo hashed_log in
  let rms : rms rmsId = HKDF.hkdf_expand_label h ams "resumption master secret" sh_rctx hL in

  // Exporter Master Secret (returned to Handshake)
  let exportId = ExportID asId loginfo hashed_log in
  let ems : ems exportId = HKDF.hkdf_expand_label h ams "resumption master secret" sh_rctx hL in
  st := C (C_13_postHS alpha latefin_info rekey_info (| rmsId, rms |) (| exportId, ems |));
  (| exportId, ems |)

(******************************************************************)

// Called by Hanshake when DH key echange is negotiated
val ks_client_12_full_dh: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> peer_share:CommonDH.key -> ST CommonDH.key
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\
    (C_12_Full_CH? (C?.s st) \/ C_12_Resume_CH? (C?.s st) \/ C_13_wait_SH? (C?.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_full_dh ks sr pv cs ems peer_share =
  let KS #region st _ = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr
    | C (C_13_wait_SH cr _ _ _ ) -> cr in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let our_share, pmsb = CommonDH.dh_responder peer_share in
  let () =
    if ks_debug then
      let _ = print_share our_share in
      let _ = print_share peer_share in
      let _ = IO.debug_print_string ("PMS: "^(Platform.Bytes.print_bytes pmsb)^"\n") in
      ()
    else () in
  let dhp = CommonDH.key_params peer_share in
  let dhpmsId = PMS.DHPMS(dhp, (CommonDH.share_of_key our_share), (CommonDH.share_of_key peer_share), PMS.ConcreteDHPMS(pmsb)) in
  let ns = 
    if ems then
      C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let _ =
        if ks_debug then
           IO.debug_print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n")
        else false in
      let msId = StandardMS dhpmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; our_share

// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\
    (C_12_Full_CH? (C?.s st) \/ C_12_Resume_CH? (C?.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_full_rsa ks sr pv cs ems pk =
  let KS #region st _ = ks in
  let alpha = (pv, cs, ems) in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr in
  let csr = cr @| sr in
  let rsapms = PMS.genRSA pk pv in
  let pmsb = PMS.leakRSA pk pv rsapms in
  let encrypted = CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 pmsb in
  let rsapmsId = PMS.RSAPMS(pk, pv, rsapms) in
  let ns =
    if ems then
      C_12_wait_MS csr alpha rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS rsapmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; encrypted

val ks_client_12_set_session_hash: ks:ks -> ST unit
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C_12_wait_MS? (C?.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_set_session_hash ks =
  let KS #region st hsl = ks in
  let C (C_12_wait_MS csr alpha pmsId pms) = !st in
  let (pv, cs, true) = alpha in
  let kef = kefAlg pv cs true in
  let h = verifyDataHashAlg_of_ciphersuite cs in
  let log = HandshakeLog.getHash hsl h in
  let ms = TLSPRF.prf (pv,cs) pms (utf8 "extended master secret") log 48 in
  let _ =
    if ks_debug then
      IO.debug_print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n")
    else false in
  let msId = ExtendedMS pmsId log kef in
  st := C (C_12_has_MS csr alpha msId ms)

// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************


// Will become private; public API will have
// ks_client_12_keygen: ks -> (i:id * w:StatefulLHAE.writer i)
// ks_server_12_keygen: ...
val ks_12_get_keys: ks:ks -> ST (writer:recordInstance)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    match st with
    | C (C_12_has_MS _ _ _ _) | S (S_12_has_MS _ _ _ _) -> true
    | _ -> false)
  (ensures fun h0 r h1 ->
    modifies Set.empty h0 h1)

(*private*) let ks_12_get_keys ks =
  let KS #region st _ = ks in
  let role, csr, alpha, msId, ms =
    match !st with
    | C (C_12_has_MS csr alpha msId ms) -> Client, csr, alpha, msId, ms
    | S (S_12_has_MS csr alpha msId ms) -> Server, csr, alpha, msId, ms in
  let cr, sr = split csr 32 in
  let (pv, cs, ems) = alpha in
  let kdf = kdfAlg pv cs in
  let ae = get_aeAlg cs in
  let id = ID12 pv msId kdf ae cr sr role in
  let AEAD alg _ = ae in (* 16-10-18 FIXME! only correct for AEAD *)
  let klen = CoreCrypto.aeadKeySize alg in
  let slen = AEADProvider.salt_length id in 
  let expand = TLSPRF.kdf kdf ms (sr @| cr) (klen + klen + slen + slen) in
  let k1, expand = split expand klen in
  let k2, expand = split expand klen in
  let iv1, iv2 = split expand slen in
  let wk, wiv, rk, riv =
    match role with
    | Client -> k1, iv1, k2, iv2
    | Server -> k2, iv2, k1, iv1 in
  let w = StAE.coerce HyperHeap.root id (wk @| wiv) in
  let rw = StAE.coerce HyperHeap.root id (rk @| riv) in
  let r = StAE.genReader HyperHeap.root rw in
  StAEInstance r w

(******************************************************************)
(******************************************************************)

let ks_client_12_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C_12_has_MS? (C?.s st))
  (ensures fun h0 r h1 -> h1 == h0)
  =
  let KS #region st hsl = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  TLSPRF.verifyData (pv,cs) ms Client log

let ks_server_12_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    S? st /\ S_12_has_MS? (S?.s st))
  (ensures fun h0 r h1 -> h1 == h0)
  =
  let KS #region st hsl = ks in
  let S (S_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  TLSPRF.verifyData (pv,cs) ms Client log

let ks_server_12_server_finished ks
  : ST (svd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    S? st /\ S_12_has_MS? (S?.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
  =
  let KS #region st hsl = ks in
  let S (S_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  st := S S_Done;
  TLSPRF.verifyData (pv,cs) ms Server log

let ks_client_12_server_finished ks
  : ST (svd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C_12_has_MS? (C?.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
  =
  let KS #region st hsl = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Server log

val getId: recordInstance -> GTot id
let getId (StAEInstance #i rd wr) = i

val recordInstanceToEpoch: #r:rgn -> #n:TLSInfo.random -> 
    			   h:handshake ->
			   ks:recordInstance -> Tot (epoch r n)
let recordInstanceToEpoch #hs_rgn #n hs (StAEInstance #i rd wr) =
  Epoch hs rd wr


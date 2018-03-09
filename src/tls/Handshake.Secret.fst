module Handshake.Secret

/// This module implements all operations on abstract TLS secrets 
/// for the handshake, grouped by message-processing stages.
/// (It used to be named KeySchedule.)

open FStar.Bytes
open FStar.Error

open Mem
open TLSError
open TLSConstants
open TLSInfo
open Idx
open HKDF // avoid?
open PSK  // avoid?

module MM = FStar.Monotonic.Map
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module H = Hashing.Spec

(* A flag for runtime debugging of computed keys.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false *)
let discard (b:bool): ST unit (requires (fun _ -> True))
 (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print s = discard (IO.debug_print_string ("KS | "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  if DebugFlags.debug_KS then print else (fun _ -> ())


// parsed handshake message transcript; essentially opaque/ghost to
// the key-schedule: what we get out of HandshakeLog.

type transcript = HandshakeLog.hs_transcript // ghost 
let digest (i:id) (t:transcript) = 
  let ha = Idx.ha_of_id i in 
  let v = HandshakeLog.transcript_bytes t in 
  t: Hashing.Spec.anyTag {Hashing.CRF.hashed ha v /\ t = Hashing.hash ha v}


/// THE LIVE OF KEY INDEXES. we use relative paths to index various
/// secrets and keys as we progress in the schedule; we try to keep
/// the index syntax abstract outside this module.
///
/// TODO would a bespoke IK.id for TLS help?

let binder_label i = if Preshared? i then "ext binder" else "res binder" 
let salt_of_ms i = Derive i "derived"     Expand // extraction salt

let ems_of_psk i     = Derive i "" Extract 
let hms_of_ems i idh = Derive (salt_of_ms i) "" (ExtractDH idh)
let ams_of_hms i     = Derive (salt_of_ms i) "" Extract 

assume val tmp: Hashing.Spec.anyTag 
// the branch on the static label will require two UFCMA packages for binders 
let bns_of_ems i = Derive i (binder_label i) Expand
let x0s_of_ems i transcript = Derive i "e exp master" (ExpandLog transcript tmp) 

let x1s_of_ams i transcript = Derive i "exp master"   (ExpandLog transcript tmp) 
let rms_of_ams i transcript = Derive i "res master"   (ExpandLog transcript tmp) 

let psk_of_rms i nonce = Derive i "resumption" (ExpandLog nonce tmp) // ticket-based

// transport secrets have a designated sender role, controlling the
// reader/writer flag of derived StreamAE instances.
let rec sender_of_id i = 
  match i with 
  | Derive i "c e traffic"  (ExpandLog _ _) 
  | Derive i "c hs traffic" (ExpandLog _ _) 
  | Derive i "c ap traffic" (ExpandLog _ _) -> Some Client
  | Derive i "s hs traffic" (ExpandLog _ _) 
  | Derive i "s ap traffic" (ExpandLog _ _) -> Some Server
  | Derive i "traffic upd" Expand -> sender_of_id i
  | _ -> None 
let ts_id = i:pre_id {Some? (sender_of_id i)}

let ets_of_ems i transcript: i:ts_id {sender_of_id i = Some Client} = Derive i "c e traffic"  (ExpandLog transcript tmp)
let cts_of_hms i transcript: i:ts_id {sender_of_id i = Some Client} = Derive i "c hs traffic" (ExpandLog transcript tmp)
let sts_of_hms i transcript: i:ts_id {sender_of_id i = Some Server} = Derive i "s hs traffic" (ExpandLog transcript tmp)
let cts_of_ams i transcript: i:ts_id {sender_of_id i = Some Client} = Derive i "c ap traffic" (ExpandLog transcript tmp)
let sts_of_ams i transcript: i:ts_id {sender_of_id i = Some Server} = Derive i "s ap traffic" (ExpandLog transcript tmp)

//TODO define [aeadAlg_of_i] specifically on transport secrets. 
//TODO make the most of welldefined_id

let iv_of_ts  (i: ts_id)        = Derive i "iv"          Expand // AEAD static IV
let key_of_ts (i: ts_id)        = Derive i "key"         Expand // AEAD keying
let ts_of_ts  (i: ts_id): ts_id = Derive i "traffic upd" Expand // post-handshake rekeying 

// we have three derived MACs for Binders for Finished messages. 
let fnk_of_s i = Derive i "finished"    Expand // binder/finished MAC keying (not always a ts)
let bfk_of_ems i = fnk_of_s (bns_of_ems i)
let cfk_of_hms i transcript = fnk_of_s (cts_of_hms i transcript)
let sfk_of_hms i transcript = fnk_of_s (sts_of_hms i transcript)


let sprint_share (#g:CommonDH.group) (s:CommonDH.pre_share g): string
  =
  let kb = CommonDH.serialize_raw #g s in
  let kh = FStar.Bytes.hex_of_bytes kb in
  "Share: "^kh


//17-12-07 out of date?
(********************************************
*    Resumption PSK is disabled for now     *
*********************************************

abstract type res_psk (i:rmsId) =
  b:bytes{exists i.{:pattern index b i} index b i <> 0z}

abstract type res_context (i:rmsId) =
  b:bytes{length b = CoreCrypto.H.tagLen (rmsId_hash i)}

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
  b2t (Some? (MM.sel (HS.sel h res_psk_table) i))

let res_psk_context (i:rmsId{registered_res_psk i}) =
  let (_, _, c, _) = Some.v (MM.sel res_psk_table i) in c

private let res_psk_value (i:rmsId{registered_res_psk i}) =
  let (psk, _, _, _) = Some.v (MM.sel res_psk_table i) in psk

**)


// PSK (internal/external multiplex, abstract)
// Note that application PSK is externally defined but should
// be idealized together with KS

//TODO indexing with depth and usage?
let u_of_i = Extract1.ODH.u_of_i
abstract type secret (i:id) = (
  let (|d, u|) = u_of_i i in 
  assume(registered i);
  KDF.secret d u i )


/// for readability so far; we could be more specific
type ems_id = id
type hms_id = id
type ams_id = id 

/// To be refined with whatever it takes to use it as an application
/// master secret, etc.
type ems (i:ems_id) = secret i
type hms (i:hms_id) = secret i
type ams (i:ams_id) = secret i

(*
type hsId       = i: id {labelled i ""}
type asId       = i: id {labelled i ""}
type finishedId = i: id {labelled i "finished"} 
type binderId   = i: id {labelled i "ext binder" \/ labelled i "res binder" }
type rmsId      = i: id {True}
type exportId = id
*)


type psk (i:id) //TODO from PSK and IK

// We treat the absence of PSK using reserved, corrupt PSK identifiers
// with all-zero coerced keys.

assume val no_psk_id: Idx.kdfa -> i:id {match i with Preshared ha _ -> True | _ -> False}
assume val no_psk (i:id): bool

let dummy_psk ha: psk (no_psk_id ha) = 
  magic() // PSK.coerce (no_psk_id ha) ha (H.zeroHash ha) 
  // we'll need them to be registered as corrupt and pre-defined to
  // meet coerce's precondition.


/// Move to PSK? DB lookup from concrete pskid to indexed abstract psk & info.


let read_psk (pi:PSK.pskid): ST (i:id & u:PSK.pskInfo {ha_of_id i = u.early_hash} * psk i)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
=
  magic()
  (*
  let c = PSK.psk_info pi in
  let i =
    if Some? c.ticket_nonce then
      let (| li, rmsid |) = Ticket.dummy_rmsid c.early_ae c.early_hash in
      ResumptionPSK #li rmsid
    else
      ApplicationPSK #c.early_hash #c.early_ae pi
    in
  (id, c, PSK.psk_value pi)
  *)

(* 17-12-04 now handled within IK/Extract? 
// Resumption context
let rec esId_rc : (esId -> St bytes) =
  function
  | NoPSK h -> H.zeroHash h

and hsId_rc : (hsId -> St bytes) = function
  | HSID_DHE (Salt i) _ _ _ -> secretId_rc i
  | HSID_PSK (Salt i) -> secretId_rc i

and asId_rc : (asId -> St bytes) = function
  | ASID (Salt i) -> secretId_rc i

and secretId_rc : (secretId -> St bytes) = function
  | EarlySecretID i -> esId_rc i
  | HandshakeSecretID i -> hsId_rc i
  | ApplicationSecretID i -> asId_rc i
*)


// pre-master-secrets and secret for earlier versions of TLS
// (not idealized in this branch)
// ==========
// PRF (type pms) -> TLSInfo (type id) -> KEF (extract pms)
//                     \ StatefulLHAE (coerce id) /
// TODO rework old 1.2 types
type ms = bytes
type pms = bytes
//17-12-07 can they also be products of IK? no immediate need

#set-options "--z3rlimit 30"
// only for TLS 1.3, will need refining 
let fink i = HMAC.UFCMA.key Idx.ii i
let binderKey i = HMAC.UFCMA.key Idx.ii i
//was:
//type fink (i:finishedId)    = HMAC.UFCMA.key (HMAC.UFCMA.HMAC_Finished i) (fun _ -> True)
//type binderKey (i:binderId) = HMAC.UFCMA.key (HMAC.UFCMA.HMAC_Binder i) (fun _ -> True)


// type exportKey = (i:id & ems i * logInfo)

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


type ks_alpha12 = 
  pv:protocolVersion * 
  cs:cipherSuite * 
  ems:bool // extended-master-secret flag

// For TLS 1.3, HS keeps the concrete ha and (optionally) aea, subject
// to in Nego, and reminds them to KS as we progress in the
// schedule. Both are also always bound as a function of the ghost
// index.

/// key-schedule states for TLS 1.2, now kept in the Handshake state;
/// to be similarly refactored. (The initial states holding just the
/// nonce are gone.)
noeq type ks12_state = 
| C12_Resume_CH: 
    cr:random -> 
    si:sessionInfo -> 
    msId:TLSInfo.msId -> 
    ms:ms -> ks12_state
// optional intermediate state within HS.client_ServerHelloDone 
| C12_wait_MS: 
    csr:csRands -> 
    alpha:ks_alpha12 -> 
    id:TLSInfo.pmsId -> 
    pms:pms -> ks12_state
// state after HS.client_ServerHelloDone
| C12_has_MS: 
    csr:csRands -> 
    alpha:ks_alpha12 -> 
    id:TLSInfo.msId -> 
    ms:ms -> ks12_state
//
// type ks_server_state =
| S12_wait_CKE_DH: 
    csr:csRands -> 
    alpha:ks_alpha12 -> 
    our_share:(g:CommonDH.group & CommonDH.pre_keyshare g) -> ks12_state
| S12_wait_CKE_RSA: 
    csr: csRands -> 
    alpha:ks_alpha12 -> ks12_state
| S12_has_MS: 
    csr:csRands -> 
    alpha:ks_alpha12 -> 
    id:TLSInfo.msId -> 
    ms:ms -> ks12_state

// state after sending ClientHello (for all protocol  versions)
abstract type c13_wait_ServerHello 
  (psks  : list (i:id{~(no_psk i)})) 
  (groups: list CommonDH.group) = 
| C13_wait_ServerHello:
  // symmetric extracts for the PSKs the client is proposing
  // (the indexes are a function of those of the PKSs)
  esl: list (i:id{~(no_psk i)} & ems i) ->
  // private exponents for the honestly-generated shares the client is
  // proposing (overwritten on hello_retry)
  gxs: list CommonDH.dhi -> c13_wait_ServerHello psks groups

// now just ams i:
// abstract type c13_wait_ServerFinished (i: amsId) = 
// abstract type c13_wait_ClientFinished (i: amsId) = 

/// rekeying part of the final state, holding the *next* transport
/// secret, separately for the client and the server.
abstract type next_ts (i: ts_id) = secret (ts_of_ts i) 

//18-01-07 TODO AEAD packaging
assume val aeadAlg_of_i: id -> aeAlg //18-01-07  should match AEAD.Pkg.aeadAlg?

// intermediate state waiting for the the ...ServerHello digest
abstract type s13_wait_ServerHello (i0: id (*esId*)) (z:id_dhe) =
| S13_wait_SH: 
    ha: kdfa {ha = ha_of_id i0} -> 
    aea: option (a:aeAlg {a == aeadAlg_of_i i0}) -> // still undefined when there is no PSK
    cr:random -> 
    sr:random -> 
    ems i0 ->
    hms (hms_of_ems i0 z) -> s13_wait_ServerHello i0 z

abstract type s13_wait_ServerFinished (i: id (*amsId*)) = secret i 


// KeySchedule instances
(*
 * AR: changing state from rref to ref, with region captured in the refinement.
 *)
//type ks =
//| KS: #region:rid -> state:(ref ks_state){HS.MkRef?.id state = region} -> ks
//17-04-17 CF: expose it as a concrete ref?
//17-04-17 CF: no need to keep the region, already in the ref.

/// Extract keys and IVs from a derived TLS 1.3 traffic secret
/// TODO
/// 2-stage AEAD creation
/// return abstract AEAD writer instance
/// reader instance as a follow up call?
/// key-install invariant
/// regions?
/// reader vs writer? 

(* 18-01-07 TODO AEAD 

val derive_ae13:
  #u: Idx.usage -> // should be specific
  #i: Idx.id {Idx.registered i} -> // should be refined
  s: Idx.secret u i -> 
  info: Idx.info {info = Idx.get_info i} ->
  parent: rgn -> 
  ST (StreamAE.key (ae_traffic i))
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> True)

let derive_ae13 #u #i s info parent = 
  let k: AEAD.key (Derive i "key" Expand) = derive ha secret "key" Expand (parent, info.aea) in 
  let iv: StreamAE.iv (Derive i "iv" Expand) = derive ha secret "iv" Expand (info.pv, info.aea) in
  let w: StreamAE.writer i = StreamAE.wrapWriter k iv in 
  w
(* WAS:
private let keygen_13 h secret ae : St (bytes * bytes) =
  let kS = CoreCrypto.aeadKeySize ae in
  let iS = CoreCrypto.aeadRealIVSize ae in
  let kb = HKDF.hkdf_expand_label h secret "key" empty_bytes kS in
  let ib = HKDF.hkdf_expand_label h secret "iv" empty_bytes iS in
  (kb, ib)
*)
*)


// // Extract finished keys
// private let derive_finished13 h secret: St bytes =
//   HKDF.hkdf_expand_label h secret "finished" empty_bytes (H.tagLen h)

(* GONE: 
// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> role -> ST (ks * random)
  (requires fun h -> rid<>root)
  (ensures fun h0 (r,_) h1 ->
    let KS #ks_region state = r in
    HS.fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref state))) ( h0) ( h1))

let create #rid r =
  ST.recall_region rid;
  let ks_region = new_region rid in
  let nonce = Nonce.mkHelloRandom r ks_region in
  let istate = match r with
    | Client -> C (C_Init nonce)
    | Server -> S (S_Init nonce) in
  (KS #ks_region (ralloc ks_region istate)), nonce
*)

private let group_of_valid_namedGroup
  (g:CommonDH.supportedNamedGroup)
  : CommonDH.group
  = Some?.v (CommonDH.group_of_namedGroup g)

effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)

val map_ST: ('a -> ST0 'b) -> list 'a -> ST0 (list 'b)
let rec map_ST f x = match x with
  | [] -> []
  | a::tl -> f a :: map_ST f tl

private let group_of_cks = function
  | CommonDH.Share g _ -> Some?.v (CommonDH.namedGroup_of_group g)
  | CommonDH.UnknownShare g _ -> g

// 17-12-02 should call IK.initI, at least for TLS 1.3
private let keygen (g:CommonDH.group)
  : St (g:CommonDH.group & CommonDH.pre_keyshare g)
  = (| g, CommonDH.keygen g |)

assume val ks_client_init: ogl: option (CommonDH.supportedNamedGroups)
  -> ST (option CommonDH.clientKeyShare)
  (requires fun h0 -> True)
  (ensures fun h0 ogxl h1 ->
    (None? ogl ==> None? ogxl) /\
    (Some? ogl ==> (Some? ogxl /\ Some?.v ogl == List.Tot.map group_of_cks (Some?.v ogxl))) /\
    modifies_none h0 h1)

(* 17-12-02 FIXME
let ks_client_init ogl =
  dbg ("ks_client_init "^(if ogl=None then "1.2" else "1.3"));
  match ogl with
  | None -> None // TLS 1.2
  | Some gl ->   // TLS 1.3
    let groups = List.Tot.map group_of_valid_namedGroup gl in
    let gs = map_ST keygen groups in
    let serialize_share (gx: CommonDH.dhi) =
      let (| g, gx |) = gx in
      match CommonDH.namedGroup_of_group g with
      | None -> None // Impossible
      | Some ng -> Some (CommonDH.Share g (CommonDH.pubshare #g gx)) in
    let gxl = List.Tot.choose serialize_share gs in
    // st := C (C_13_wait_SH cr [] gs);
    Some gxl
*)


(* 17-11-25 functionally replacing the two functions below *)

// the digest comes with its logical payload, ready to be MACed.
// we will need a full spec of the early index. 
// we can re-use this code at the server, except that we verify instead of MACing


val client13_compute_es_and_bfk:
  #rid: rgn -> 
  (pskid:PSK.pskid * PSK.obfuscated_ticket_age) -> 
  ST (i: id (*esId{~(dummy i)}*) & ems i * binderKey (bns_of_ems i) * Idx.info (*TBC*) )
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

// cwinter: broken, but unused?
// let client13_compute_es_and_bfk truncatedHello #rid (pskid,_) =
//   // 17-11-25 rediscuss this callback
//   let i, pski, psk = read_psk pskid in
//   let ha = pski.early_hash in
//   dbg ("Loaded pre-shared key "^print_bytes pskid^": "^print_bytes psk);

//   let es: es i = magic() in // extract0 psk ha in
//   dbg ("Early secret: "^print_bytes es);

//   // // strange twist on usage; does it help re: salt collisions?
//   //
//   // let binder_key = 
//   //   if ApplicationPSK? i 
//   //   then derive_secret "ext binder" es ha 
//   //   else derive_secret "res binder" es ha
//   let lb = 
//     if ApplicationPSK? i //17-11-26 we need to know at run-time
//     then "ext binder" 
//     else "res binder" in

//   let bk: binderKey (binder_of_esid_id i) = magic() in 
//   let es_info = magic() in
//   (*
//   let bId = Binder i ll in
//   let bk: secret bId = magic() in // KDF.derive_secret ha es lb (H.emptyHash ha) in
//   dbg ("binder key["^lb^"]: "^print_bytes bk);

//   let bkfId = binderKey bId in 
//   let bfk: HMAC.UFCMA.key bkfId = KDF.derive bk ha "finished" in
//   dbg ("binder Finished key: "^print_bytes bfk);
//   *)
//   (| i, (es, bk, es_info) |)

(* WAS:
private let mk_binder (#rid) (pskid:PSK.pskid)
  : ST ((i:binderId & bk:binderKey i) * (i:esId{~(dummy i)} & es i))
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let i, pski, psk = read_psk pskid in
  let h = pski.early_hash in
  dbg ("Loaded pre-shared key "^(print_bytes pskid)^": "^(print_bytes psk));
  let es : es i = HKDF.extract #h (H.zeroHash h) psk in
  dbg ("Early secret: "^(print_bytes es));
  let ll, lb =
    if ApplicationPSK? i then ExtBinder, "ext binder"
    else ResBinder, "res binder" in
  let bId = Binder i ll in
  let bk = magic() in // HKDF.derive_secret h es lb (H.emptyHash h) in
  dbg ("Binder key["^lb^"]: "^(print_bytes bk));
  let bk = derive_finished13 h bk in
  dbg ("Binder Finished key: "^(print_bytes bk));
  let bk : binderKey bId = magic() in //HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Binder bId) (fun _ -> True) rid bk in
  (| bId, bk|), (| i, es |)

let ks_client_13_get_binder_keys ks pskl =
  let KS #rid st = ks in
  let C (C_13_wait_SH cr [] gs) = !st in
  let pskl = map_ST (mk_binder #rid) pskl in
  let (bkl, esl) = List.Tot.split pskl in
  st := C (C_13_wait_SH cr esl gs);
  bkl
*)

// 17-11-25 new state-passing variant; why do we resample? impact on
// the KS proof? We suppose Nego does the filtering. 

let client13_HelloRetryRequest (g:CommonDH.group): ST0 (CommonDH.ikeyshare g) =
  // TODO: just call initI g 
  admit()
//let x: CommonDH.ikeyshare g = CommonDH.keygen g in
//let gX = CommonDH.pubshare #g s in
//[(| g, x|)], gX

(*
let ks_client_13_hello_retry ks (g:CommonDH.group)
  : ST0 (CommonDH.ikeyshare g) =
  let KS #rid st = ks in
  let C (C_13_wait_SH cr esl gs) = !st in
  let s : CommonDH.keyshare g = CommonDH.keygen g in
  st := C (C_13_wait_SH cr esl [(| g, s |)]);
  CommonDH.pubshare #g s
*)


/// When 0-RTT is offered, derive the early data key and exporter
/// secret from the early secret of the first offered PSK.

// cwinter: broken, but unused?
// let client13_0RTT 
//   (i: emsi) 
//   (es: secret i) //TODO does the secret embed its info? otherwise [ha,aea] required
//   (truncated_ClientHello: transcript) // ghost
//   (digest: Hashing.Spec.anyTag) // to be refined
//   (writer_parent: rgn) 
//   : ST (
//     secret (x0s_of_ems i truncated_ClientHello) * 
//     StreamAE.writer (ets_of_ems i truncated_ClientHello))
//   (requires fun h0 -> True 
//     // freshness of this transcript (from freshness of its nonce)
//     )
//   (ensures fun h0 r h1 ->
//     modifies_none h0 h1 
//     // except for the keys we derive
//     )
//   =
//   dbg ("client13_0RTT log="^print_bytes digest);
//   let ha = esId_hash i in
//   let aea = esId_ae i in
//   let info = (ha,aea) in

//   let x0si = x0s_of_ems i transcript in 
//   let x0s: secret x0si = derive es ha "e exp master" transcript digest info in
//   dbg ("Early exporter master secret:    "^print_bytes (leak_secret x0s));

//   let etsi = ets_of_ems i transcript in
//   let ets: secret etsi = derive es ha "c e traffic" transcript digest info in
//   dbg ("Client early traffic secret:     "^print_bytes (leak_secret ets));

//   let key0 = derive_streamAE #etsi ets Writer writer_parent in 
//   x0s, key0

(* WAS: 
let ks_client_13_ch ks (log:bytes): ST (exportKey * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies_none h0 h1)
  =
  dbg ("ks_client_13_ch log="^(print_bytes log));
  let KS #rid st = ks in
  let C (C_13_wait_SH cr ((| i, es |) :: _) gs) = !st in

  let h = esId_hash i in
  let ae = esId_ae i in

  let li = LogInfo_CH0 ({
   li_ch0_cr = cr;
   li_ch0_ed_ae = ae;
   li_ch0_ed_hash = h;
   li_ch0_ed_psk = empty_bytes; }) in

  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID i) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret:     "^print_bytes ets);
  let expId : exportId li = EarlyExportID i log in
  let early_export : ems expId = HKDF.derive_secret h es "e exp master" log in
  dbg ("Early exporter master secret:    "^print_bytes early_export);
  let exporter0 = (| li, expId, early_export |) in

  // Expand all keys from the derived early secret
  let (ck, civ) = keygen_13 h ets ae in
  dbg ("Client 0-RTT key:                "^print_bytes ck^", IV="^print_bytes civ);

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in
  let early_d = StAEInstance r rw in
  exporter0, early_d
*)

//17-12-29 we don't use cr sr pv cs ems yet; simplify? This is just odh_init 
val server12_init_dh: 
  cr: random -> 
  sr: random -> 
  pv: protocolVersion -> 
  cs: cipherSuite -> 
  ems: bool -> 
  g: CommonDH.group -> 
  ST (ks12_state * CommonDH.share g)
  (requires fun h0 ->
    match cs with 
    | CipherSuite Kex_DHE _ _ 
    | CipherSuite Kex_ECDHE _ _ -> True
    | _ -> False) 
  (ensures fun h0 r h1 -> True)

let server12_init_dh cr sr pv cs ems g =
  dbg "server12_init_dh";
  let y = CommonDH.keygen g in
  let _ = sprint_share (CommonDH.ipubshare y) in
  let csr = cr @| sr in
  S12_wait_CKE_DH csr (pv, cs, ems) (| g, y |),
  CommonDH.ipubshare y


/// Once TLS 1.3 is accepted, compute all keys up to the handshake
/// secret (except for now for the optional [server13_0rtt_key],
/// which further require the client transcript).
///
val server13_init:
  cr: random ->
  sr: random ->
  cs: cipherSuite ->
  pskid: option PSK.pskid ->
  g_gx: option (g:CommonDH.group & CommonDH.share g) ->
  transcript: _ ->
  ST (
    i: id (* TODO: carefully relate i to pskid *) &
    (option CommonDH.serverKeyShare * 
    // option (binderKey (fnk_of_ts (ets_of_ems i)))) // cwinter: no fnk_of_ts?
    (let tsid = ets_of_ems i transcript in
     option (binderKey (fnk_of_s tsid)))))
  (requires fun h0 -> 
    // stateless conditions: 
    (Some? g_gx \/ Some? pskid) /\
    (Some? g_gx ==> Some? (CommonDH.namedGroup_of_group (dfst (Some?.v g_gx)))) /\
    CipherSuite13? cs
    // will also require the global keyed invariant
    )
  (ensures fun h0 (|i, (gy, bk)|) h1 ->
    // will modify the global keyed footprint and restore its invariant;
    // any more details required? 
    modifies_none h0 h1 /\
    (Some? bk <==> Some? pskid) /\
    (Some? gy \/ Some? bk) )

let leak_secret es = es 
let leak_psk psk = psk

let server13_init cr sr cs pskid g_gx tr =
  dbg "server13_init";
  let CipherSuite13 aea ha = cs in

  // retrieve optional pre-shared key; should the index be pski instead?
  let (| i, (psk0, ha) |): ( i:id & psk i * ha: Hashing.Spec.alg {ha = ha_of_id i} ) =
    match pskid with 
    | None ->
      dbg "No PSK selected.";
      (| no_psk_id ha, (dummy_psk ha, ha) |) 
    | Some id -> 
      dbg ("Using negotiated PSK identity: "^print_bytes id);
        //17-11-26 should this branch move to PSK? 
        match Ticket.check_ticket id with
        | Some (Ticket.Ticket13 cs li rmsId rms _ _) ->
          dbg ("Ticket RMS: "^print_bytes rms);
          let i = ResumptionPSK #li rmsId in
          let CipherSuite13 _ ha = cs in //17-11-26 no consistency check? 
          let nonce, _ = split_ id 12 in  //17-11-26 what's this nonce? 
          let psk0 = HKDF.derive_secret ha rms "resumption" nonce in
          (|i, (psk, ha)|)
        | None ->
          let (| i, (pski, psk) |) = read_psk id in //17-11-26 no consistency check?
          (| i, (psk, pski.early_hash) |) in
  if Some? pskid then dbg ("Pre-shared key: "^leak_psk psk);

  // extract early master secret
  let i0 = ems_of_psk i in 
  let es: secret i0 = Extract0.extract0 psk0 ha in 
  dbg ("Computed early secret:           "^leak_secret es);
  let bfko =
    match pskid with 
    | None -> None
    | Some _ -> // optionally compute the binder-verification key
      let lbl = binder_label i in
      let bnsi = bns_of_ems i0 in
      let bns: secret bnsi = KDF.derive es ha lbl Expand info in
      let bfkId = binderKey i in
      let info0 = magic() in // missing region and logical payload
      let bfk: HMAC.UFCMA.key i = KDF.derive bns ha "finished" Expand info0 in
      dbg ("binder key:                      "^print_bytes bfkId);
      dbg ("binder Finished key:             "^print_bytes bfk);
      Some bfk in

  // TODO optionally compute the 0RTT key too? 

  // extract handshake secret, mixing-in the optional DH secret. 
  let salt1: Extract1.PRF.salt (salt_of_ms i0) = KDF.derive es ha "derived" Expand () in
  let idh, hs =
    match g_gx with
    | None -> 
        let hs = Extract1.extractP ha salt1 in
        NoIDH, hs
    | Some (| g, gX |) ->
        let gY, hs = Extract1.extractR ha g gX in 
        IDH gX gY, hs in
  dbg ("Handshake salt:                  "^print_bytes salt1);
  dbg ("Handshake secret:                "^print_bytes hs);
  (| idh, (bfko, (*local state:*) hs)|)

(* WAS:
let ks_server_13_init ks cr cs pskid g_gx =
  dbg ("ks_server_init");
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let CipherSuite13 ae h = cs in
  let esId, es, bk =
    match pskid with
    | Some id ->
      dbg ("Using negotiated PSK identity: "^(print_bytes id));
      let i, psk, h : esId * bytes * Hashing.Spec.alg =
        match Ticket.check_ticket id with
        | Some (Ticket.Ticket13 cs li rmsId rms) ->
          dbg ("Ticket RMS: "^(print_bytes rms));
          let i = ResumptionPSK #li rmsId in
          let CipherSuite13 _ h = cs in
          let nonce, _ = split id 12 in
          let psk = HKDF.derive_secret h rms "resumption" nonce in
          (i, psk, h)
        | None ->
          let i, pski, psk = read_psk id in
          (i, psk, pski.early_hash)
        in
      dbg ("Pre-shared key: "^(print_bytes psk));
      let es = HKDF.hkdf_extract h (H.zeroHash h) psk in
      let ll, lb =
        if ApplicationPSK? i then ExtBinder, "ext binder"
        else ResBinder, "res binder" in
      let bId = Binder i ll in
      let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
      let bk = finished_13 h bk in
      dbg ("binder key:                      "^print_bytes bk);
      dbg ("binder Finished key:             "^print_bytes bk);
      let bk : binderKey bId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Binder bId) (fun _ -> True) region bk in
      i, es, Some (| bId, bk |)
    | None ->
      dbg "No PSK selected.";
      let esId = NoPSK h in
      let es : es esId = HKDF.hkdf_extract h (H.zeroHash h) (H.zeroHash h) in
      esId, es, None
    in
  dbg ("Computed early secret:           "^print_bytes es);
  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("Handshake salt:                  "^print_bytes salt);
  let gy, hsId, hs =
    match g_gx with
    | Some (| g, gx |) ->
      let gy, gxy = CommonDH.dh_responder gx in
      dbg ("DH shared secret: "^(print_bytes gxy));
      let hsId = HSID_DHE saltId g gx gy in
      let hs : hs hsId = HKDF.hkdf_extract h salt gxy in
      Some (CommonDH.Share g gy), hsId, hs
    | None ->
      let hsId = HSID_PSK saltId in
      let hs : hs hsId = HKDF.hkdf_extract h salt (H.zeroHash h) in
      None, hsId, hs
    in
  dbg ("Handshake secret:                "^print_bytes hs);
  st := S (S_13_wait_SH (ae, h) cr sr (| esId, es |) (| hsId, hs |));
  gy, bk
*)

(* 2018.03.08 Sbroken, but unused?
let server13_0RTT 
  (i: esId) 
  (idh:_) 
  (ks: s13_wait_ServerHello i idh) 
  (truncated_ClientHello: transcript)
  (digest: Hashing.Spec.anyTag) 
  (reader_parent: rgn):
  ST (
    secret (x0s_of_ems i truncated_ClientHello) *
    StreamAE.reader (ets_of_ems i truncated_ClientHello))
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
=
  dbg "server13_0rtt_key";
  let S13_wait_SH ha aea _ _ es _ = ks in
  let info = (ha, aea) in

  let x0si = x0s_of_ems i truncated_ClientHello in
  let x0s = secret x0si = derive es ha "e exp master" truncated_ClientHello digest info in
  dbg ("Early exporter master secret:    "^leak_secret x0s);

  let ets = derive es ha "c e traffic" truncated_ClientHello digest info in
  dbg ("Client early traffic secret:     "^leak_secret ets);

  let key0 = derive_streamAE #etsi ets Reader reader_parent in
  (x0s, key0)
*)

/// Continues from the handshake secret, now that we have the handshake
/// digest up to ServerHello. We stop at the application master secret
/// and return the handshake AE keys to install and the Finished keys.

val server13_ServerHello: 
  i: esId ->
  idh:_ ->
  ks: s13_wait_ServerHello i idh ->
  tr: transcript ->
  digest: Hashing.Spec.anyTag ->
  ST (
    i: hsId {i = hms_of_ems i idh} &
    s13_wait_ServerFinished (ams_of_hms i) *
    StreamAE.reader (cts_of_hms i) *
    StreamAE.writer (sts_of_hms i)  
    )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> modifies_none h0 h1)

let server13_ServerHello ks log =
  dbg ("server13_ServerHello, hashed log = "^print_bytes digest);

  let S13_wait_SH ha aea _ _ es hs = ks in
  // Derived handshake traffic secrets and keys 
  let cts = derive ha hs "c hs traffic" log info in
  let sts = derive ha hs "s hs traffic" log info in 

  // Handshake traffic keys
  let w = derive_streamAE sts info Writer writer_parent in 
  let r = derive_streamAE cts info Reader reader_parent in 

  // Finished keys (hiding too much their regions and logical payloads)
  let cfk1 = finished_13 h cts in
  let sfk1 = finished_13 h sts in

  dbg ("handshake traffic secret[C]:     "^sprint_secret cts);
  dbg ("handshake traffic secret[S]:     "^sprint_secret sts);
  dbg ("finished key[C]:                 "^sprint_secret cfk1);
  dbg ("finished key[S]:                 "^sprint_secret sfk1);
  //dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  //dbg ("handshake key[S]:                "^print_bytes sk^", IV="^print_bytes siv);

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = derive_secret hs ha "derived" Expand in
  //dbg ("Application salt:                "^print_bytes salt);
  let amsi = ams_of_hms hmsi in
  let ams: secret amsi = extract2 salt ha in
  dbg ("Application secret:              "^sprint_secret ams);

  let next = S13_wait_ServerFinished #amsi ha aea ams in
  (| hmsi, (next, r, w) |)


// Will become private; public API will have
// client12_keygen: ks -> (i:id * w:StatefulLHAE.writer i)
// server12_keygen: ...
val ks12_finished_key: st: ks_state -> ST TLSPRF.key
  (requires fun h0 -> C12_has_MS? s \/ S12_has_MS? s)
  (ensures fun h0 r h1 -> modifies Set.empty h0 h1)

let ks12_finished_key st =
  let ms = match st with
  | C12_has_MS _ _ _ ms -> ms
  | S12_has_MS _ _ _ ms -> ms in
  TLSPRF.coerce ms

let ks12_ms st = 
  match st with 
  | C12_has_MS _ _ msId ms -> (msId, ms)
  | S12_has_MS _ _ msId ms -> (msId, ms)

private val ks12_record_key: st: ks12_state -> St recordInstance
let ks12_record_key st =
  dbg "ks12_record_key";
  let role, csr, alpha, msId, ms =
    match st with
    | C12_has_MS csr alpha msId ms -> Client, csr, alpha, msId, ms
    | S12_has_MS csr alpha msId ms -> Server, csr, alpha, msId, ms in
  let cr, sr = split csr 32 in
  let pv, cs, ems = alpha in
  let kdf = kdfAlg pv cs in
  let ae = get_aeAlg cs in
  let id = ID12 pv msId kdf ae cr sr role in
  let AEAD alg _ = ae in (* 16-10-18 FIXME! only correct for AEAD *)
  let klen = CoreCrypto.aeadKeySize alg in
  let slen = AEADProvider.salt_length id in
  let expand = TLSPRF.kdf kdf ms (sr @| cr) (klen + klen + slen + slen) in
  dbg ("keystring (CK, SK, CIV, SIV) = "^print_bytes expand);
  let k1, expand = split expand klen in
  let k2, expand = split expand klen in
  let iv1, iv2 = split expand slen in
  let wk, wiv, rk, riv =
    match role with
    | Client -> k1, iv1, k2, iv2
    | Server -> k2, iv2, k1, iv1 in
  let w = StAE.coerce HS.root id (wk @| wiv) in
  let rw = StAE.coerce HS.root id (rk @| riv) in
  let r = StAE.genReader HS.root rw in
  StAEInstance r w

(* 1.2 resumption *)

// We can potentially 1.2 resume from 1.2 or 1.3 ClientHello
// (used to be [C12_Full_CH? \/ C_13_wait_SH?] now joined in Handshake)
val client12_resume: 
  cr: random -> 
  sr: random -> 
  pv: protocolVersion -> 
  cs: cipherSuite ->
  ems: bool ->
  msId:TLSInfo.msId ->
  ms:bytes -> 
  ST (ks12_state * recordInstance)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let client12_resume cr sr pv cs ems msId ms =
  dbg "client12_resume";
  dbg ("Recall MS: "^print_bytes ms);
  let ks = C12_has_MS (cr @| sr) (pv, cs, ems) msId ms in
  ks, ks12_record_key ks

val server12_resume: 
  cr: random -> 
  sr: random -> 
  pv: protocolVersion -> 
  cs: cipherSuite -> 
  ems: bool -> 
  msId: msId -> 
  ms:bytes ->
  ST (ks12_state * recordInstance)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> True)
let server12_resume cr sr pv cs ems msId ms =   
  dbg "server12_resume";
  dbg ("Recall MS: "^print_bytes ms);
  let ks = S12_has_MS (cr @| sr) (pv, cs, ems) msId ms in 
  ks, ks12_record_key ks

(******************************************************************)

// log is the raw HS log, used for EMS derivation
val server12_cke_dh: 
  ks: ks12_state {C12_wait_CKE_DH? ks} -> 
  gy: (g:CommonDH.group & CommonDH.share g) ->
  log: bytes -> 
  ST (ks12_state * recordInstance)
  (requires fun h0 ->
    // Responder share must be over the same group as initiator's
    match ks with 
    | S12_wait_CKE_DH _ _ (| g', _ |) -> g' = dfst gy 
    | _ -> False)
  (ensures fun h0 r h1 -> True)
let server12_cke_dh ks gy hashed_log =
  dbg "server12_cke_dh";
  let S12_wait_CKE_DH csr alpha (| g, gx |) = ks in
  let (pv, cs, ems) = alpha in
  let (| _, gy |) = gy in
  let _ = print_share gy in
  let pmsb = CommonDH.dh_initiator #g gx gy in
  dbg ("PMS: "^print_bytes pmsb);
  let pmsId = PMS.DHPMS g (CommonDH.pubshare gx) gy (PMS.ConcreteDHPMS pmsb) in
  let kef = kefAlg pv cs ems in
  let msId, ms =
    if ems then
      begin
      let ms = TLSPRF.prf (pv,cs) pmsb (utf8 "extended master secret") hashed_log 48 in
      dbg ("extended master secret:"^(print_bytes ms));
      let msId = ExtendedMS pmsId hashed_log kef in
      msId, ms
      end
    else
      begin
      let ms = TLSPRF.extract kef pmsb csr 48 in
      dbg ("master secret:"^print_bytes ms);
      let msId = StandardMS pmsId csr kef in
      msId, ms
      end
    in
  let ks = S12_has_MS csr alpha msId ms in
  ks, ks12_record_key ks

(**
// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val client12_resume: ks:ks -> random -> pv:protocolVersion -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C12_Resume_CH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let client12_resume ks sr pv cs =
  let KS #region st = ks in
  let C (C12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extended_ms in
  st := C (C12_has_MS csr (pv, cs, ems) msId ms)
*)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguments
//   2. they use different return types
//   3. they are called at different locations

val client13_ServerHello:
  psks: list (i:esId{~(no_psk i)}) -> groups: list CommonDH.group -> // ghosts indexing ks
  ks: c13_wait_ServerHello psks groups -> 
  sr: random -> 
  cs: cipherSuite -> 
  transcript: bytes ->
  accepted_psk: option (n:nat{n < length psks}) -> 
  accepted_group: CommonDH.group {List.mem g groups} -> 
  gy: CommonDH.share g -> 
  ST ( 
    i: hsId {i = hsId_of_es i} & // next caller index, for convenience
    (*ks':*) c13_wait_finished1 (amsId_of_hs i) *
    (*cfk:*) MAC.UFCMA.key (cfkId_of_hs i transcript) *
    (*sfk:*) MAC.UFCMA.key (sfkId_of_hs i transcript) *
    (*hsw:*) StreamAE.writer (ctsId_of_hs i) *
    (*hsr:*) StreamAE.reader (stsID_of_hs i) )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> modifies_none h0 h1)

let client13_ServerHello psks groups ks sr cs log accept_psk g gy =
  dbg ("ks_client_13_sh hashed_log = "^print_bytes log);
  let C13_wait_ServerHello esl gxs = ks in
  let Some gx = List.Tot.find (
      fun ((| g', _ |):(x:CommonDH.group & CommonDH.keyshare g)) -> g = g'
    ) gc in
  let (| g, gx |) = gx in
  let b = print_share gy in
  let gxy = CommonDH.dh_initiator #g gx gy in
  dbg ("DH shared secret: "^print_bytes gxy);
  let CipherSuite13 ae h = cs in
  let gx = CommonDH.pubshare gx in

  // Early secret: must derive zero here as hash is not known before
  let esId, es =
    match esl, accept_psk with
    | l, Some n ->
      let Some (| i, es |) : option (i:esId & es i) = List.Tot.nth l n in
      dbg ("recallPSK early secret:          "^print_bytes es);
      i, es
    | _, None ->
      let es = HKDF.hkdf_extract h (H.zeroHash h) (H.zeroHash h) in
      dbg ("no PSK negotiated. Early secret: "^print_bytes (leak_secret es));
      NoPSK h, es in

  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("handshake salt:                  "^print_bytes (leak_salt salt));

  let hsId = HSID_DHE saltId g gx gy in
  let hs : hs hsId = HKDF.hkdf_extract h salt gxy in
  dbg ("handshake secret:                "^print_bytes (leak_secret hs));

  let secretId = HandshakeSecretID hsId in
  let li = LogInfo_SH ({
    li_sh_cr = cr;
    li_sh_sr = sr;
    li_sh_ae = ae;
    li_sh_hash = h;
    li_sh_psk = None;
  }) in
  let log: hashed_log li = log in
  let c_expandId = ExpandedSecret secretId ClientHandshakeTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ServerHandshakeTrafficSecret log in

  let cts = HKDF.derive_secret h hs "c hs traffic" log in
  let sts = HKDF.derive_secret h hs "s hs traffic" log in
  let (ck,civ) = keygen_13 h cts ae in
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("handshake traffic secret[C]:     "^print_bytes cts);
  dbg ("handshake traffic secret[S]:     "^print_bytes sts);
  dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  dbg ("handshake key[S]:                "^print_bytes sk^", IV="^print_bytes siv);

  // Finished keys
  let cfkId = FinishedID c_expandId in
  let sfkId = FinishedID s_expandId in
  let cfk1 = finished_13 h cts in
  dbg ("finished key[C]: "^(print_bytes cfk1));
  let sfk1 = finished_13 h sts in
  dbg ("finished key[S]: "^(print_bytes sfk1));

  let cfk1 : fink cfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished cfkId) (fun _ -> True) region cfk1 in
  let sfk1 : fink sfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished sfkId) (fun _ -> True) region sfk1 in

  (*TODO factor out *)
  let id = ID13 (KeyID c_expandId) in
  assert_norm(ID13 (KeyID s_expandId) = peerId id);
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HS.root id (ckv @| civ) in
  let rw = StAE.coerce HS.root id (skv @| siv) in
  let r = StAE.genReader HS.root rw in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  let asId = ASID saltId in
  let ams: ams asId = HKDF.hkdf_extract h salt (H.zeroHash h) in
  dbg ("application salt:                "^print_bytes (leak_salt salt));
  dbg ("application secret:              "^print_bytes (leak_secret ams));

  let next = C13_wait_ServerFinished ae h ams in
  (next, cfk1, sfk1, hs_wr, hs_rd)

(******************************************************************)

let client13_ServerFinished
  (i: amsId) 
  (s: ams i)
  (transcript_Finished: transcript): 
  ST (
//  c13_wait_Finished2 i * 
//  MAC.UFCMA.key (cfkId_of_hs i transcript1) *
//  MAC.UFCMA.key (sfkId_of_hs i transcript1) *
    StreamAE.reader (askId_of_hs i transcript_Finished) *
    StreamAE.writer (ackId_of_hs i transcript_Finished)
    exporter (ex1Id_of_hs i transcript2) 
// missing late materials    
    )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> modifies_none h0 h1 (*TBC*) )
=
  dbg ("ks_client_13_sf hashed_log = "^print_bytes transcript1);
  let C13_wait_Finished1 h ae transcript_fk cfk sfk ams = state in

  // let FinishedID #li _ = dfst cfk in // TODO loginfo
  // let secretId = ApplicationSecretID asId in
  // let c_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  // let s_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  // let emsId : exportId li = ExportID asId log in

  let i2 = ams_of_hs i in 
  let ctsId = ctsId_of_as i2 transcript2 in 
  let stsId = ctsId_of_as i2 transcript2 in 
  let exsId = exsId_of_as i2 transcript2 in 

  let info = magic() in 
  let cts: secret ctsId = Idx.derive h ams "c ap traffic" transcript2 info in
  let sts: secret stsId = Idx.derive h ams "s ap traffic" transcript2 info in
  let exs: secret exsId = Idx.derive h ams "exp master"   transcript2 info in
  let (ck,civ) = keygen_13 h cts ae in
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("application traffic secret[C]:   "^print_bytes cts);
  dbg ("application traffic secret[S]:   "^print_bytes sts);
  dbg ("exporter master secret:          "^print_bytes ems);
  dbg ("application key[C]:              "^print_bytes ck^", IV="^print_bytes civ);
  dbg ("application key[S]:              "^print_bytes sk^", IV="^print_bytes siv);

  let id = ID13 (KeyID c_expandId) in
  assert_norm(peerId id = ID13 (KeyID s_expandId));
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StAE.coerce HS.root id (ckv @| civ) in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let rw = StAE.coerce HS.root id (skv @| siv) in
  let r = StAE.genReader HS.root rw in

  let next = C13_wait_Finished2 h ae ams (cts,sts) in
  // what to do with next?
  (r, w, exs)


/// Continues from the application master secret, now that we have the
/// digest of the complete handshake. We keep this secret (required to
/// compute the RMS) and return the application AE keys to install. We
/// also immediately derive and return the next transport secrets, to
/// help with forward secrecy.
/// 
val server13_ServerFinished: 
  #i: amsId -> 
  s: ams i ->
  ha: kdfa {ha = ha_of_id i} -> 
  aea: option (a: aeAlg {a = get_aeadAlg i}) -> 
  tr: transcript -> 
  tag: digest i tr -> 
  ST (
    StreamAE.reader (cts_of_ams i) * 
    StreamAE.writer (sts_of_ams i) *
    secret (x1s_of_ams i) *
    next_ts (cts_of_ams i) *
    next_ts (sts_of_ams i) )
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)

let server13_ServerFinished #i ams ha aea tr tag =   
  let ems = derive_secret ams h "exp master" tr tag in
  let cts = derive ha ams "c ap traffic" tr tag ha in
  let sts = derive ha ams "s ap traffic" tr tag ha in
  let r   = derive_streamAE ha ae cts parent in
  let w   = derive_streamAE ha ae sts parent in 
  let cts'= derive ha cts "traffic upd" Expand ha in
  let sts'= derive ha cts "traffic upd" Expand ha in 
  dbg ("server13_ServerFinished hash   = "^print_bytes tag);
  dbg ("exporter master secret:          "^print_bytes (leak_secret ems));
  dbg ("application traffic secret[C,0]: "^print_bytes (leak_secret cts));
  dbg ("application traffic secret[S,0]: "^print_bytes (leak_secret sts));
  dbg ("application traffic secret[C,1]: "^print_bytes (leak_secret cts'));
  dbg ("application traffic secret[S,1]: "^print_bytes (leak_secret sts'));
  r, w, ems, cts', sts'

/// Final step for both client13 and server13, returning the
/// resumption master secret; the application master secret should
/// then be discarded.

val rms13_ClientFinished: 
  #i: amsId -> 
  s: ams i -> 
  ha: kdfa {ha = ha_of_id i} -> 
  tr: transcript -> // [ClientHello; ...; ClientFinished]
  tag: digest i tr -> 
  ST (secret (rms_of_ams i tr))
  (requires fun h0 -> True 
    // multi-functionality inv
    )
  (ensures fun h0 r h1 -> True 
    // multi-functionality inv
    // modifies some KDF
    )
let rms13_ClientFinished #i ams ha tr tag =
  let rms = derive_secret ha ams "res master" tr tag ha in
  dbg ("resumption master secret:        "^print_bytes (leak_secret rms));
  rms

/// For each ticket received from the server,
/// generate a PSK from the current RMS and incoming ticket nonce
/// (may be called several times).
///
/// Sharable between client13 and server13

// problem: there is no transcript associated with nonce, so we will
// probably need to add some ExpandNonce.

val derive_resumption_secret:
  i: id ->
  s: secret i ->
  ha: kdfa {ha = ha_of_id i} -> 
  nonce: bytes -> // really?
  ST (secret (psk_of_rms i i))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> modifies_none h0 h1)

let derive_resumption_secret i s ha nonce = 
  dbg "ks_client_13_rms";
  dbg ("Recall RMS: "^hex_of_bytes rms);
  derive ha rms "resumption" (ExpandLog nonce) ha 

/// Rekeying for both client13 and server13, also returning the next
/// transport secret.
/// 
let rekey 
  (#i: ts_id) 
  (ha: prfa {ha = ha_of_i i})
  (aea: aeadAlg {aea = aeadAlg_of_i i}) 
  (ts: next_transport_secret i) 
  (rw: TLSConstants.rw {rw = rw_of_i i})
  (parent: rgn): 
  ST( 
    StreamAE.key (ts_of_ts i) ) rw *
    next_transport_secret (ts_of_ts i) 
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
=
  let k  = derive_streamAE #i ts rw (aea,parent) in 
  let j: ts_id = ts_of_ts i in 
  let ts: secret j = derive ts ha "traffic upd" Expand in 
  k, ts
    

(******************************************************************)

// Called by Hanshake when DH key echange is negotiated; 
// 3 incoming states: was (C12_Full_CH? (C?.s st) \/ C12_Resume_CH? (C?.s st) \/ C_13_wait_SH? (C?.s st)))

val client12_full_dh: 
  cr: random -> 
  sr: random -> 
  pv: protocolVersion ->
  cs: cipherSuite -> 
  ems: bool -> 
  gx:(g:CommonDH.group & CommonDH.share g) -> ST (ks12_state * CommonDH.share (dfst gx))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    (C12_wait_MS? st \/ C12_has_MS? st) /\ 
    modifies_none h0 h1 // TODO modifies for DH
  )
let client12_full_dh ks sr pv cs ems (|g,gx|) =
  let KS #region st = ks in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let gy, pmsb = CommonDH.dh_responder #g gx in
  dbg ("g^x: "^sprint_share gx);
  dbg ("g^y: "^sprint_share gy);
  dbg ("PMS: "^print_bytes pmsb);
  let dhpmsId = PMS.DHPMS g gx gy (PMS.ConcreteDHPMS pmsb) in
  let ns =
    if ems then
      C12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      dbg ("master secret: "^print_bytes ms);
      let msId = StandardMS dhpmsId csr kef in
      C12_has_MS csr alpha msId ms in
  ns, gy

// Called by Handshake after server hello when a full RSA key exchange is negotiated
// returns the encrypted (currently disabled)
// pre was: (C12_Full_CH? (C?.s st) \/ C12_Resume_CH? (C?.s st)))
val client12_full_rsa: 
  cr: random -> 
  sr:random -> 
  pv:protocolVersion -> 
  cs:cipherSuite -> 
  ems:bool -> 
  RSAKey.pk -> ST (ks12_state * bytes)
  (requires fun h0 -> True)
  (ensures fun h0 (st,r) h1 -> 
    (C12_wait_MS? st \/ C12_has_MS? st) /\ 
    modifies_none h0 h1 // TODO modifies for RSA
  )
let client12_full_rsa cr sr pv cs ems pk =
  let alpha = (pv, cs, ems) in
  let csr = cr @| sr in
  let rsapms = PMS.genRSA pk pv in
  let pmsb = PMS.leakRSA pk pv rsapms in
  let encrypted = CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 pmsb in
  let rsapmsId = PMS.RSAPMS(pk, pv, rsapms) in
  let ns =
    if ems then
      C12_wait_MS csr alpha rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      dbg ("master secret: "^print_bytes ms);
      let msId = StandardMS rsapmsId csr kef in
      C12_has_MS csr alpha msId ms in
  ns, encrypted

// second call from client_ServerHelloDone
val client12_set_session_hash: 
  ks: ks12_state -> 
  h:bytes -> ST (ks12_state * TLSPRF.key * recordInstance)
  (requires fun h0 ->
    C12_wait_MS? st \/ C12_has_MS? st)
  (ensures fun h0 (st,prfk,ak) h1 ->
    C12_has_MS? st /\ 
    modifies_none h0 h1)

let client12_set_session_hash st digest =
  dbg ("client12_set_session_hash hashed_log = "^print_bytes digest);
  let st, ms =
    match st with
    | C12_has_MS csr alpha msId ms ->
      dbg ("master secret:"^print_bytes ms);
      st, ms
    | C12_wait_MS csr alpha pmsId pms ->
      let (pv, cs, ems) = alpha in
      let kef = kefAlg pv cs ems in
      let h = verifyDataHashAlg_of_ciphersuite cs in
      let msId, ms =
        if ems then (
          let ms = TLSPRF.prf (pv,cs) pms (utf8 "extended master secret") digest 48 in
          dbg ("extended master secret:"^print_bytes ms);
          let msId = ExtendedMS pmsId digest kef in
          msId, ms )
        else (
          let ms = TLSPRF.extract kef pms csr 48 in
          dbg ("master secret:"^print_bytes ms);
          let msId = StandardMS pmsId csr kef in
          msId, ms ) in 
      C12_has_MS csr alpha msId ms, ms
    in
  let appk = ks12_record_key ks in
  let fink = TLSPRF.coerce ms in 
  (st, fink, appk)

// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************

(*)
let client12_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C12_has_MS? (C?.s st))
  (ensures fun h0 r h1 -> h1 == h0)
  =
  let KS #region st = ks in
  let C (C12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  TLSPRF.verifyData (pv,cs) ms Client log

let server12_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    S? st /\ S12_has_MS? (S?.s st))
  (ensures fun h0 r h1 -> h1 == h0)
  =
  let KS #region st = ks in
  let S (S12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  TLSPRF.verifyData (pv,cs) ms Client log

let server12_server_finished ks
  : ST (svd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    S? st /\ S12_has_MS? (S?.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid !{as_ref st} ( h0) ( h1))
  =
  let KS #region st = ks in
  let S (S12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  st := S S_Done;
  TLSPRF.verifyData (pv,cs) ms Server log

let client12_server_finished ks: ST (svd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C12_has_MS? (C?.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid !{as_ref st} ( h0) ( h1))
  =
  let KS #region st = ks in
  let C (C12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Server log
*)

val getId: recordInstance -> GTot id
let getId (StAEInstance #i rd wr) = i


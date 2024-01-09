module MiTLS.Old.KeySchedule
open MiTLS

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes
open FStar.Error
//open FStar.Integers 

open MiTLS.TLSError
open MiTLS.TLSConstants
open MiTLS.Extensions
open MiTLS.TLSInfo
open MiTLS.Range
open MiTLS.StatefulLHAE
open MiTLS.HKDF
open MiTLS.PSK

module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module H = MiTLS.Hashing.Spec

module HMAC_UFCMA = MiTLS.Old.HMAC.UFCMA

type finishedId = HMAC_UFCMA.finishedId

(* A flag for runtime debugging of computed keys.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false *)
let discard (b:bool): ST unit (requires (fun _ -> True))
 (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print s = discard (IO.debug_print_string ("KS | "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  if DebugFlags.debug_KS then print else (fun _ -> ())

#set-options "--admit_smt_queries true"

let print_share (#g:CommonDH.group) (s:CommonDH.share g) : ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let kb = CommonDH.serialize_raw #g s in
  let kh = FStar.Bytes.hex_of_bytes kb in
  dbg ("Share: "^kh)

(********************************************
*    Resumption PSK is disabled for now     *
*********************************************

abstract type res_psk (i:rmsId) =
  b:bytes{exists i.{:pattern index b i} index b i <> 0z}

abstract type res_context (i:rmsId) =
  b:bytes{length b = CoreCrypto.H.hash_len (rmsId_hash i)}

private type res_psk_entry (i:rmsId) =
  (res_psk i) * (res_context i) * ctx:psk_context * leaked:(rref tls_tables_region bool)

let res_psk_injective (m:MDM.map' rmsId res_psk_entry) =
  forall i1 i2.{:pattern (MDM.sel m i1); (MDM.sel m i2)}
       i1 = i2 <==> (match MDM.sel m i1, MDM.sel m i2 with
                  | Some (psk1, _, _, _), Some (psk2, _, _, _) -> b2t (equalBytes psk1 psk2)
                  | _ -> True)

let res_psk_table : MDM.t tls_tables_region rmsId res_psk_entry res_psk_injective =
  MDM.alloc #TLSConstants.tls_tables_region #rmsId #res_psk_entry #res_psk_injective

let registered_res_psk (i:rmsId) (h:HH.t) =
  b2t (Some? (MDM.sel (HS.sel h res_psk_table) i))

let res_psk_context (i:rmsId{registered_res_psk i}) =
  let (_, _, c, _) = Some.v (MDM.sel res_psk_table i) in c

private let res_psk_value (i:rmsId{registered_res_psk i}) =
  let (psk, _, _, _) = Some.v (MDM.sel res_psk_table i) in psk

**)

// PSK (internal/external multiplex, abstract)
// Note that application PSK is externally defined but should
// be idealized together with KS
val psk (i:esId) : Type0

let read_psk (i:PSK.pskid)
  : ST (esId * pskInfo * PSK.app_psk i)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let c = PSK.psk_info i in
  let id =
    if Some? c.ticket_nonce then
      let (| li, rmsid |) = Ticket.dummy_rmsid c.early_ae c.early_hash in
      ResumptionPSK #li rmsid
    else
      ApplicationPSK #(c.early_hash) #(c.early_ae) i
    in
  (id, c, PSK.psk_value i)

type binderId = i:pre_binderId{valid (I_BINDER i)}
type hsId = i:TLSInfo.pre_hsId{valid (I_HS i)}
type asId = i:pre_asId{valid (I_AS i)}

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

// miTLS 0.9:
// ==========
// PRF (type pms) -> TLSInfo (type id) -> KEF (extract pms)
//                     \ StatefulLHAE (coerce id) /
// TODO rework old 1.2 types
type ms = bytes
type pms = bytes

// Early secret (abstract)
val es (i:esId) : Type0

// Handshake secret (abstract)
val hs (i:hsId) : Type0
type fink (i:finishedId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Finished i) (fun _ -> True)
let trivial (_: bytes) = True
type binderKey (i:binderId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Binder i) trivial

// TLS 1.3 master secret (abstract)
val ams (i:asId) : Type0

type rekeyId (li:logInfo) = i:expandId li{
  (let ExpandedSecret _ t _ = i in
    ApplicationTrafficSecret? t \/
    ClientApplicationTrafficSecret? t \/
    ServerApplicationTrafficSecret? t)}

val rekey_secrets (#li:_) (i:expandId li) : Type0

type raw_rekey_secrets = {
  rekey_aead: aeadAlg;
  rekey_hash: hash_alg;
  rekey_client: bytes;
  rekey_server: bytes;
}

// Leaked to HS for tickets
(*abstract*) type rms #li (i:rmsId li) = H.tag (rmsId_hash i)

type ems #li (i:exportId li) = H.tag (exportId_hash i)

// TODO this is superseeded by StAE.state i
// but I'm waiting for it to be tested to switch over
// TODO use the newer index types
type recordInstance =
  | StAEInstance: 
    #id:TLSInfo.id ->
    r: StAE.reader (peerId id) ->
    w: StAE.writer id ->
    pn: option bytes * option bytes ->
    recordInstance

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

type exportKey = (li:logInfo & i:exportId li & ems i)

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
type ks_alpha13 = ae:aeadAlg * h:hash_alg

type ks_client_state =
| C_Init: cr:random -> ks_client_state
| C_12_Resume_CH: cr:random -> si:sessionInfo -> msId:TLSInfo.msId -> ms:ms -> ks_client_state
| C_12_Full_CH: cr:random -> ks_client_state
| C_12_wait_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.pmsId -> pms:pms -> ks_client_state
| C_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_client_state
| C_13_wait_SH: cr:random -> esl: list (i:esId{~(NoPSK? i)} & es i) ->
                gs:list (g:CommonDH.group & CommonDH.ikeyshare g) -> ks_client_state
| C_13_wait_SF: alpha:ks_alpha13 -> (i:finishedId & cfk:fink i) -> (i:finishedId & sfk:fink i) ->
                (i:asId & ams:ams i) -> ks_client_state
| C_13_wait_CF: alpha:ks_alpha13 -> (i:finishedId & cfk:fink i) -> (i:asId & ams:ams i) ->
                (li:logInfo & i:rekeyId li & rekey_secrets i) -> ks_client_state
| C_13_postHS: alpha:ks_alpha13 -> (li:logInfo & i:rekeyId li & rekey_secrets i) ->
                (li:logInfo & i:rmsId li & rms i) -> ks_client_state
| C_Done

type ks_server_state =
| S_Init: sr:random -> ks_server_state
| S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha12 -> our_share:(g:CommonDH.group & CommonDH.ikeyshare g) -> ks_server_state
| S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha12 -> ks_server_state
| S_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_server_state
| S_13_wait_SH: alpha:ks_alpha13 -> cr:random -> sr:random -> es:(i:esId & es i) ->
                hs:( i:hsId & hs i ) -> ks_server_state
| S_13_wait_SF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:finishedId & sfk:fink i ) ->
                ( i:asId & ams:ams i ) -> ks_server_state
| S_13_wait_CF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:asId & ams i ) ->
                ( li:logInfo & i:rekeyId li & rekey_secrets i ) ->  ks_server_state
| S_13_postHS: alpha:ks_alpha13 -> ( li:logInfo & i:rekeyId li & rekey_secrets i ) ->
	        ( li:logInfo & i:rmsId li & rms i) -> ks_server_state
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
| KS:
  #region:rid ->
  state:(ref ks_state){HS.frameOf state = region} ->
  is_quic: bool ->
  ks

//17-04-17 CF: expose it as a concrete ref?
//17-04-17 CF: no need to keep the region, already in the ref.

// Extract keys and IVs from a derived 1.3 secret
private let keygen_13 h secret ae is_quic : St (bytes * bytes * option bytes) =
  let kS = EverCrypt.aead_keyLen ae in
  let iS = 12ul in // IV length
  let lk, liv = if is_quic then "quic key", "quic iv" else "key", "iv" in
  let kb = HKDF.expand_label #h secret lk empty_bytes kS in
  let ib = HKDF.expand_label #h secret liv empty_bytes iS in
  let pn = if is_quic then
      Some (HKDF.expand_label #h secret "quic hp" empty_bytes kS)
    else None in
  (kb, ib, pn)

// Extract finished keys
private let finished_13 h secret : St (bytes) =
  HKDF.expand_label #h secret "finished" empty_bytes (Hacl.Hash.Definitions.hash_len h)

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
let create: #rid:rid -> role -> is_quic:bool -> ST (ks * random)
  (requires fun h -> rid<>root)
  (ensures fun h0 (r,_) h1 ->
    let KS #ks_region state iq = r in
    HS.fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ iq = is_quic
    /\ modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref state))) ( h0) ( h1)) =
  fun #rid r is_quic ->
  ST.recall_region rid;
  let ks_region = new_region rid in
  let nonce = Nonce.mkHelloRandom r ks_region in
  let istate = match r with
    | Client -> C (C_Init nonce)
    | Server -> S (S_Init nonce) in
  (KS #ks_region (ralloc ks_region istate) is_quic), nonce

private let group_of_valid_namedGroup
  (g:CommonDH.supportedNamedGroup)
  : CommonDH.group
  = Some?.v (CommonDH.group_of_namedGroup g)

effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)

let rec map_ST: (#a:Type) -> (#b:Type) -> (a -> ST0 b) -> list a -> ST0 (list b) =
  fun #_ #_ f x -> match x with
  | [] -> []
  | a::tl -> f a :: map_ST f tl

private let group_of_cks = function
  | CommonDH.Share g _ -> Some?.v (CommonDH.namedGroup_of_group g)
  | CommonDH.UnknownShare g _ -> g

private let keygen (g:CommonDH.group)
  : St (g:CommonDH.group & CommonDH.ikeyshare g)
  = (| g, CommonDH.keygen g |)

private
let serialize_share (gx:(g:CommonDH.group & CommonDH.ikeyshare g)) =
    let (| g, gx |) = gx in
    match CommonDH.namedGroup_of_group g with
      | None -> None // Impossible
      | Some ng -> Some (CommonDH.Share g (CommonDH.ipubshare #g gx))

let rec map_ST_keygen: list CommonDH.group -> ST0 (list (g:CommonDH.group & CommonDH.ikeyshare g)) =
 fun l ->
  match l with
  | [] -> []
  | hd :: tl -> keygen hd :: map_ST_keygen tl

let ks_client_init: ks:ks -> ogl: option CommonDH.supportedNamedGroups
  -> ST (option CommonDH.clientKeyShare)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 ogxl h1 ->
    let KS #rid st _ = ks in
    (None? ogl ==> None? ogxl) /\
    (Some? ogl ==> (Some? ogxl /\ Some?.v ogl == List.Tot.map group_of_cks (Some?.v ogxl))) /\
    modifies (Set.singleton rid) h0 h1 /\
    HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1)) =

  fun ks ogl ->
  dbg ("ks_client_init "^(if ogl=None then "1.2" else "1.3"));
  let KS #rid st _ = ks in
  let C (C_Init cr) = !st in
  match ogl with
  | None -> // TLS 1.2
    st := C (C_12_Full_CH cr);
    None
  | Some gl -> // TLS 1.3
    let groups = List.Tot.map group_of_valid_namedGroup gl in
    let gs = map_ST_keygen groups in
    let gxl = List.Tot.choose serialize_share gs in
    st := C (C_13_wait_SH cr [] gs);
    Some gxl

type ticket13 = t:Ticket.ticket{Ticket.Ticket13? t}

private val mk_binder (#rid:rid) (pskid:psk_identifier) (t:ticket13)
  : ST ((i:binderId & bk:binderKey i) * (i:esId{~(NoPSK? i)} & es i))
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

private let rec tickets13 #rid acc (l:list (psk_identifier * Ticket.ticket))
  : ST0 (list ((i:binderId & bk:binderKey i) * (i:esId{~(NoPSK? i)} & es i)))
  = match l with
  | [] -> List.Tot.rev acc
  | (pskid, t) :: r -> tickets13 #rid (if Ticket.Ticket13? t then (mk_binder #rid pskid t)::acc else acc) r

let ks_client_13_get_binder_keys ks l =
  let KS #rid st _ = ks in
  let C (C_13_wait_SH cr [] gs) = !st in
  let (bkl, esl) = List.Tot.split (tickets13 #rid [] l) in
  st := C (C_13_wait_SH cr esl gs);
  bkl

let ks_client_13_hello_retry ks (g:CommonDH.group)
  : ST0 (CommonDH.share g) =
  let KS #rid st _ = ks in
  let C (C_13_wait_SH cr esl gs) = !st in
  let s : CommonDH.ikeyshare g = CommonDH.keygen g in
  st := C (C_13_wait_SH cr esl [(| g, s |)]);
  CommonDH.ipubshare #g s

// Derive the early data key from the first offered PSK
// Only called if 0-RTT is enabled on the client
val ks_client_13_ch (ks:_) (log:bytes): ST (exportKey * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies_none h0 h1)

val ks_server_12_init_dh: ks:ks -> cr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> g:CommonDH.group -> ST (CommonDH.share g)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  
val ks_server_13_init:
  ks:ks ->
  cr:random ->
  cs:cipherSuite ->
  pskid:option PSK.pskid ->
  g_gx:option (g:CommonDH.group & CommonDH.share g) ->
  ST (option CommonDH.serverKeyShare * option (i:binderId & binderKey i))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ (Some? g_gx \/ Some? pskid)
    /\ (Some? g_gx ==> Some? (CommonDH.namedGroup_of_group (dfst (Some?.v g_gx))))
    /\ CipherSuite13? cs)
  (ensures fun h0 (gy, bk) h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ (Some? bk <==> Some? pskid)
    /\ (Some? gy \/ Some? bk)
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) h0 h1)


val ks_server_13_0rtt_key (ks:_) (log:bytes)
  : ST ((li:logInfo & i:exportId li & ems i) * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val ks_server_13_sh: ks:ks -> log:bytes -> ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_server_13_server_finished ks
  : ST (i:finishedId & fink i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
  =
  let KS #region st _ = ks in
  let S (S_13_wait_SF _ _ sfk _) = !st in
  sfk

let ks_server_13_client_finished ks
  : ST (i:finishedId & fink i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
  =
  let KS #region st _ = ks in
  let S (S_13_wait_CF _ cfk _ _) = !st in
  cfk

// Will become private; public API will have
// ks_client_12_keygen: ks -> (i:id * w:StatefulLHAE.writer i)
// ks_server_12_keygen: ...
val ks_12_finished_key: ks:ks -> ST (key:TLSPRF.key)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    match st with
    | C (C_12_has_MS _ _ _ _) | S (S_12_has_MS _ _ _ _) -> true
    | _ -> false)
  (ensures fun h0 r h1 ->
    modifies Set.empty h0 h1)

let ks_12_ms ks =
  let KS #region st _ = ks in
  match !st with
  | C (C_12_has_MS _ _ msId ms) -> (msId, ms)
  | S (S_12_has_MS _ _ msId ms) -> (msId, ms)

private val ks_12_record_key: ks:ks -> St recordInstance
(* 1.2 resumption *)

// We can potentially 1.2 resume from 1.2 or 1.3 ClientHello
let ks_client_12_resume (ks:ks) (sr:random) (pv:protocolVersion) (cs:cipherSuite)
  (ems:bool) (msId:TLSInfo.msId) (ms:bytes) : ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ (C_12_Full_CH? (C?.s kss) \/ C_13_wait_SH? (C?.s kss)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg "ks_client_12_resume";
  let KS #rid st _ = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_13_wait_SH cr _ _) -> cr in
  dbg ("Recall MS: "^(print_bytes ms));
  st := C (C_12_has_MS (cr @| sr) (pv, cs, ems) msId ms);
  ks_12_record_key ks

let ks_server_12_resume (ks:ks) (cr:random) (pv:protocolVersion) (cs:cipherSuite)
  (ems:bool) (msId:msId) (ms:bytes) =
  dbg ("ks_server_12_resume");
  let KS #region st _ = ks in
  let S (S_Init sr) = !st in
  dbg ("Recall MS: "^(print_bytes ms));
  st := S (S_12_has_MS (cr @| sr) (pv, cs, ems) msId ms);
  ks_12_record_key ks

(******************************************************************)

// log is the raw HS log, used for EMS derivation
val ks_server_12_cke_dh: ks:ks -> gy:(g:CommonDH.group & CommonDH.share g) ->
  log:bytes -> ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_12_wait_CKE_DH? (S?.s kss) /\
    (let S (S_12_wait_CKE_DH _ _ (| g', _ |)) = kss in
    g' = dfst gy)) // Responder share must be over the same group as initiator's
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

(**
// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val ks_client_12_resume: ks:ks -> random -> pv:protocolVersion -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_12_Resume_CH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_client_12_resume ks sr pv cs =
  let KS #region st = ks in
  let C (C_12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extended_ms in
  st := C (C_12_has_MS csr (pv, cs, ems) msId ms)
*)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

private let group_matches
              (g:CommonDH.group)
              (gx:(x:CommonDH.group & CommonDH.ikeyshare g)) =
    let (| g', _ |) = gx in
    g=g'

val ks_client_13_sh: ks:ks -> sr:random -> cs:cipherSuite -> h:bytes ->
  gy:option (g:CommonDH.group & CommonDH.share g) -> accept_psk:option nat ->
  ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss) /\
    // Ensure that the PSK accepted is one offered
    (let C_13_wait_SH _ ei gc = C?.s kss in
     (match gy with
     | Some (| g, _ |) -> List.Tot.existsb (fun gx -> g = dfst gx) gc
     | None -> True)
     /\
     (match ei, accept_psk with
      | [], None -> True
      | _::_ , Some n -> n < List.Tot.length ei
      | _ -> False)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))


(******************************************************************)

val ks_client_13_sf (ks:_) (log:bytes)
  : ST (( i:finishedId & sfk:fink i ) * ( i:finishedId & cfk:fink i ) * recordInstance * exportKey)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

val ks_server_13_sf (ks:_) (log:bytes)
  : ST (recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

val ks_server_13_cf (ks:_) (log:bytes) : ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_CF? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_server_13_rms ks : ST (li:logInfo & i:rmsId li & rms i)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_postHS? (S?.s kss))
  (ensures fun h0 r h1 -> modifies (Set.empty) h0 h1)
  =
  let KS #region st _ = ks in
  let S (S_13_postHS _ _ rms) = !st in
  rms
  
// Handshake must call this when ClientFinished goes into log
val ks_client_13_cf (ks:_) (log:bytes) : ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_CF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

// Generate a PSK out of the current RMS and incoming ticket nonce
// May be called several times if server sends multiple tickets
let ks_client_13_rms_psk ks (nonce:bytes) : ST (bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_postHS? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies_none h0 h1)
  =
  dbg "ks_client_13_rms";
  let KS #region st _ = ks in
  let C (C_13_postHS _ _ rmsi) = !st in
  let (| li, rmsId, rms |) = rmsi in
  dbg ("Recall RMS: "^(hex_of_bytes rms));
  HKDF.derive_secret (rmsId_hash rmsId) rms "resumption" nonce

val ks_13_rekey_secrets (ks:_) : ST (option raw_rekey_secrets)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies_none h0 h1)

(******************************************************************)

// Called by Hanshake when DH key echange is negotiated
val ks_client_12_full_dh: ks:ks -> sr:random -> pv:protocolVersion ->
  cs:cipherSuite -> ems:bool -> gx:(g:CommonDH.group & CommonDH.share g) ->
  ST (CommonDH.share (dfst gx))
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\
    (C_12_Full_CH? (C?.s st) \/ C_12_Resume_CH? (C?.s st) \/ C_13_wait_SH? (C?.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))


// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\
    (C_12_Full_CH? (C?.s st) \/ C_12_Resume_CH? (C?.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st _ = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

val ks_client_12_set_session_hash: ks:ks -> h:bytes -> ST (TLSPRF.key * recordInstance)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ (C_12_wait_MS? (C?.s st) \/ C_12_has_MS? (C?.s st)))
  (ensures fun h0 r h1 ->
    let st = sel h1 (KS?.state ks) in
    modifies (Set.singleton (KS?.region ks)) h0 h1 /\
    C? st /\ (C_12_has_MS? (C?.s st))
    /\ HS.modifies_ref (KS?.region ks) (Set.singleton (Heap.addr_of (as_ref (KS?.state ks)))) ( h0) ( h1))


// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************

(*)
let ks_client_12_client_finished ks
  : ST (cvd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ C_12_has_MS? (C?.s st))
  (ensures fun h0 r h1 -> h1 == h0)
  =
  let KS #region st = ks in
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
  let KS #region st = ks in
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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid !{as_ref st} ( h0) ( h1))
  =
  let KS #region st = ks in
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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid !{as_ref st} ( h0) ( h1))
  =
  let KS #region st = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
//  let h = verifyDataHashAlg_of_ciphersuite cs in
//  let log = HandshakeLog.getHash hsl h in
  let log = HandshakeLog.getBytes hsl in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Server log
*)

let getId: recordInstance -> GTot id =
fun (StAEInstance #i _ _ _) -> i

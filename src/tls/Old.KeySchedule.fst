module Old.KeySchedule

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes
open FStar.Error

open TLSError
open TLSConstants
open Extensions
open TLSInfo
open Range
open StatefulLHAE
open Old.HKDF
open PSK

module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module H = Hashing.Spec

module HMAC_UFCMA = Old.HMAC.UFCMA
module HKDF = Old.HKDF

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
  b:bytes{length b = CoreCrypto.H.tagLen (rmsId_hash i)}

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
abstract let psk (i:esId) =
  b:bytes{len b = H.tagLen (esId_hash i)}

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
abstract type es (i:esId) = H.tag (esId_hash i)

// Handshake secret (abstract)
abstract type hs (i:hsId) = H.tag (hsId_hash i)
type fink (i:finishedId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Finished i) (fun _ -> True)
let trivial (_: bytes) = True
type binderKey (i:binderId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Binder i) trivial

// TLS 1.3 master secret (abstract)
abstract type ams (i:asId) = H.tag (asId_hash i)

type rekeyId (li:logInfo) = i:expandId li{
  (let ExpandedSecret _ t _ = i in
    ApplicationTrafficSecret? t \/
    ClientApplicationTrafficSecret? t \/
    ServerApplicationTrafficSecret? t)}

abstract type rekey_secrets #li (i:expandId li) =
  H.tag (expandId_hash i) * H.tag (expandId_hash i)

// Leaked to HS for tickets
(*abstract*) type rms #li (i:rmsId li) = H.tag (rmsId_hash i)

type ems #li (i:exportId li) = H.tag (exportId_hash i)

// TODO this is superseeded by StAE.state i
// but I'm waiting for it to be tested to switch over
// TODO use the newer index types
type recordInstance =
  | StAEInstance: #id:TLSInfo.id -> StAE.reader (peerId id) -> StAE.writer id -> recordInstance

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
                ks_server_state
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
| KS: #region:rid -> state:(ref ks_state){HS.frameOf state = region} -> ks
//17-04-17 CF: expose it as a concrete ref?
//17-04-17 CF: no need to keep the region, already in the ref.

// Extract keys and IVs from a derived 1.3 secret
private let keygen_13 h secret ae : St (bytes * bytes) =
  let kS = CoreCrypto.aeadKeySize ae in
  let iS = CoreCrypto.aeadRealIVSize ae in
  let kb = HKDF.hkdf_expand_label h secret "key" empty_bytes kS in
  let ib = HKDF.hkdf_expand_label h secret "iv" empty_bytes iS in
  (kb, ib)

// Extract finished keys
private let finished_13 h secret : St (bytes) =
  HKDF.hkdf_expand_label h secret "finished" empty_bytes (UInt32.v (H.tagLen h))

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

private let keygen (g:CommonDH.group)
  : St (g:CommonDH.group & CommonDH.ikeyshare g)
  = (| g, CommonDH.keygen g |)

val ks_client_init: ks:ks -> ogl: option CommonDH.supportedNamedGroups
  -> ST (option CommonDH.clientKeyShare)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 ogxl h1 ->
    let KS #rid st = ks in
    (None? ogl ==> None? ogxl) /\
    (Some? ogl ==> (Some? ogxl /\ Some?.v ogl == List.Tot.map group_of_cks (Some?.v ogxl))) /\
    modifies (Set.singleton rid) h0 h1 /\
    HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))


private
let serialize_share (gx:(g:CommonDH.group & CommonDH.ikeyshare g)) =
    let (| g, gx |) = gx in
    match CommonDH.namedGroup_of_group g with
      | None -> None // Impossible
      | Some ng -> Some (CommonDH.Share g (CommonDH.ipubshare #g gx))

private val map_ST_keygen: list CommonDH.group -> ST0 (list (g:CommonDH.group & CommonDH.ikeyshare g))
private let rec map_ST_keygen l =
  match l with
  | [] -> []
  | hd :: tl -> keygen hd :: map_ST_keygen tl

let ks_client_init ks ogl =
  dbg ("ks_client_init "^(if ogl=None then "1.2" else "1.3"));
  let KS #rid st = ks in
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

private let mk_binder (#rid) (pskid:PSK.pskid)
  : ST ((i:binderId & bk:binderKey i) * (i:esId{~(NoPSK? i)} & es i))
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let i, pski, psk = read_psk pskid in
  let h = pski.early_hash in
  dbg ("Loaded pre-shared key "^(print_bytes pskid)^": "^(print_bytes psk));
  let es : es i = HKDF.hkdf_extract h (H.zeroHash h) psk in
  dbg ("Early secret: "^(print_bytes es));
  let ll, lb =
    if ApplicationPSK? i then ExtBinder, "ext binder"
    else ResBinder, "res binder" in
  let bId = Binder i ll in
  let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
  dbg ("Binder key["^lb^"]: "^(print_bytes bk));
  let bk = finished_13 h bk in
  dbg ("Binder Finished key: "^(print_bytes bk));
  let bk : binderKey bId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Binder bId) trivial rid bk in
  (| bId, bk|), (| i, es |)

private val map_ST_mk_binder: #rid:rid -> list PSK.pskid -> ST0 (list ((i:binderId & bk:binderKey i) * (i:esId{~(NoPSK? i)} & es i)))
let rec map_ST_mk_binder #rid l =
  match l with
  | [] -> []
  | hd :: tl -> mk_binder #rid hd :: map_ST_mk_binder #rid tl

let ks_client_13_get_binder_keys ks pskl =
  let KS #rid st = ks in
  let C (C_13_wait_SH cr [] gs) = !st in
  let pskl = map_ST_mk_binder #rid pskl in
  let (bkl, esl) = List.Tot.split pskl in
  st := C (C_13_wait_SH cr esl gs);
  bkl

let ks_client_13_hello_retry ks (g:CommonDH.group)
  : ST0 (CommonDH.share g) =
  let KS #rid st = ks in
  let C (C_13_wait_SH cr esl gs) = !st in
  let s : CommonDH.ikeyshare g = CommonDH.keygen g in
  st := C (C_13_wait_SH cr esl [(| g, s |)]);
  CommonDH.ipubshare #g s

// Derive the early data key from the first offered PSK
// Only called if 0-RTT is enabled on the client
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

val ks_server_12_init_dh: ks:ks -> cr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> g:CommonDH.group -> ST (CommonDH.share g)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_Init? (S?.s kss)
    /\ CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_server_12_init_dh ks cr pv cs ems g =
  dbg "ks_server_12_init_dh";
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen g in
  let _ = print_share (CommonDH.ipubshare our_share) in
  let csr = cr @| sr in
  st := S (S_12_wait_CKE_DH csr (pv, cs, ems) (| g, our_share |));
  CommonDH.ipubshare our_share
  
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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ (Some? bk <==> Some? pskid)
    /\ (Some? gy \/ Some? bk)
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

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
        | Some (Ticket.Ticket13 cs li rmsId rms _ _ _) ->
          dbg ("Ticket RMS: "^(print_bytes rms));
          let i = ResumptionPSK #li rmsId in
          let CipherSuite13 _ h = cs in
          let nonce, _ = split id 12ul in
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
      dbg ("binder key:                      "^print_bytes bk);
      let bk = finished_13 h bk in
      dbg ("binder Finished key:             "^print_bytes bk);
      let bk : binderKey bId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Binder bId) (fun _ -> True) region bk in
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
      let gy, gxy = CommonDH.dh_responder g gx in
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

let ks_server_13_0rtt_key ks (log:bytes)
  : ST ((li:logInfo & i:exportId li & ems i) * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  dbg "ks_server_13_0rtt_key";
  let KS #region st = ks in
  let S (S_13_wait_SH (ae, h) cr sr (| esId, es |) _) = !st in

  let li = LogInfo_CH0 ({
    li_ch0_cr = cr;
    li_ch0_ed_ae = ae;
    li_ch0_ed_hash = h;
    li_ch0_ed_psk = empty_bytes;
  }) in
  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID esId) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret:     "^print_bytes ets);
  let expId : exportId li = EarlyExportID esId log in
  let early_export : ems expId = HKDF.derive_secret h es "e exp master" log in
  dbg ("Early exporter master secret:    "^print_bytes early_export);

  // Expand all keys from the derived early secret
  let (ck,civ) = keygen_13 h ets ae in
  dbg ("Client 0-RTT key:                "^print_bytes ck^", IV="^print_bytes civ);

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in
  let early_d = StAEInstance r rw in
  (| li, expId, early_export |), early_d

val ks_server_13_sh: ks:ks -> log:bytes -> ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_server_13_sh ks log =
  dbg ("ks_server_13_sh, hashed log = "^print_bytes log);
  let KS #region st = ks in
  let S (S_13_wait_SH (ae, h) cr sr _ (| hsId, hs |)) = !st in
  let secretId = HandshakeSecretID hsId in
  let li = LogInfo_SH ({
    li_sh_cr = cr;
    li_sh_sr = sr;
    li_sh_ae = ae;
    li_sh_hash = h;
    li_sh_psk = None;
  }) in
  let log : hashed_log li = log in

  let c_expandId = ExpandedSecret secretId ClientHandshakeTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ServerHandshakeTrafficSecret log in

  // Derived handshake secret
  let cts = HKDF.derive_secret h hs "c hs traffic" log in
  dbg ("handshake traffic secret[C]:     "^print_bytes cts);
  let sts = HKDF.derive_secret h hs "s hs traffic" log in
  dbg ("handshake traffic secret[S]:     "^print_bytes sts);
  let (ck,civ) = keygen_13 h cts ae in
  dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("handshake key[S]: "^print_bytes sk^", IV="^print_bytes siv);

  // Handshake traffic keys
  let id = ID13 (KeyID c_expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HS.root id (skv @| siv) in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in

  // Finished keys
  let cfkId = FinishedID c_expandId in
  let sfkId = FinishedID s_expandId in
  let cfk1 = finished_13 h cts in
  dbg ("finished key[C]:                 "^print_bytes cfk1);
  let sfk1 = finished_13 h sts in
  dbg ("finished key[S]:                 "^print_bytes sfk1);

  let cfk1 : fink cfkId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Finished cfkId) (fun _ -> True) region cfk1 in
  let sfk1 : fink sfkId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Finished sfkId) (fun _ -> True) region sfk1 in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  dbg ("Application salt:                "^print_bytes salt);

  // Replace handshake secret with application master secret
  let amsId = ASID saltId in
  let ams : ams amsId = HKDF.hkdf_extract h salt (H.zeroHash h) in
  dbg ("Application secret:              "^print_bytes ams);

  st := S (S_13_wait_SF (ae, h) (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| amsId, ams |));
  StAEInstance r w

let ks_server_13_server_finished ks
  : ST (i:finishedId & fink i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
  =
  let KS #region st = ks in
  let S (S_13_wait_SF _ _ sfk _) = !st in
  sfk

let ks_server_13_client_finished ks
  : ST (i:finishedId & fink i)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
  =
  let KS #region st = ks in
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

let ks_12_finished_key ks =
 let KS #region st = ks in
 let ms = match !st with
 | C (C_12_has_MS _ _ _ ms) -> ms
 | S (S_12_has_MS _ _ _ ms) -> ms in
 TLSPRF.coerce ms

let ks_12_ms ks =
  let KS #region st = ks in
  match !st with
  | C (C_12_has_MS _ _ msId ms) -> (msId, ms)
  | S (S_12_has_MS _ _ msId ms) -> (msId, ms)

private val ks_12_record_key: ks:ks -> St recordInstance
let ks_12_record_key ks =
  dbg "ks_12_record_key";
  let KS #region st = ks in
  let role, csr, alpha, msId, ms =
    match !st with
    | C (C_12_has_MS csr alpha msId ms) -> Client, csr, alpha, msId, ms
    | S (S_12_has_MS csr alpha msId ms) -> Server, csr, alpha, msId, ms in
  let cr, sr = split csr 32ul in
  let (pv, cs, ems) = alpha in
  let kdf = kdfAlg pv cs in
  let ae = get_aeAlg cs in
  let id = ID12 pv msId kdf ae cr sr role in
  let AEAD alg _ = ae in (* 16-10-18 FIXME! only correct for AEAD *)
  let klen = CoreCrypto.aeadKeySize alg in
  let slen = AEADProvider.salt_length id in
  let expand = TLSPRF.kdf kdf ms (sr @| cr) (UInt32.uint_to_t (klen + klen + slen + slen)) in
  dbg ("keystring (CK, CIV, SK, SIV) = "^(print_bytes expand));
  let k1, expand = split_ expand klen in
  let k2, expand = split_ expand klen in
  let iv1, iv2 = split_ expand slen in
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
let ks_client_12_resume (ks:ks) (sr:random) (pv:protocolVersion) (cs:cipherSuite)
  (ems:bool) (msId:TLSInfo.msId) (ms:bytes) : ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ (C_12_Full_CH? (C?.s kss) \/ C_13_wait_SH? (C?.s kss)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg "ks_client_12_resume";
  let KS #rid st = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_13_wait_SH cr _ _) -> cr in
  dbg ("Recall MS: "^(print_bytes ms));
  st := C (C_12_has_MS (cr @| sr) (pv, cs, ems) msId ms);
  ks_12_record_key ks

let ks_server_12_resume (ks:ks) (cr:random) (pv:protocolVersion) (cs:cipherSuite)
  (ems:bool) (msId:msId) (ms:bytes) =
  dbg ("ks_server_12_resume");
  let KS #region st = ks in
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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
let ks_server_12_cke_dh ks gy hashed_log =
  dbg "ks_server_12_cke_dh";
  let KS #region st = ks in
  let S (S_12_wait_CKE_DH csr alpha (| g, gx |)) = !st in
  let (pv, cs, ems) = alpha in
  let (| _, gy |) = gy in
  let _ = print_share gy in
  let pmsb = CommonDH.dh_initiator g gx gy in
  dbg ("PMS: "^(print_bytes pmsb));
  let pmsId = PMS.DHPMS g (CommonDH.ipubshare gx) gy (PMS.ConcreteDHPMS pmsb) in
  let kef = kefAlg pv cs ems in
  let msId, ms =
    if ems then
      begin
      let ms = TLSPRF.prf (pv,cs) pmsb (utf8_encode "extended master secret") hashed_log 48ul in
      dbg ("extended master secret:"^(print_bytes ms));
      let msId = ExtendedMS pmsId hashed_log kef in
      msId, ms
      end
    else
      begin
      let ms = TLSPRF.extract kef pmsb csr 48ul in
      dbg ("master secret:"^(print_bytes ms));
      let msId = StandardMS pmsId csr kef in
      msId, ms
      end
    in
  st := S (S_12_has_MS csr alpha msId ms);
  ks_12_record_key ks

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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

private let group_matches
              (g:CommonDH.group)
              (gx:(x:CommonDH.group & CommonDH.ikeyshare g)) =
    let (| g', _ |) = gx in
    g=g'

// ServerHello log breakpoint (client)
let ks_client_13_sh ks sr cs log gy accept_psk =
  dbg ("ks_client_13_sh hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let C (C_13_wait_SH cr esl gc) = !st in
  let CipherSuite13 ae h = cs in

  // Early secret: must derive zero here as hash is not known before
  let esId, es =
    match esl, accept_psk with
    | l, Some n ->
      let Some (| i, es |) : option (i:esId & es i) = List.Tot.nth l n in
      dbg ("recallPSK early secret:          "^print_bytes es);
      i, es
    | _, None ->
      let es = HKDF.hkdf_extract h (H.zeroHash h) (H.zeroHash h) in
      dbg ("no PSK negotiated. Early secret: "^print_bytes es);
      NoPSK h, es
  in

  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("handshake salt:                  "^print_bytes salt);

  let hsId, hs =
    match gy with
    | Some (| g, gy |) -> (* (PSK-)DHE *)
      let Some (| _, gx |) = List.Helpers.find_aux g group_matches gc in
      let gxy = CommonDH.dh_initiator g gx gy in
      dbg ("DH shared secret: "^(print_bytes gxy));
      let hsId = HSID_DHE saltId g (CommonDH.ipubshare gx) gy in
      let hs : hs hsId = HKDF.hkdf_extract h salt gxy in
      hsId, hs
    | None -> (* Pure PSK *)
      let hsId = HSID_PSK saltId in
      let hs : hs hsId = HKDF.hkdf_extract h salt (H.zeroHash h) in
      hsId, hs
    in
  dbg ("handshake secret:                "^print_bytes hs);

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
  dbg ("handshake traffic secret[C]:     "^print_bytes cts);
  let sts = HKDF.derive_secret h hs "s hs traffic" log in
  dbg ("handshake traffic secret[S]:     "^print_bytes sts);
  let (ck,civ) = keygen_13 h cts ae in
  dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("handshake key[S]:                "^print_bytes sk^", IV="^print_bytes siv);

  // Finished keys
  let cfkId = FinishedID c_expandId in
  let sfkId = FinishedID s_expandId in
  let cfk1 = finished_13 h cts in
  dbg ("finished key[C]: "^(print_bytes cfk1));
  let sfk1 = finished_13 h sts in
  dbg ("finished key[S]: "^(print_bytes sfk1));

  let cfk1 : fink cfkId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Finished cfkId) (fun _ -> True) region cfk1 in
  let sfk1 : fink sfkId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Finished sfkId) (fun _ -> True) region sfk1 in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  dbg ("application salt:                "^print_bytes salt);

  let asId = ASID saltId in
  let ams : ams asId = HKDF.hkdf_extract h salt (H.zeroHash h) in
  dbg ("application secret:              "^print_bytes ams);

  let id = ID13 (KeyID c_expandId) in
  assert_norm(ID13 (KeyID s_expandId) = peerId id);
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HS.root id (ckv @| civ) in
  let rw = StAE.coerce HS.root id (skv @| siv) in
  let r = StAE.genReader HS.root rw in
  st := C (C_13_wait_SF (ae, h) (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| asId, ams |));
  StAEInstance r w

(******************************************************************)

let ks_client_13_sf ks (log:bytes)
  : ST (( i:finishedId & sfk:fink i ) * ( i:finishedId & cfk:fink i ) * recordInstance * exportKey)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg ("ks_client_13_sf hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let C (C_13_wait_SF alpha cfk sfk (| asId, ams |)) = !st in
  let (ae, h) = alpha in

  let FinishedID #li _ = dfst cfk in // TODO loginfo
  let log : hashed_log li = log in
  let secretId = ApplicationSecretID asId in
  let c_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in

  let cts = HKDF.derive_secret h ams "c ap traffic" log in
  dbg ("application traffic secret[C]:   "^print_bytes cts);
  let sts = HKDF.derive_secret h ams "s ap traffic" log in
  dbg ("application traffic secret[S]:   "^print_bytes sts);
  let emsId : exportId li = ExportID asId log in
  let ems = HKDF.derive_secret h ams "exp master" log in
  dbg ("exporter master secret:          "^print_bytes ems);
  let exporter1 = (| li, emsId, ems |) in

  let (ck,civ) = keygen_13 h cts ae in
  dbg ("application key[C]:              "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv) = keygen_13 h sts ae in
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

  st := C (C_13_wait_CF alpha cfk (| asId, ams |) (| li, c_expandId, (cts,sts)|));
  (sfk, cfk, StAEInstance r w, exporter1)

let ks_server_13_sf ks (log:bytes)
  : ST (recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg ("ks_server_13_sf hashed_log = "^print_bytes log);
  let KS #region st = ks in
  let S (S_13_wait_SF alpha cfk _ (| asId, ams |)) = !st in
  let FinishedID #li _ = dfst cfk in // TODO loginfo
  let (ae, h) = alpha in

  let log : hashed_log li = log in
  let secretId = ApplicationSecretID asId in
  let c_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in

  let cts = HKDF.derive_secret h ams "c ap traffic" log in
  dbg ("application traffic secret[C]:   "^print_bytes cts);
  let sts = HKDF.derive_secret h ams "s ap traffic" log in
  dbg ("application traffic secret[S]:   "^print_bytes sts);
  let emsId : exportId li = ExportID asId log in
  let ems = HKDF.derive_secret h ams "exp master" log in
  dbg ("exporter master secret:          "^print_bytes ems);
  let exporter1 = (| li, emsId, ems |) in

  let (ck,civ) = keygen_13 h cts ae in
  dbg ("application key[C]:              "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("application key[S]:              "^print_bytes sk^", IV="^print_bytes siv);

  let id = ID13 (KeyID c_expandId) in
  assert_norm(peerId id = ID13 (KeyID s_expandId));
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StAE.coerce HS.root id (skv @| siv) in
  let ckv: StreamAE.key (peerId id) = ck in
  let civ: StreamAE.iv (peerId id)  = civ in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in

  st := S (S_13_wait_CF alpha cfk (| asId, ams |) (| li, c_expandId, (cts,sts) |));
  StAEInstance r w, exporter1

let ks_server_13_cf ks (log:bytes) : ST (li:logInfo & i:rmsId li & rms i)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_CF? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg ("ks_server_13_cf hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let S (S_13_wait_CF alpha cfk (| asId, ams |) rekey_info) = !st in
  let (ae, h) = alpha in

  // TODO loginfo CF
  let (| li, _, _ |) = rekey_info in
  let log : hashed_log li = log in
  let rmsId : rmsId li = RMSID asId log in

  let rms : rms rmsId = HKDF.derive_secret h ams "res master" log in
  dbg ("resumption master secret:        "^print_bytes rms);
  st := S (S_13_postHS alpha rekey_info);
  (| li, rmsId, rms |)

// Handshake must call this when ClientFinished goes into log
let ks_client_13_cf ks (log:bytes) : ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_CF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))
  =
  dbg ("ks_client_13_cf hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let C (C_13_wait_CF alpha cfk (| asId, ams |) rekey_info) = !st in
  let (ae, h) = alpha in

  // TODO loginfo CF
  let (| li, _, _ |) = rekey_info in
  let log : hashed_log li = log in
  let rmsId : rmsId li = RMSID asId log in

  let rms : rms rmsId = HKDF.derive_secret h ams "res master" log in
  dbg ("resumption master secret:        "^print_bytes rms);
  st := C (C_13_postHS alpha rekey_info (| li, rmsId, rms |))

// Generate a PSK out of the current RMS and incoming ticket nonce
// May be called several times if server sends multiple tickets
let ks_client_13_rms_psk ks (nonce:bytes) : ST (bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_postHS? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies_none h0 h1)
  =
  dbg "ks_client_13_rms";
  let KS #region st = ks in
  let C (C_13_postHS _ _ rmsi) = !st in
  let (| li, rmsId, rms |) = rmsi in
  dbg ("Recall RMS: "^(hex_of_bytes rms));
  HKDF.derive_secret (rmsId_hash rmsId) rms "resumption" nonce

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
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_client_12_full_dh ks sr pv cs ems (|g,gx|) =
  let KS #region st = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr
    | C (C_13_wait_SH cr _ _ ) -> cr in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let gy, pmsb = CommonDH.dh_responder g gx in
  let _ = print_share gx in
  let _ = print_share gy in
  dbg ("PMS: "^(print_bytes pmsb));
  let dhpmsId = PMS.DHPMS g gx gy (PMS.ConcreteDHPMS pmsb) in
  let ns =
    if ems then
      C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48ul in
      dbg ("master secret: "^(print_bytes ms));
      let msId = StandardMS dhpmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; gy

// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\
    (C_12_Full_CH? (C?.s st) \/ C_12_Resume_CH? (C?.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ HS.modifies_ref rid (Set.singleton (Heap.addr_of (as_ref st))) ( h0) ( h1))

let ks_client_12_full_rsa ks sr pv cs ems pk =
  let KS #region st = ks in
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
      let ms = TLSPRF.extract kef pmsb csr 48ul in
      let msId = StandardMS rsapmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; encrypted

val ks_client_12_set_session_hash: ks:ks -> h:bytes -> ST (TLSPRF.key * recordInstance)
  (requires fun h0 ->
    let st = sel h0 (KS?.state ks) in
    C? st /\ (C_12_wait_MS? (C?.s st) \/ C_12_has_MS? (C?.s st)))
  (ensures fun h0 r h1 ->
    let st = sel h1 (KS?.state ks) in
    modifies (Set.singleton (KS?.region ks)) h0 h1 /\
    C? st /\ (C_12_has_MS? (C?.s st))
    /\ HS.modifies_ref (KS?.region ks) (Set.singleton (Heap.addr_of (as_ref (KS?.state ks)))) ( h0) ( h1))

let ks_client_12_set_session_hash ks log =
  dbg ("ks_client_12_set_session_hash hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let ms =
    match !st with
    | C (C_12_has_MS csr alpha msId ms) ->
      dbg ("master secret:"^(print_bytes ms));
      ms
    | C (C_12_wait_MS csr alpha pmsId pms) ->
      let (pv, cs, ems) = alpha in
      let kef = kefAlg pv cs ems in
      let h = verifyDataHashAlg_of_ciphersuite cs in
      let msId, ms =
        if ems then
          begin
          let ms = TLSPRF.prf (pv,cs) pms (utf8_encode "extended master secret") log 48ul in
          dbg ("extended master secret:"^(print_bytes ms));
          let msId = ExtendedMS pmsId log kef in
          msId, ms
          end
        else
          begin
          let ms = TLSPRF.extract kef pms csr 48ul in
          dbg ("master secret:"^(print_bytes ms));
          let msId = StandardMS pmsId csr kef in
          msId, ms
          end
      in
      st := C (C_12_has_MS csr alpha msId ms);
      ms
    in
  let appk = ks_12_record_key ks in
  (TLSPRF.coerce ms, appk)

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

val getId: recordInstance -> GTot id
let getId (StAEInstance #i rd wr) = i

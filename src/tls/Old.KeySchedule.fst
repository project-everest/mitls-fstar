module Old.KeySchedule

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes
open FStar.Error
//open FStar.Integers 

open TLSError
open TLS.Callbacks
open TLSConstants
open Extensions
open TLSInfo
open Range
open StatefulLHAE
open HKDF
//open PSK

module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module H = Hashing.Spec

module HMAC_UFCMA = Old.HMAC.UFCMA

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

// PSK (internal/external multiplex, abstract)
// Note that application PSK is externally defined but should
// be idealized together with KS
abstract let psk (i:esId) =
  b:bytes{len b = Hacl.Hash.Definitions.hash_len (esId_hash i)}

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

type ks_info12 =
| Info12: pv:protocolVersion -> cs:cipherSuite -> ems:bool -> ks_info12
type ks_info13 =
| Info13: is_quic:bool -> ae:aeadAlg -> h:hash_alg -> ks_info13
 
/// 19-07-05 Notes towards verified state-passing refactoring: each of
///          these cases will become its own type (or possibly cover a
///          couple of cases within the same Handshake state),
///          parametrized by a single "main" key index and ad hoc
///          parts of the state determined by the Handshake messages
///          (such as nonces, public shares, and alpha)

type ks_client =
| C_wait_ServerHello:
  cr:random ->
  is_quic: bool ->
  esl: list (i:esId{~(NoPSK? i)} & es i) ->
  gs:list (g:CommonDH.group & CommonDH.ikeyshare g) ->
  ks_client

| C13_wait_Finished1:
  info:ks_info13 -> 
  (i:finishedId & cfk:fink i) -> 
  (i:finishedId & sfk:fink i) ->
  (i:asId & ams:ams i) ->
  ks_client

| C13_wait_Finished2:
  info: ks_info13 ->
  (i:finishedId & cfk:fink i) -> // still indexed by [..ServerHello] 
  (i:asId & ams:ams i) -> // indexed by [..Finished1] 
  (li:logInfo & i:rekeyId li & rekey_secrets i) ->
  ks_client

| C13_Complete: 
  info:ks_info13 -> 
  (li:logInfo & i:rekeyId li & rekey_secrets i) -> // indexed by [..Finished1] 
  (li:logInfo & i:rmsId li & rms i) -> // indexed by [..Finished2]
  ks_client

| C12_Full_CH: // To be removed
  cr:random ->
  ks_client

| C12_Resume_CH:
  cr:random ->
  si:sessionInfo ->
  msId:TLSInfo.msId ->
  ms:ms ->
  ks_client

| C12_wait_MS:
  csr:csRands ->
  info: ks_info12 ->
  id:TLSInfo.pmsId -> 
  pms:pms ->
  ks_client
  
| C12_has_MS:
  csr:csRands ->
  info:ks_info12 ->
  id:TLSInfo.msId ->
  ms:ms ->
  ks_client

type ks_server =
| S12_wait_CKE_DH:
  csr:csRands ->
  info:ks_info12 ->
  our_share: (g:CommonDH.group & CommonDH.ikeyshare g) ->
  ks_server

| S12_has_MS:
  csr:csRands ->
  info:ks_info12 ->
  id:TLSInfo.msId ->
  ms:ms ->
  ks_server

| S13_wait_SH:
  info:ks_info13 ->
  cr:random ->
  sr:random ->
  es:(i:esId & es i) ->
  hs:(i:hsId & hs i) ->
  ks_server

| S13_wait_SF:
  info:ks_info13 ->
  sfk:(i:finishedId & cfk:fink i) ->
  cfk:(i:finishedId & sfk:fink i) ->
  ams:(i:asId & ams:ams i) ->
  ks_server

| S13_wait_CF:
  info:ks_info13 ->
  cfk:(i:finishedId & cfk:fink i) ->
  ams:(i:asId & ams i) ->
  rk:(li:logInfo & i:rekeyId li & rekey_secrets i) ->
  ks_server

| S13_postHS:
  info:ks_info13 ->
  rki:(li:logInfo & i:rekeyId li & rekey_secrets i) ->
  rms:(li:logInfo & i:rmsId li & rms i) ->
  ks_server

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

private let group_of_valid_namedGroup
  (g:CommonDH.supportedNamedGroup)
  : CommonDH.group
  = Some?.v (CommonDH.group_of_namedGroup g)

effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)

val map_ST: ('a -> ST0 'b) -> list 'a -> ST0 (list 'b)
let rec map_ST f x = match x with
  | [] -> []
  | a::tl -> f a :: map_ST f tl

private let keygen (g:CommonDH.group)
  : St (g:CommonDH.group & CommonDH.ikeyshare g)
  = (| g, CommonDH.keygen g |)

val ks_client_init: 
  cr: random ->
  is_quic: bool ->
  ogl: option CommonDH.supportedNamedGroups -> 
  ST (ks_client * option keyShareClientHello)
  (requires fun h0 -> True)
  (ensures fun h0 (ks,ogxl) h1 -> 
    C_wait_ServerHello? ks /\
    h0 == h1 /\ 
    (None? ogl ==> None? ogxl) /\
    (Some? ogl ==> (Some? ogxl /\ Some?.v ogl == List.Tot.map tag_of_keyShareEntry (Some?.v ogxl))))

private
let serialize_share (gx:(g:CommonDH.group & CommonDH.ikeyshare g)) =
  let (| g, gx |) = gx in
  CommonDH.format #g (CommonDH.ipubshare gx)

private val map_ST_keygen: list CommonDH.group -> ST0 (list (g:CommonDH.group & CommonDH.ikeyshare g))
private let rec map_ST_keygen l =
  match l with
  | [] -> []
  | hd :: tl -> keygen hd :: map_ST_keygen tl

let ks_client_init cr is_quic ogl =
  dbg ("ks_client_init "^(if ogl=None then "1.2" else "1.3"));
  match ogl with
  | None -> // TLS 1.2
    C12_Full_CH cr, None
  | Some gl -> // TLS 1.3
    let groups = List.Tot.map group_of_valid_namedGroup gl in
    let gs = map_ST_keygen groups in
    let gxl = List.Tot.map serialize_share gs in
    C_wait_ServerHello cr is_quic [] gs, Some gxl
 
type ticket13 = t:Ticket.ticket{Ticket.Ticket13? t}
type bkey13 = psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t}
type binder_key = i:binderId & bk:binderKey i
type early_secret = i:esId{~(NoPSK? i)} & es i

private let mk_binder (bk:bkey13)
  : ST (binder_key * early_secret)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let (pskid,t) = bk in 
  let i : esId = ResumptionPSK (Ticket.Ticket13?.rmsId t) in
  let pski = Some?.v (Ticket.ticket_pskinfo t) in
  let psk = Ticket.Ticket13?.rms t in
  let CipherSuite13 _ h = pski.early_cs in
  dbg ("Loaded pre-shared key "^(print_bytes pskid)^": "^(print_bytes psk));
  let es : es i = HKDF.extract #h (H.zeroHash h) psk in
  dbg ("Early secret: "^(print_bytes es));
  let ll, lb =
    if ApplicationPSK? i then ExtBinder, "ext binder"
    else ResBinder, "res binder" in
  let bId = Binder i ll in
  let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
  dbg ("Binder key["^lb^"]: "^(print_bytes bk));
  let bk = finished_13 h bk in
  dbg ("Binder Finished key: "^(print_bytes bk));
  let bk : binderKey bId = HMAC_UFCMA.coerce (HMAC_UFCMA.HMAC_Binder bId) trivial HS.root bk in
  (| bId, bk|), (| i, es |)

private let rec tickets13 acc (l:list bkey13)
  : ST0 (list (binder_key * early_secret))
  = match l with
  | [] -> List.Tot.rev acc
  | bk :: r -> tickets13 ((mk_binder bk)::acc) r

// Called from TLS.Handshake.Client, updates both the list 
// of early secrets and computes the binder keys
let ks_client13_get_binder_keys (s:ks_client) (l:list bkey13)
  : ST (ks_client * list binder_key)
  (requires fun h0 -> C_wait_ServerHello? s /\ C_wait_ServerHello?.esl s == [])
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ C_wait_ServerHello? s
    /\ List.Tot.length (C_wait_ServerHello?.esl s') == List.Tot.length l)
  =
  let C_wait_ServerHello cr is_quic [] gs = s in
  let (bkl, esl) = List.Tot.split (tickets13 [] l) in
  (C_wait_ServerHello cr is_quic esl gs), bkl

let ks_client13_hello_retry 
  (ks0:ks_client{ C_wait_ServerHello? ks0 }) (g:CommonDH.group)
  : ST0 (CommonDH.share g * ks1:ks_client{ C_wait_ServerHello? ks1}) =
  let C_wait_ServerHello cr is_quic esl gs = ks0 in
  let s : CommonDH.ikeyshare g = CommonDH.keygen g in
  let ks1 = C_wait_ServerHello cr is_quic esl [(| g, s |)] in
  CommonDH.ipubshare #g s, ks1

/// Derive the early data key from the first offered PSK
/// Only called if 0-RTT is enabled on the client
let ks_client13_ch client_state (log:bytes)
  : ST (exportKey * recordInstance)
  (requires fun h0 -> C_wait_ServerHello? client_state
    /\ C_wait_ServerHello?.esl client_state <> [])
  (ensures fun h0 r h1 -> modifies_none h0 h1)
  =
  dbg ("ks_client13_ch log="^print_bytes log);
  let C_wait_ServerHello cr is_quic ((| i, es |) :: _) gs = client_state in
  let h = esId_hash i in
  let ae = esId_ae i in
  let li = LogInfo_CH0 ({
   li_ch0_cr = cr;
   li_ch0_ed_ae = ae;
   li_ch0_ed_hash = h;
   li_ch0_ed_psk = PSK.coerce empty_bytes; }) in

  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID i) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret:     "^print_bytes ets);
  let expId : exportId li = EarlyExportID i log in
  let early_export : ems expId = HKDF.derive_secret h es "e exp master" log in
  dbg ("Early exporter master secret:    "^print_bytes early_export);
  let exporter0 = (| li, expId, early_export |) in

  // Expand all keys from the derived early secret
  let (ck, civ, pn) = keygen_13 h ets ae is_quic in
  dbg ("Client 0-RTT key:                "^print_bytes ck^", IV="^print_bytes civ);

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in
  let early_d = StAEInstance r rw (pn, pn) in
  exporter0, early_d

val ks_server12_init_dh: sr:random -> cr:random ->
  pv:protocolVersion -> cs:cipherSuite -> ems:bool ->
  g:CommonDH.group ->
  ST (CommonDH.share g * ks_server)
  (requires fun h0 -> CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
      (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 (gx,s) h1 -> S12_wait_CKE_DH? s)

let ks_server12_init_dh sr cr pv cs ems g =
  dbg "ks_server12_init_dh";
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen g in
  let _ = print_share (CommonDH.ipubshare our_share) in
  let info = Info12 pv cs ems in
  let csr = cr @| sr in
  let st = S12_wait_CKE_DH csr info (| g, our_share |) in
  CommonDH.ipubshare our_share, st

val ks_server13_init:
  sr:random ->
  cr:random ->
  cs:cipherSuite ->
  is_quic:bool ->
  pskid:option bkey13 ->
  g_gx:option (g:CommonDH.group & CommonDH.share g) ->
  ST (ks_server *
      option (g:CommonDH.group & CommonDH.share g) *
      option (i:binderId & binderKey i))
  (requires fun h0 -> (Some? g_gx \/ Some? pskid)
    /\ (Some? g_gx ==> Some? (CommonDH.namedGroup_of_group (dfst (Some?.v g_gx))))
    /\ CipherSuite13? cs)
  (ensures fun h0 (ks', gy, bk) h1 ->
    modifies_none h0 h1
    /\ (Some? bk <==> Some? pskid)
    /\ (Some? gy \/ Some? bk)
    /\ S13_wait_SH? ks')

let ks_server13_init sr cr cs is_quic pskid g_gx =
  dbg ("ks_server_init");
  let CipherSuite13 ae h = cs in
  let info = Info13 is_quic ae h in
  let (| esId, es |), bk =
    match pskid with
    | Some (id, Ticket.Ticket13 cs li rmsId rms _ _ _ _) ->
      dbg ("Using negotiated PSK identity: "^(print_bytes id));
      dbg ("Ticket RMS: "^(print_bytes rms));
      let i = ResumptionPSK #li rmsId in
      let CipherSuite13 _ h = cs in
      let nonce, _ = split id 12ul in
      let psk = HKDF.derive_secret h rms "resumption" nonce in
      dbg ("Pre-shared key: "^(print_bytes psk));
      let es: es i = HKDF.extract #h (H.zeroHash h) psk in
      let ll, lb =
        if ApplicationPSK? i then ExtBinder, "ext binder"
        else ResBinder, "res binder" in
      let bId: pre_binderId = Binder i ll in
      let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
      dbg ("binder key:                      "^print_bytes bk);
      let bk = finished_13 h bk in
      dbg ("binder Finished key:             "^print_bytes bk);
      let bk : binderKey bId = HMAC_UFCMA.coerce
        (HMAC_UFCMA.HMAC_Binder bId) (fun _ -> True) Mem.tls_region bk in
      (| i, es |), Some (| bId, bk |)
    | None ->
      dbg "No PSK selected.";
      let esId = NoPSK h in
      let es : es esId = HKDF.extract #h (H.zeroHash h) (H.zeroHash h) in
      (| esId, es |), None
    in
  dbg ("Computed early secret:           "^print_bytes es);
  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("Handshake salt:                  "^print_bytes salt);
  let gy, (hsId: pre_hsId), (hs: Hashing.Spec.tag h) =
    match g_gx with
    | Some (| g, gx |) ->
      let gy, gxy = CommonDH.dh_responder g gx in
      dbg ("DH shared secret: "^(print_bytes gxy));
      let hsId = HSID_DHE saltId g gx gy in
      let hs : hs hsId = HKDF.extract #h salt gxy in
      Some (| g, gy |), hsId, hs
    | None ->
      let hsId = HSID_PSK saltId in
      let hs : hs hsId = HKDF.extract #h salt (H.zeroHash h) in
      None, hsId, hs
    in
  dbg ("Handshake secret:                "^print_bytes hs);
  let ks' = (S13_wait_SH info cr sr (| esId, es |) (| hsId, hs |)) in
  ks', gy, bk

let ks_server13_0rtt_key (s:ks_server) (log:bytes)
  : ST ((li:logInfo & i:exportId li & ems i) * recordInstance)
  (requires fun h0 -> S13_wait_SH? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  dbg "ks_server13_0rtt_key";
  let S13_wait_SH (Info13 is_quic ae h) cr sr (| esId, es |) _ = s in
  let li = LogInfo_CH0 ({
    li_ch0_cr = cr;
    li_ch0_ed_ae = ae;
    li_ch0_ed_hash = h;
    li_ch0_ed_psk = PSK.coerce empty_bytes;
  }) in
  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID esId) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret:     "^print_bytes ets);
  let expId : exportId li = EarlyExportID esId log in
  let early_export : ems expId = HKDF.derive_secret h es "e exp master" log in
  dbg ("Early exporter master secret:    "^print_bytes early_export);

  // Expand all keys from the derived early secret
  let (ck, civ, pn) = keygen_13 h ets ae is_quic in
  dbg ("Client 0-RTT key:                "^print_bytes ck^", IV="^print_bytes civ);

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HS.root id (ckv @| civ) in
  let r = StAE.genReader HS.root rw in
  let early_d = StAEInstance r rw (pn, pn) in
  (| li, expId, early_export |), early_d

val ks_server13_sh: s:ks_server -> log:bytes ->
  ST (ks_server * recordInstance)
  (requires fun h0 -> S13_wait_SH? s)
  (ensures fun h0 (s', _) h1 -> modifies_none h0 h1
    /\ S13_wait_SF? s')

let ks_server13_sh s log =
  dbg ("ks_server13_sh, hashed log = "^print_bytes log);
  let S13_wait_SH info cr sr _ (| hsId, hs |) = s in
  let Info13 is_quic ae h = info in
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
  let (ck, civ, cpn) = keygen_13 h cts ae is_quic in
  dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  let (sk, siv, spn) = keygen_13 h sts ae is_quic in
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

  let cfk1 : fink cfkId = HMAC_UFCMA.coerce
    (HMAC_UFCMA.HMAC_Finished cfkId) (fun _ -> True) HS.root cfk1 in
  let sfk1 : fink sfkId = HMAC_UFCMA.coerce
    (HMAC_UFCMA.HMAC_Finished sfkId) (fun _ -> True) HS.root sfk1 in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  dbg ("Application salt:                "^print_bytes salt);

  // Replace handshake secret with application master secret
  let amsId = ASID saltId in
  let ams : ams amsId = HKDF.extract #h salt (H.zeroHash h) in
  dbg ("Application secret:              "^print_bytes ams);

  let s' = S13_wait_SF info (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| amsId, ams |) in
  s', StAEInstance r w (cpn, spn) 

let ks_server13_get_sfk (S13_wait_SF _ _ sfk _) = sfk
let ks_server13_get_cfk (S13_wait_CF _ cfk _ _) = cfk

let ks_client12_finished_key (C12_has_MS _ _ _ ms) = TLSPRF.coerce ms
let ks_server12_finished_key (S12_has_MS _ _ _ ms) = TLSPRF.coerce ms

let ks_client12_ms (C12_has_MS _ _ msId ms) = (msId, ms)
let ks_server12_ms (S12_has_MS _ _ msId ms) = (msId, ms)

private let ks12_record_key role csr info msId ms
  : St recordInstance =
  dbg "ks12_record_key";
  let cr, sr = split csr 32ul in
  let Info12 pv cs ems = info in
  let kdf = kdfAlg pv cs in
  let ae = get_aeAlg cs in
  let id = ID12 pv msId kdf ae cr sr role in
  let AEAD alg _ = ae in (* 16-10-18 FIXME! only correct for AEAD *)
  let klen = EverCrypt.aead_keyLen alg in
  let slen = UInt32.uint_to_t (AEADProvider.salt_length id) in
  let expand = TLSPRF.kdf kdf ms (sr @| cr) FStar.Integers.(klen + klen + slen + slen) in
  dbg ("keystring (CK, CIV, SK, SIV) = "^(print_bytes expand));
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
  StAEInstance r w (None, None)

let ks12_client_key (s:ks_client)
  : ST recordInstance
  (requires fun h0 -> C12_has_MS? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let C12_has_MS csr info msId ms = s in
  ks12_record_key Client csr info msId ms

let ks12_server_key (s:ks_server)
  : ST recordInstance
  (requires fun h0 -> S12_has_MS? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let S12_has_MS csr info msId ms = s in
  ks12_record_key Server csr info msId ms

let ks_client12_resume (s:ks_client) (sr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (msId:TLSInfo.msId) (ms:bytes)
  : ST ks_client
  (requires fun h0 -> (C12_Full_CH? s \/ C_wait_ServerHello? s))
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C12_has_MS? s')
  =
  dbg "ks_client12_resume";
  let cr = match s with
    | C12_Full_CH cr -> cr
    | C_wait_ServerHello cr _ _ _ -> cr in
  let csr = cr @| sr in
  let info = Info12 pv cs ems in
  dbg ("Recall MS: "^(print_bytes ms));
  C12_has_MS csr info msId ms

let ks_server12_resume (sr:random) (cr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (msId:msId) (ms:bytes)
  : ST ks_server
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> modifies_none h0 h1
    /\ S12_has_MS? s)
  =
  dbg ("ks_server12_resume MS: "^(print_bytes ms));
  let csr = cr @| sr in
  let info = Info12 pv cs ems in
  S12_has_MS csr info msId ms

val ks_server12_cke_dh: s:ks_server ->
  gy:(g:CommonDH.group & CommonDH.share g) ->
  log:bytes ->
  ST ks_server
  (requires fun h0 -> S12_wait_CKE_DH? s /\
    (let S12_wait_CKE_DH _ _ (| g', _ |) = s in
    g' = dfst gy)) // Responder share must be over the same group as initiator's
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ S12_has_MS? s')

let ks_server12_cke_dh s gy hashed_log =
  dbg "ks_server12_cke_dh";
  let S12_wait_CKE_DH csr alpha (| g, gx |) = s in
  let Info12 pv cs ems = alpha in
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
  S12_has_MS csr alpha msId ms

private let group_matches (g:CommonDH.group)
  (gx:(x:CommonDH.group & CommonDH.ikeyshare g)) =
  g = dfst gx

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

val ks_client13_sh: Mem.rgn -> ks:ks_client ->
  sr:random -> cs:cipherSuite ->
  h:bytes -> // [..ServerHello]
  gy:option (g:CommonDH.group & CommonDH.share g) ->
  accept_psk:option UInt16.t ->
  ST (ks_client * recordInstance)
  (requires fun h0 ->
    match ks with 
    | C_wait_ServerHello _ _ ei gc ->
      // Ensure that the PSK accepted is one offered
     (match gy with
     | Some (| g, _ |) -> List.Tot.existsb (fun gx -> g = dfst gx) gc
     | None -> True)
     /\
     (match ei, accept_psk with
      | [], None -> True
      | _::_ , Some n -> UInt16.v n < List.Tot.length ei
      | _ -> False)
    | _ -> False )  
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ C13_wait_Finished1? s')

let ks_client13_sh region ks sr cs log gy accept_psk =
  dbg ("ks_client13_sh hashed_log = "^print_bytes log);
  let C_wait_ServerHello cr is_quic esl gc = ks in
  let CipherSuite13 ae h = cs in
  let info = Info13 is_quic ae h in
  
  // Early secret: must derive zero here as hash is not known before
  let (| esId, es |): (i: esId & es i) =
    match esl, accept_psk with
    | l, Some n ->
      let Some (| i, es |) : option (i:esId & es i) = List.Tot.nth l (UInt16.v n) in
      dbg ("recallPSK early secret:          "^print_bytes es);
      (| i, es |)
    | _, None ->
      let es = HKDF.extract #h (H.zeroHash h) (H.zeroHash h) in
      dbg ("no PSK negotiated. Early secret: "^print_bytes es);
      (| NoPSK h, es |)
  in

  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("handshake salt:                  "^print_bytes salt);

  let (| hsId, hs |): (hsId: pre_hsId & hs: hs hsId) =
    match gy with
    | Some (| g, gy |) -> (* (PSK-)DHE *)
      let Some (| _, gx |) = List.Helpers.find_aux g group_matches gc in
      let gxy = CommonDH.dh_initiator g gx gy in
      dbg ("DH shared secret: "^(print_bytes gxy));
      let hsId = HSID_DHE saltId g (CommonDH.ipubshare gx) gy in
      let hs : hs hsId = HKDF.extract #h salt gxy in
      (| hsId, hs |)
    | None -> (* Pure PSK *)
      let hsId = HSID_PSK saltId in
      let hs : hs hsId = HKDF.extract #h salt (H.zeroHash h) in
      (| hsId, hs |)
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
  let (ck, civ, cpn) = keygen_13 h cts ae is_quic in
  dbg ("handshake key[C]:                "^print_bytes ck^", IV="^print_bytes civ);
  let (sk, siv, spn) = keygen_13 h sts ae is_quic in
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
  let ams : ams asId = HKDF.extract #h salt (H.zeroHash h) in
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
  let s'= C13_wait_Finished1 info (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| asId, ams |) in
  s', StAEInstance r w (spn, cpn)

let ks_client13_sf (s:ks_client) (log:bytes) // [..Finished1]
  : ST (ks_client * ((i:finishedId & sfk:fink i) * (i:finishedId & cfk:fink i) * recordInstance * exportKey))
  (requires fun h0 -> C13_wait_Finished1? s)
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ C13_wait_Finished2? s')
  =
  dbg ("ks_client13_sf hashed_log = "^print_bytes log);
  let C13_wait_Finished1 info cfk sfk (| asId, ams |) = s in
  let Info13 is_quic ae h = info in

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

  let (ck,civ,cpn) = keygen_13 h cts ae is_quic in
  dbg ("application key[C]:              "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv,spn) = keygen_13 h sts ae is_quic in
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

  C13_wait_Finished2 info cfk (| asId, ams |) (| li, c_expandId, (cts,sts)|),
  (sfk, cfk, StAEInstance r w (spn, cpn), exporter1)

let ks_server13_sf (s:ks_server) (log:bytes) // [..Finished1]
  : ST (ks_server * recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 -> S13_wait_SF? s)
  (ensures fun h0 (s',_,_) h1 -> modifies_none h0 h1
    /\ S13_wait_CF? s')
  =
  dbg ("ks_server13_sf hashed_log = "^print_bytes log);
  let S13_wait_SF info cfk _ (| asId, ams |) = s in
  let FinishedID #li _ = dfst cfk in // TODO loginfo
  let Info13 is_quic ae h = info in

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

  let (ck,civ,cpn) = keygen_13 h cts ae is_quic in
  dbg ("application key[C]:              "^print_bytes ck^", IV="^print_bytes civ);
  let (sk,siv,spn) = keygen_13 h sts ae is_quic in
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

  let s' = S13_wait_CF info cfk (| asId, ams |) (| li, c_expandId, (cts,sts) |) in
  s', StAEInstance r w (cpn, spn), exporter1

let ks_server13_cf (s:ks_server) (log:bytes)
  : ST ks_server
  (requires fun h0 -> S13_wait_CF? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ S13_postHS? s')
  =
  dbg ("ks_server13_cf hashed_log = "^(print_bytes log));
  let S13_wait_CF info cfk (| asId, ams |) rekey_info = s in
  let Info13 is_quic ae h = info in
  let (| li, _, _ |) = rekey_info in
  let log : hashed_log li = log in
  let rmsId : rmsId li = RMSID asId log in
  let rms : rms rmsId = HKDF.derive_secret h ams "res master" log in
  dbg ("resumption master secret:        "^print_bytes rms);
  S13_postHS info rekey_info (| li, rmsId, rms |)

let ks_server13_rms (S13_postHS _ _ rms) = rms

let ks_client13_cf (s:ks_client) (log:bytes)
  : ST ks_client
  (requires fun h0 -> C13_wait_Finished2? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C13_Complete? s')
  =
  dbg ("ks_client13_cf hashed_log = "^print_bytes log);
  let C13_wait_Finished2 info cfk (| asId, ams |) rekey_info = s in
  let Info13 is_quic ae h = info in

  let (| li, _, _ |) = rekey_info in
  let log : hashed_log li = log in
  let rmsId : rmsId li = RMSID asId log in

  let rms : rms rmsId = HKDF.derive_secret h ams "res master" log in
  dbg ("resumption master secret:        "^print_bytes rms);
  C13_Complete info rekey_info (| li, rmsId, rms |)

// Generate a PSK out of the current RMS and incoming ticket nonce
// May be called several times if server sends multiple tickets
let ks_client13_rms_psk (s:ks_client) (nonce:bytes)
  : ST bytes
  (requires fun h0 -> C13_Complete? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  dbg "ks_client13_rms";
  let C13_Complete _ _ rmsi = s in
  let (| li, rmsId, rms |) = rmsi in
  dbg ("Recall RMS: "^hex_of_bytes rms);
  HKDF.derive_secret (rmsId_hash rmsId) rms "resumption" nonce

let ks_client12_full_dh (s:ks_client) (sr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (g_gx:(g:CommonDH.group & CommonDH.share g))
  : ST (ks_client * CommonDH.share (dfst g_gx))
  (requires fun h0 ->
    C12_Full_CH? s \/ C12_Resume_CH? s \/ C_wait_ServerHello? s)
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ (if ems then C12_wait_MS? s' else C12_has_MS? s'))
  =
  let (| g, gx |) = g_gx in
  let cr = match s with
    | C12_Full_CH cr -> cr
    | C12_Resume_CH cr _ _ _ -> cr
    | C_wait_ServerHello cr _ _ _ -> cr in
  let csr = cr @| sr in
  let info = Info12 pv cs ems in
  let gy, pmsb = CommonDH.dh_responder g gx in
  let _ = print_share gx in
  let _ = print_share gy in
  dbg ("PMS: "^(print_bytes pmsb));
  let dhpmsId = PMS.DHPMS g gx gy (PMS.ConcreteDHPMS pmsb) in
  let s' =
    if ems then
      C12_wait_MS csr info dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48ul in
      dbg ("master secret: "^(print_bytes ms));
      let msId = StandardMS dhpmsId csr kef in
      C12_has_MS csr info msId ms in
  s', gy

(* Disabling RSA - support is removed in EverCrypt
let ks_client12_full_rsa (s:ks_client) (sr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (pk:RSAKey.pk)
  : ST (ks_client * bytes)
  (requires fun h0 -> C12_Full_CH? s \/ C12_Resume_CH? s)
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ (if ems then C12_wait_MS? s' else C12_has_MS? s'))
  =
  let info = Info12 pv cs ems in
  let cr = match s with
    | C12_Full_CH cr -> cr
    | C12_Resume_CH cr _ _ _ -> cr in
  let csr = cr @| sr in
  let rsapms = PMS.genRSA pk pv in
  let pmsb = PMS.leakRSA pk pv rsapms in
  //CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 pmsb in
  let encrypted = Random.sample 256 in
  let rsapmsId = PMS.RSAPMS(pk, pv, rsapms) in
  let s' =
    if ems then
      C12_wait_MS csr info rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48ul in
      let msId = StandardMS rsapmsId csr kef in
      C12_has_MS csr info msId ms in
  s', encrypted
*)

let ks_client12_set_session_hash (s:ks_client) (log:bytes)
  : ST (ks_client)
  (requires fun h0 -> C12_wait_MS? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C12_has_MS? s')
  =
  dbg ("ks_client12_set_session_hash hashed_log = "^(print_bytes log));
  let C12_wait_MS csr info pmsId pms = s in
  let Info12 pv cs ems = info in
  let kef = kefAlg pv cs ems in
  let h = verifyDataHashAlg_of_ciphersuite cs in
  let msId, ms =
    if ems then (
      let ms = TLSPRF.prf (pv,cs) pms (utf8_encode "extended master secret") log 48ul in
      dbg ("extended master secret:"^(print_bytes ms));
      let msId = ExtendedMS pmsId log kef in
      msId, ms
    ) else (
      let ms = TLSPRF.extract kef pms csr 48ul in
      dbg ("master secret:"^(print_bytes ms));
      let msId = StandardMS pmsId csr kef in
      msId, ms
    ) in
  C12_has_MS csr info msId ms

// Used by Epochs to read index of recordInstance
val getId: recordInstance -> GTot id
let getId (StAEInstance #i _ _ _) = i

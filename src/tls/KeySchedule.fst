module KeySchedule
(*the top level key schedule module, it should not expose secrets to Handshake *)

(* the goal is to keep ephemerals like eph_s and eph_c as currently defined 
   in Handshake local *)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties
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
open HSCrypto

// KEF.fst/TLSPRF.fst for TLS 1.2
// CoreCrypto.hkdf for TLS 1.3

// does NOT subsumes the idealized module PRF.fst
// (we do not solve the circular dependency properly)


// LONG TERM GLOBAL SECRETS
// ******************************************

// For now, we stick to the style of miTLS 0.9
// to avoid a circular dependency between KEF and StatefulLHAE

// PRF (type pms) -> TLSInfo (type id) -> KEF (extract pms)
//                     \ StatefulLHAE (coerce id) / 

// Morally, we would like the following types to be
// abstract, but they must be concrete in order for the definition
// of id to appear in StatefulLHAE.

//abstract type ms = b:bytes{length b == 48}
type ms = bytes
type pms = bytes 

// type pms =
// | DH_PMS of CommonDH.dhpms // concrete
// | RSA_PMS of RSAKey.rsapms // concrete

// Index type for keys; it is morally abstract in
// StatefulLHAE (but has functions safeId: id->bool,
// algId: id -> aeAlg) and its concrete definition may
// be used to prove that StatefulLHAE.gen is not called
// twice with the same id
//type id = TLSInfo.id

// (in TLSInfo.fst)
// type id = {
//  msId   : msId;            // the index of the master secret used for key derivation
//  kdfAlg : kdfAlg_t;          // the KDF algorithm used for key derivation
//  pv     : protocolVersion; // should be part of aeAlg
//  aeAlg  : aeAlg;           // the authenticated-encryption algorithms
//  csrConn: csRands;         // the client-server random of the connection
//  ext: negotiatedExtensions;// the extensions negotiated for the current session
//  writer : role             // the role of the writer
//  }

// abstract type resumption_secret = b:bytes{}
//type resumption_secret = b:bytes{}

//type exporter_secret = b:bytes{}

// abstract type pre_share_key = b:bytes{}
//type pre_shared_key = PSK.psk


// Agility parameters, extend as needed
// may be moved to TLSInfo for joint idealization with Handshake
type ks_alpha12 = pv:protocolVersion * cs:cipherSuite * ems:bool
type ks_alpha13 = ae:aeadAlg * h:CoreCrypto.hash_alg

// Internal KS state, now with ad-hoc parameters
type ks_client_state =
| C_Init
| C_12_Resume_CH: cr:random -> si:sessionInfo -> msId:TLSInfo.msId -> ms:ms -> ks_client_state
| C_12_Full_CH: cr:random -> ks_client_state
| C_12_wait_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.pmsId -> pms:pms -> ks_client_state
| C_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_client_state
| C_13_1RTT_CH: cr:random -> gs:list (namedGroup * CommonDH.key) -> ks_client_state
| C_13_1RTT_HTK: alpha:ks_alpha13 -> id:TLSInfo.msId -> xES:ms -> ks_client_state
| C_13_TS: alpha:ks_alpha13 -> cfk:bytes -> atk0:bytes -> ks_client_state
| C_Done

type ks_server_state =
| S_Init
| S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha12 -> our_share:CommonDH.key -> ks_server_state
| S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha12 -> ks_server_state
| S_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_server_state
| S_13_1RTT_wait_HTK: alpha:ks_alpha13 -> id:TLSInfo.msId -> xES:ms -> ks_server_state
| S_13_TS: alpha:ks_alpha13 -> cfk:bytes -> atk0:bytes -> ks_server_state
| S_Done

// Reflecting state separation from HS
type ks_state =
| C: s:ks_client_state -> ks_state
| S: s:ks_server_state -> ks_state

type ks =
| KS: #region:rid -> state:rref region ks_state -> ks

type recordInstance =
| StAEInstance: #id:StreamAE.id -> StreamAE.reader id -> StreamAE.writer id -> recordInstance
| StLHAEInstance: #id:StatefulLHAE.id -> StatefulLHAE.reader id -> StatefulLHAE.writer id -> recordInstance

// TODO replace constants (16, 12) with aeadAlg-derived values
private let expand_13 (h:CoreCrypto.hash_alg) (secret:bytes) (phase:string) (context:bytes) =
  let cekb = HSCrypto.hkdf_expand_label h
             secret (phase ^ ", client write key") context 16 in
  let civb = HSCrypto.hkdf_expand_label h
             secret (phase ^ ", client write iv") context 12 in
  let sekb = HSCrypto.hkdf_expand_label h
             secret (phase ^ ", server write key") context 16 in
  let sivb = HSCrypto.hkdf_expand_label h
             secret (phase ^ ", server write iv") context 12 in
  (cekb,civb,sekb,sivb)

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> role -> ST ks
  (requires fun h -> rid<>root)
  (ensures fun h0 r h1 ->
    let KS #ks_region state = r in
    fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref state} h0 h1)

let create #rid r =
  ST.recall_region rid;
  let ks_region = new_region rid in 
  let istate = match r with | Client -> C C_Init | Server -> S S_Init in
  KS #ks_region (ralloc ks_region istate)

val ks_client_13_init_1rtt: ks:ks -> list (g:namedGroup{is_SEC g \/ is_FFDHE g}) -> ST (random * (list (namedGroup * bytes)))
  (requires fun h0 -> sel h0 (KS.state ks) = C C_Init)
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_init_1rtt ks groups =
  let KS #rid st = ks in
  let cr = Nonce.mkHelloRandom Client rid in
  let kg x = x, (match x with
    | SEC ecg -> CommonDH.keygen (CommonDH.ECDH ecg)
    | FFDHE g -> CommonDH.keygen (CommonDH.FFDH (DHGroup.Named g))) in
  let gs = List.Tot.map kg groups in
  st := C (C_13_1RTT_CH cr gs);
  let pub (x,y) = x, CommonDH.serialize y in
  (cr, List.Tot.map pub gs)

// Called before sending client hello
// (the external style of resumption may become internal to protect ms abstraction)
val ks_client_init_12: ks:ks -> ST (random * option sessionInfo)
  (requires fun h0 -> sel h0 (KS.state ks) = C C_Init)
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

// TODO resumption support
let ks_client_init_12 ks =
  let cr = Nonce.mkHelloRandom Client ks.region in
  let osi, ns = None, (C (C_12_Full_CH cr)) in
//    match cfg.resuming with
//    | None -> None, (KS_C_12_Full_CH cr)
//    | Some shard ->
//      (match DB.lookup shard with TODO
//      | Some (si, msId, ms) -> (Some si), (KS_C_12_Resume_CH cr si msId ms)
//      | None -> None, (KS_C_12_Full_CH cr)) in
  (KS.state ks) := ns;
  cr, osi

val ks_server_12_init_dh: ks:ks -> cr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> group:namedGroup -> ST (random * bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss)
    /\ is_CipherSuite cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_init_dh ks cr pv cs ems group =
  let KS #region st = ks in
  let group = (match group with 
      	       | SEC c -> CommonDH.ECDH c
	       | FFDHE f -> CommonDH.FFDH (DHGroup.Named f)) in
  let sr = Nonce.mkHelloRandom Server region in
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen group in
  let csr = cr @| sr in
  st := S (S_12_wait_CKE_DH csr (pv, cs, ems) our_share);
  (sr, CommonDH.serialize our_share)

val ks_server_13_1rtt_init: ks:ks -> cr:random -> cs:cipherSuite -> gn:namedGroup -> gxb:bytes -> ST (random * bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_Init (S.s kss)
    /\ is_CipherSuite cs
    /\ (let CipherSuite kex _ _ = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_1rtt_init ks cr cs gn gxb =
  let KS #region st = ks in
  let SEC ec = gn in
  let Some gx = CommonDH.parse (CommonDH.ECP (ECGroup.params_of_group ec)) gxb in
  let sr = Nonce.mkHelloRandom Server region in
  let CipherSuite _ _ (AEAD ae h) = cs in
  let our_share, gxy = CommonDH.dh_responder gx in
  let zeroes = Platform.Bytes.abytes (String.make 32 (Char.char_of_int 0)) in
  let msId = noMsId in
  let xES = HSCrypto.hkdf_extract h zeroes gxy in
  st := S (S_13_1RTT_wait_HTK (ae, h) msId xES);
  (sr, CommonDH.serialize our_share)

val ks_server_13_get_htk: ks:ks -> log_hash:bytes -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_1RTT_wait_HTK (S.s kss))
  (ensures fun h0 r h1 -> h0 = h1)

let ks_server_13_get_htk ks log_hash =
  let KS #region st = ks in
  let S (S_13_1RTT_wait_HTK (ae, h) msId xES) = !st in
  let (ck,civ,sk,siv) = expand_13 h xES "handshake key expansion" log_hash in
  // TODO fix the broken index of StreamAE
  let id = {
    msId = msId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Server
  } in
  assume (~ (authId id));
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StreamAE.coerce HyperHeap.root id skv siv in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  StAEInstance r w

// log is the raw HS log, used for EMS derivation
val ks_server_12_cke_dh: ks:ks -> peer_share:CommonDH.key -> log:bytes -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_12_wait_CKE_DH (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_cke_dh ks peer_share log =
  let KS #region st = ks in
  let S (S_12_wait_CKE_DH csr alpha our_share) = !st in
  let (pv, cs, ems) = alpha in
  let pmsb = CommonDH.dh_initiator our_share peer_share in
  let dhp = CommonDH.key_params our_share in
  let pms = PMS.DHPMS(dhp, our_share, peer_share, PMS.ConcreteDHPMS(pmsb)) in
  let pmsId = TLSInfo.SomePmsId(pms) in
  let kef = kefAlg pv cs ems in
  let msId, ms =
    if ems then
      let ms = TLSPRF.prf_hashed (pv,cs) pmsb (utf8 "extended master secret") log 48 in
      let msId = ExtendedMS pmsId log kef in
      (msId, ms)
    else
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS pmsId csr kef in
      (msId, ms) in
   st := S (S_12_has_MS csr alpha msId ms)

// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val ks_client_12_resume: ks:ks -> random -> pv:protocolVersion -> cs:cipherSuite -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_12_Resume_CH (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_resume ks sr pv cs =
  let KS #region st = ks in
  let C (C_12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extensions.ne_extended_ms in
  st := C (C_12_has_MS csr (pv, cs, ems) msId ms)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

val ks_client_13_1rtt: ks:ks -> cs:cipherSuite -> gy:(namedGroup * bytes) -> log_hash:bytes -> ST recordInstance
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_1RTT_CH (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_1rtt ks cs (gs, gyb) log_hash =
  let KS #region st = ks in
  let C (C_13_1RTT_CH cr gc) = !st in
  let Some (_, gx) = List.Tot.find (fun (gc,_) -> gc=gs) gc in
  let Some gy = CommonDH.parse (CommonDH.key_params gx) gyb in
  let gxy = CommonDH.dh_initiator gx gy in
  let CipherSuite _ _ (AEAD ae h) = cs in
  let zeroes = Platform.Bytes.abytes (String.make 32 (Char.char_of_int 0)) in
  let msId = noMsId in
  let xES = HSCrypto.hkdf_extract h zeroes gxy in
  let (ck,civ,sk,siv) = expand_13 h xES "handshake key expansion" log_hash in
  // TODO fix the broken index of StreamAE
  let id = {
    msId = msId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Client
  } in
  assume (~ (authId id));
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StreamAE.coerce HyperHeap.root id ckv civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let rw = StreamAE.coerce HyperHeap.root id skv siv in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := C (C_13_1RTT_HTK (ae, h) msId xES);
  StAEInstance r w

// Old KS: ms, cfk, sfk is up to CertificateVerify
// application keys use atk with context up to server finished
val ks_client_13_1rtt_server_finished: ks:ks -> log_hash:bytes -> ST (svd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_1RTT_HTK (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_1rtt_server_finished ks log_hash =
  let KS #region st = ks in
  let C (C_13_1RTT_HTK alpha msId xES) = !st in
  let (ae, h) = alpha in
  let mSS = HSCrypto.hkdf_expand_label h xES "expanded static secret" log_hash 32 in
  let mES = HSCrypto.hkdf_expand_label h xES "expanded ephemeral secret" log_hash 32 in
  let ms = HSCrypto.hkdf_extract h mSS mES in

  let cfk = HSCrypto.hkdf_expand_label h ms "client finished" empty_bytes 32 in
  let sfk = HSCrypto.hkdf_expand_label h ms "server finished" empty_bytes 32 in
  let ts0 = HSCrypto.hkdf_expand_label h ms "traffic secret" log_hash 32 in
  let svd = CoreCrypto.hmac h sfk log_hash in
  st := C (C_13_TS alpha cfk ts0);
  svd

val ks_server_13_server_finished: ks:ks -> log_hash:bytes -> ST (svd:bytes)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_1RTT_wait_HTK (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_server_finished ks log_hash =
  let KS #region st = ks in
  let S (S_13_1RTT_wait_HTK (ae, h) msId xES) = !st in
  let mSS = HSCrypto.hkdf_expand_label h xES "expanded static secret" log_hash 32 in
  let mES = HSCrypto.hkdf_expand_label h xES "expanded ephemeral secret" log_hash 32 in
  let ms = HSCrypto.hkdf_extract h mSS mES in

  let cfk = HSCrypto.hkdf_expand_label h ms "client finished" empty_bytes 32 in
  let sfk = HSCrypto.hkdf_expand_label h ms "server finished" empty_bytes 32 in
  let ts0 = HSCrypto.hkdf_expand_label h ms "traffic secret" log_hash 32 in
  let svd = CoreCrypto.hmac h sfk log_hash in
  st := S (S_13_TS (ae, h) cfk ts0);
  svd

val ks_server_13_client_finished: ks:ks -> log_hash:bytes -> ST (cvd:bytes * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_S kss /\ is_S_13_TS (S.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_13_client_finished ks log_hash =
  let KS #region st = ks in
  let S (S_13_TS alpha cfk ts0) = !st in
  let (ae, h) = alpha in
  let cvd = CoreCrypto.hmac h cfk log_hash in
  let (ck,civ,sk,siv) = expand_13 h ts0 "application data key expansion" log_hash in
  // TODO need to completely scrap and redo 1.3 index types
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Server
  } in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StreamAE.coerce HyperHeap.root id skv siv in
  let rw = StreamAE.coerce HyperHeap.root id ckv civ in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := S (S_Done);
  (cvd, StAEInstance r w)

val ks_client_13_1rtt_client_finished: ks:ks -> log_hash:bytes -> ST (cvd:bytes * recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_C kss /\ is_C_13_TS (C.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_13_1rtt_client_finished ks log_hash =
  let KS #region st = ks in
  let C (C_13_TS alpha cfk ts0) = !st in
  let (ae, h) = alpha in
  let cvd = CoreCrypto.hmac h cfk log_hash in
  let (ck,civ,sk,siv) = expand_13 h ts0 "application data key expansion" log_hash in
  // TODO need to completely scrap and redo 1.3 index types
  let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p3;
    aeAlg = (AEAD ae h);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None
    };
    writer = Client
  } in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StreamAE.coerce HyperHeap.root id ckv civ in
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let rw = StreamAE.coerce HyperHeap.root id skv siv in
  let r = StreamAE.genReader HyperHeap.root rw in
  st := C (C_Done);
  (cvd, StAEInstance r w)

// Called by Hanshake when DH key echange is negotiated
val ks_client_12_full_dh: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> CommonDH.params -> peer_share:CommonDH.key -> ST CommonDH.key
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\
    (is_C_12_Full_CH (C.s st) \/ is_C_12_Resume_CH (C.s st) \/ is_C_13_1RTT_CH (C.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_full_dh ks sr pv cs ems dhp peer_share =
  let KS #region st = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr
    | C (C_13_1RTT_CH cr _ ) -> cr in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let our_share, pmsb = CommonDH.dh_responder peer_share in
  let dhpms = PMS.DHPMS(dhp, our_share, peer_share, PMS.ConcreteDHPMS(pmsb)) in
  let dhpmsId = TLSInfo.SomePmsId(dhpms) in
  let ns = 
    if ems then
      C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS dhpmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; our_share

// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> sr:random -> pv:protocolVersion -> cs:cipherSuite -> ems:bool -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\
    (is_C_12_Full_CH (C.s st) \/ is_C_12_Resume_CH (C.s st)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

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
  let rsapmsId = TLSInfo.SomePmsId(PMS.RSAPMS(pk, pv, rsapms)) in
  let ns =
    if ems then
      C_12_wait_MS csr alpha rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS rsapmsId csr kef in
      C_12_has_MS csr alpha msId ms in
  st := C ns; encrypted

val ks_client_12_set_session_hash: ks:ks -> log:bytes -> ST unit
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\ is_C_12_wait_MS (C.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_set_session_hash ks log =
  let KS #region st = ks in
  let C (C_12_wait_MS csr alpha pmsId pms) = !st in
  let (pv, cs, true) = alpha in
  let kef = kefAlg pv cs true in
  let ms = TLSPRF.prf_hashed (pv,cs) pms (utf8 "extended master secret") log 48 in
  let msId = ExtendedMS pmsId log kef in
  st := C (C_12_has_MS csr alpha msId ms)

// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************


// Will become private; public API will have
// ks_client_12_keygen: ks -> (i:id * w:StatefulLHAE.writer i)
// ks_server_12_keygen: ...
val ks_12_get_keys: ks:ks -> ST (wk:bytes * wiv:bytes * rk:bytes * riv:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    match st with
    | C (C_12_has_MS _ _ _ _) | S (S_12_has_MS _ _ _ _) -> true
    | _ -> false)
  (ensures fun h0 r h1 ->
    modifies Set.empty h0 h1)

(*private*) let ks_12_get_keys ks =
  let KS #region st = ks in
  let role, csr, alpha, msId, ms =
    match !st with
    | C (C_12_has_MS csr alpha msId ms) -> Client, csr, alpha, msId, ms
    | S (S_12_has_MS csr alpha msId ms) -> Server, csr, alpha, msId, ms in
  let cr, sr = split csr 32 in
  let (pv, cs, ems) = alpha in
  let ae_id = {
    msId = msId;
    kdfAlg = kdfAlg pv cs;
    pv = pv;
    aeAlg = get_aeAlg cs;
    csrConn = csr;
    ext = TLSInfo.ne_default; // TODO FIXME we don't have full NE anymore
    writer = role
  } in
  let expand = TLSPRF.kdf ae_id.kdfAlg ms (sr @| cr) 40 in
  let k1, expand = split expand 16 in
  let k2, expand = split expand 16 in
  let iv1, iv2 = split expand 4 in
  let wk, wiv, rk, riv =
    match role with
    | Client -> k1, iv1, k2, iv2
    | Server -> k2, iv2, k1, iv1 in
  (wk, wiv, rk, riv)

// VD functions split because we think the log agreement predicate may be different

val ks_client_12_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_C st /\ is_C_12_has_MS (C.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_verify_data ks log =
  let KS #region st = ks in
  let C (C_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Client log

val ks_server_12_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_S st /\ is_S_12_has_MS (S.s st))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_verify_data ks log =
  let KS #region st = ks in
  let S (S_12_has_MS csr alpha msId ms) = !st in
  let (pv, cs, ems) = alpha in
  st := C C_Done;
  TLSPRF.verifyData (pv,cs) ms Server log


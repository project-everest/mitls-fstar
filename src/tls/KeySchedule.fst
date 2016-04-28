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
type pms = PMS.pms 

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
type ks_alpha = pv:protocolVersion * cs:cipherSuite * nego:negotiatedExtensions

// Internal KS state, now with ad-hoc parameters
type ks_state =
// Client
| KS_C_Init
| KS_C_12_Resume_CH: cr:random -> si:sessionInfo -> msId:TLSInfo.msId -> ms:ms -> ks_state
| KS_C_12_Full_CH: cr:random -> ks_state
| KS_C_12_wait_MS: csr:csRands -> alpha:ks_alpha -> id:TLSInfo.pmsId -> pms:bytes -> ks_state
| KS_12_has_MS: r:role -> csr:csRands -> alpha:ks_alpha -> id:TLSInfo.msId -> ms:ms -> ks_state
// Server
| KS_S_Init
| KS_S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha -> our_share:CommonDH.key -> ks_state
| KS_S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha -> ks_state
| KS_S_12_wait_MS: csr:csRands -> alpha:ks_alpha -> id:TLSInfo.pmsId -> pms:bytes -> ks_state // This state could be removed by always passing the session hash to ks_server_12_cke_dh as it is always available at CKE
| KS_Done // PMS and MS must be deleted from memory

type ks =
| KS: #region:rid -> cfg:config -> state:rref region ks_state -> ks

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> config -> role -> ST ks
  (requires fun h -> rid<>root)
  (ensures fun h0 r h1 ->
    let KS #ks_region cfg state = r in
    fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref state} h0 h1)

let create #rid cfg r =
  ST.recall_region rid;
  let ks_region = new_region rid in 
  let istate = match r with | Client -> KS_C_Init | Server -> KS_S_Init in
  KS #ks_region cfg (ralloc ks_region istate)

// Called before sending client hello
// (the external style of resumption may become internal to protect ms abstraction)
val ks_client_init_12: ks:ks -> ST (random * option sessionInfo)
  (requires fun h0 -> sel h0 (KS.state ks) = KS_C_Init)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

// TODO resumption support
let ks_client_init_12 ks =
  let cr = Nonce.mkHelloRandom () in
  let osi, ns = None, (KS_C_12_Full_CH cr) in
//    match cfg.resuming with
//    | None -> None, (KS_C_12_Full_CH cr)
//    | Some shard ->
//      (match DB.lookup shard with TODO
//      | Some (si, msId, ms) -> (Some si), (KS_C_12_Resume_CH cr si msId ms)
//      | None -> None, (KS_C_12_Full_CH cr)) in
  (KS.state ks) := ns;
  cr, osi

val ks_server_12_init_dh: ks:ks -> cr:random -> alpha:ks_alpha -> ST (random * CommonDH.key)
  (requires fun h0 ->
    let (pv, cs, nego) = alpha in
    sel h0 (KS.state ks) = KS_S_Init
    /\ is_CipherSuite cs
    /\ (let CipherSuite kex sa ae = cs in
         (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_init_dh ks cr alpha =
  let KS #region cfg st = ks in
  let (pv, cs, nego) = alpha in
  let sr = Nonce.mkHelloRandom () in
  let CipherSuite kex sa ae = cs in
  let group = 
    match kex with
    | Kex_ECDHE ->
      (match nego.ne_supported_curves with
      | Some (h::_) -> CommonDH.ECDH h
      | _ -> CommonDH.ECDH (CoreCrypto.ECC_P256))
    | Kex_DHE -> CommonDH.default_group in // TODO FFDH
  let our_share = CommonDH.keygen group in
  let csr = cr @| sr in
  st := KS_S_12_wait_CKE_DH csr alpha our_share;
  (sr, our_share)

val ks_server_12_cke_dh: ks:ks -> peer_share:CommonDH.key -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    is_KS_S_12_wait_CKE_DH kss)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_server_12_cke_dh ks peer_share =
  let KS #region cfg st = ks in
  let KS_S_12_wait_CKE_DH csr alpha our_share = !st in
  let (pv, cs, nego) = alpha in
  let pmsb = CommonDH.dh_initiator our_share peer_share in
  let dhp = CommonDH.key_params our_share in
  let pms = PMS.DHPMS(dhp, our_share, peer_share, PMS.ConcreteDHPMS(pmsb)) in
  let pmsId = TLSInfo.SomePmsId(pms) in
  let kef = kefAlg pv cs nego.ne_extended_ms in
  let ms = TLSPRF.extract kef pmsb csr 48 in
  let ns =
    if nego.ne_extended_ms then
     KS_S_12_wait_MS csr alpha pmsId pmsb
    else
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS pmsId csr kef in
      KS_12_has_MS Server csr alpha msId ms in
   st := ns

// Called after receiving server hello; server accepts resumption proposal
// This function only checks the agility paramaters compared to the resumed sessionInfo
// and returns to the handshake whether the resumption is permissible
val ks_client_12_resume: ks:ks -> random -> alpha:ks_alpha -> ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS.state ks) in
    let (pv, cs, nego) = alpha in
    is_KS_C_12_Resume_CH kss
    /\ (let si = KS_C_12_Resume_CH.si kss in
      si.protocol_version = pv /\ si.cipher_suite = cs
      /\ (si.extensions.ne_extended_ms <==> nego.ne_extended_ms)))
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_resume ks sr alpha =
  let KS #region cfg st = ks in
  let KS_C_12_Resume_CH cr si msId ms = !st in
  let csr = cr @| sr in
  st := KS_12_has_MS Client csr alpha msId ms

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

// Called by Hanshake when DH key echange is negotiated
val ks_client_12_full_dh: ks:ks -> random -> ks_alpha -> CommonDH.params -> peer_share:CommonDH.key -> ST CommonDH.key
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_KS_C_12_Full_CH st \/ is_KS_C_12_Resume_CH st)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_full_dh ks sr alpha dhp peer_share =
  let KS #region cfg st = ks in
  let (pv, cs, nego) = alpha in
  let cr = match !st with
    | KS_C_12_Full_CH cr -> cr
    | KS_C_12_Resume_CH cr _ _ _ -> cr in
  let csr = cr @| sr in
  let our_share, pmsb = CommonDH.dh_responder peer_share in
  let dhpms = PMS.DHPMS(dhp, our_share, peer_share, PMS.ConcreteDHPMS(pmsb)) in
  let dhpmsId = TLSInfo.SomePmsId(dhpms) in
  let ns = 
    if nego.ne_extended_ms then
      KS_C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
//      let ms = TLSPRF.prf (pv,cs) pmsb (utf8 "master secret") csr 48 in
      let msId = StandardMS dhpmsId csr kef in
      KS_12_has_MS Client csr alpha msId ms in
  st := ns; our_share

// Called by Handshake after server hello when a full RSA key exchange is negotiated
val ks_client_12_full_rsa: ks:ks -> random -> ks_alpha -> RSAKey.pk -> ST bytes
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_KS_C_12_Full_CH st \/ is_KS_C_12_Resume_CH st)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_client_12_full_rsa ks sr alpha pk =
  let KS #region cfg st = ks in
  let (pv, cs, nego) = alpha in
  let cr = match !st with
    | KS_C_12_Full_CH cr -> cr
    | KS_C_12_Resume_CH cr _ _ _ -> cr in
  let csr = cr @| sr in
  let rsapms = PMS.genRSA pk pv in
  let pmsb = PMS.leakRSA pk pv rsapms in
  let encrypted = CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 pmsb in
  let rsapmsId = TLSInfo.SomePmsId(PMS.RSAPMS(pk, pv, rsapms)) in
  let ns =
    if nego.ne_extended_ms then
      KS_C_12_wait_MS csr alpha rsapmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let msId = StandardMS rsapmsId csr kef in
      KS_12_has_MS Client csr alpha msId ms in
  st := ns; encrypted

// This MUST be called by handshake as soon as session hash is available if EMS was negotiated
val ks_12_set_session_hash: ks:ks -> bytes -> ST unit
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_KS_C_12_wait_MS st \/ is_KS_S_12_wait_MS st)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_12_set_session_hash ks session_hash =
  let KS #region cfg st = ks in
  let role, csr, alpha, pmsId, pms =
    match !st with
    | KS_C_12_wait_MS csr alpha pmsId pms -> Client, csr, alpha, pmsId, pms
    | KS_S_12_wait_MS csr alpha pmsId pms -> Server, csr, alpha, pmsId, pms in
  let (pv, cs, nego) = alpha in
  let kef = kefAlg pv cs true in
  let ms = TLSPRF.prf_hashed (pv,cs) pms (utf8 "extended master secret") session_hash 48 in
  let msId = ExtendedMS pmsId session_hash kef in
  st := KS_12_has_MS role csr alpha msId ms

// *********************************************************************************
//  All functions below assume that the MS is already computed (and thus they are
//  shared accross role, key exchange, handshake mode...)
// *********************************************************************************

val ks_12_get_keys: ks:ks -> ST (wk:bytes * wiv:bytes * rk:bytes * riv:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_KS_12_has_MS st)
  (ensures fun h0 r h1 ->
    modifies Set.empty h0 h1)

let ks_12_get_keys ks =
  let KS #region cfg st = ks in
  let KS_12_has_MS role csr alpha msId ms = !st in
  let cr, sr = split csr 32 in
  let (pv, cs, nego) = alpha in
  let ae_id = {
    msId = msId;
    kdfAlg = kdfAlg pv cs;
    pv = pv;
    aeAlg = get_aeAlg cs;
    csrConn = csr;
    ext = nego;
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

val ks_12_verify_data: ks:ks -> log:bytes -> ST (vd:bytes)
  (requires fun h0 ->
    let st = sel h0 (KS.state ks) in
    is_KS_12_has_MS st)
  (ensures fun h0 r h1 ->
    let KS #rid cfg st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid !{as_ref st} h0 h1)

let ks_12_verify_data ks log =
  let KS #region cfg st = ks in
  let KS_12_has_MS role csr alpha msId ms = !st in
  let (pv, cs, nego) = alpha in
  st := KS_Done; // Destroy MS, would be better to erase instead of garbage collect
  TLSPRF.verifyData (pv,cs) ms role log


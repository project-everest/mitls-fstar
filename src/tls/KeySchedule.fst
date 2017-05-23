(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module KeySchedule

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.Set

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open Extensions
open TLSInfo
open Range
open StatefulLHAE
open HKDF
open PSK

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module H = Hashing.Spec

(* A flag for runtime debugging of computed keys.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false *)
let discard (b:bool): ST unit (requires (fun _ -> True))
 (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print s = discard (IO.debug_print_string ("KS | "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  if Flags.debug_KS then print else (fun _ -> ())

#set-options "--lax"

let print_share (#g:CommonDH.group) (s:CommonDH.share g) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  =
  let kb = CommonDH.serialize_raw #g s in
  let kh = Platform.Bytes.hex_of_bytes kb in
  IO.debug_print_string ("Share: "^kh^"\n")

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
  b:bytes{length b = H.tagLen (esId_hash i)}

let read_psk (i:PSK.pskid)
  : ST (esId * PSK.app_psk i * H.alg * aeadAlg)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let i = utf8 (iutf8 i) in // FIXME Platform.Bytes !!
  let c = PSK.psk_info i in
  (ApplicationPSK i c.early_hash, PSK.psk_value i, c.early_hash, c.early_ae)

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
type fink (i:finishedId) = HMAC.UFCMA.key (HMAC.UFCMA.HMAC_Finished i) (fun _ -> True)
type binderKey (i:binderId) = HMAC.UFCMA.key (HMAC.UFCMA.HMAC_Binder i) (fun _ -> True)

// TLS 1.3 master secret (abstract)
abstract type ams (i:asId) = H.tag (asId_hash i)

type rekeyId (li:logInfo) = i:expandId li{
  (let ExpandedSecret _ t _ = i in
    ApplicationTrafficSecret? t \/
    ClientApplicationTrafficSecret? t \/
    ServerApplicationTrafficSecret? t)}

abstract type rekey_secrets #li (i:expandId li) =
  H.tag (expandId_hash i) * H.tag (expandId_hash i)

abstract type rms #li (i:rmsId li) = H.tag (rmsId_hash i)

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
| C_13_wait_SH: cr:random -> esl: list ((i:esId & es i) * PSK.pskInfo) ->
                gs:list (g:CommonDH.group & CommonDH.keyshare g) -> ks_client_state
| C_13_wait_SF: alpha:ks_alpha13 -> (i:finishedId & cfk:fink i) -> (i:finishedId & sfk:fink i) ->
                (i:asId & ams:ams i) -> ks_client_state
| C_13_wait_CF: alpha:ks_alpha13 -> (i:finishedId & cfk:fink i) -> (i:asId & ams:ams i) ->
                (li:logInfo & i:rekeyId li & rekey_secrets i) -> ks_client_state
| C_13_postHS: alpha:ks_alpha13 -> (li:logInfo & i:rekeyId li & rekey_secrets i) ->
                (li:logInfo & i:rmsId li & rms i) -> ks_client_state
| C_Done

type ks_server_state =
| S_Init: sr:random -> ks_server_state
| S_12_wait_CKE_DH: csr:csRands -> alpha:ks_alpha12 -> our_share:(g:CommonDH.group & CommonDH.keyshare g) -> ks_server_state
| S_12_wait_CKE_RSA: csr: csRands -> alpha:ks_alpha12 -> ks_server_state
| S_12_has_MS: csr:csRands -> alpha:ks_alpha12 -> id:TLSInfo.msId -> ms:ms -> ks_server_state
| S_13_wait_SH: alpha:ks_alpha13 -> cr:random -> sr:random -> es:(i:esId & es i) ->
                hs:( i:hsId & hs i ) -> ks_server_state
| S_13_wait_SF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:finishedId & sfk:fink i ) ->
                ( i:asId & ams:ams i ) -> ks_server_state
| S_13_wait_CF: alpha:ks_alpha13 -> ( i:finishedId & cfk:fink i ) -> ( i:asId & ams i ) ->
                ( li:logInfo & i:rekeyId li & rekey_secrets i ) ->  ks_server_state
| S_13_postHS: alpha:ks_alpha13 -> ( li:logInfo & i:rekeyId li & rekey_secrets i ) ->
                ( li:logInfo & i:rmsId li & rms i ) -> ks_server_state
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
| KS: #region:rid -> state:(ref ks_state){HS.MkRef?.id state = region} -> ks
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
  HKDF.hkdf_expand_label h secret "finished" empty_bytes (H.tagLen h)

// Create a fresh key schedule instance
// We expect this to be called when the Handshake instance is created
val create: #rid:rid -> role -> ST (ks * random)
  (requires fun h -> rid<>root)
  (ensures fun h0 (r,_) h1 ->
    let KS #ks_region state = r in
    stronger_fresh_region ks_region h0 h1
    /\ extends ks_region rid
    /\ modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref state))) (HS.HS?.h h0) (HS.HS?.h h1))

let create #rid r =
  ST.recall_region rid;
  let ks_region = new_region rid in
  let nonce = Nonce.mkHelloRandom r ks_region in
  let istate = match r with
    | Client -> C (C_Init nonce)
    | Server -> S (S_Init nonce) in
  (KS #ks_region (ralloc ks_region istate)), nonce

let group_of_valid_namedGroup
  (g:valid_namedGroup)
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

val ks_client_13_init: ks:ks -> pskl:list PSK.pskid -> gl:list valid_namedGroup
  -> ST (list (i:binderId & bk:binderKey i) *
         list (PSK.pskid * PSK.pskInfo) *
         CommonDH.clientKeyShare)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 (bkl, pskl, gxl) h1 ->
    let KS #rid st = ks in
    gl == List.Tot.map group_of_cks gxl /\
    modifies (Set.singleton rid) h0 h1 /\
    modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_13_init ks pskl gl =
  dbg ("ks_client_13_init");
  let KS #rid st = ks in
  let C (C_Init cr) = !st in
  let groups = List.Tot.map group_of_valid_namedGroup gl in
  let keygen (g:CommonDH.group)
    : St (g:CommonDH.group & CommonDH.keyshare g)
    = (| g, CommonDH.keygen g |) in
  let gs = map_ST keygen groups in

  let serialize_share (gx:(g:CommonDH.group & CommonDH.keyshare g)) =
    let (| g, gx |) = gx in
    match CommonDH.namedGroup_of_group g with
    | None -> None // Impossible
    | Some ng -> Some (CommonDH.Share g (CommonDH.pubshare #g gx)) in
  let gxl = List.Tot.choose serialize_share gs in

  let mk_binder (pskid:PSK.pskid)
    : ST (((i:esId & es:es i) * PSK.pskInfo)
        * ((i:binderId & bk:binderKey i) * (PSK.pskid * PSK.pskInfo)))
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1) =
    let i, psk, h, ae = read_psk pskid in
    let pski = PSK.psk_info pskid in
    dbg ("Loaded pre-shared key "^(print_bytes pskid)^": "^(print_bytes psk));
    let es : es i = HKDF.hkdf_extract h (H.zeroHash h) psk in
    dbg ("Early secret: "^(print_bytes es));
    let ll, lb =
      if ApplicationPSK? i then ExtBinder, "ext binder"
      else ResBinder, "res binder" in
    let bId = Binder i ll in
    let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
    dbg ("Binder key: "^(print_bytes bk));
    let bk = finished_13 h bk in
    dbg ("Binder Finished key: "^(print_bytes bk));
    let bk : binderKey bId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Binder bId) (fun _ -> True) rid bk in
    ((| i, es |), pski), ((| bId, bk|), (pskid, pski)) in

  let pskl = map_ST mk_binder pskl in
  let (esl, bkl) = List.Tot.split pskl in
  let (bkl, pskinfo) = List.Tot.split bkl in
  st := C (C_13_wait_SH cr esl gs);
  (bkl, pskinfo, gxl)

// Derive the early data key from the first offered PSK
// Only called if 0-RTT is enabled on the client
let ks_client_13_ch ks (log:bytes) : ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies_none h0 h1)
  =
  dbg ("ks_client_13_ch log="^(print_bytes log));
  let KS #rid st = ks in
  let C (C_13_wait_SH cr esl gs) = !st in
  let ((| i, es |), pski) :: _ = esl in // First PSK is for ED

  let h = esId_hash i in
  let li = LogInfo_CH0 ({
   li_ch0_cr = cr;
   li_ch0_ed_ae = AEAD (PSK.pskInfo_ae pski) h;
   li_ch0_ed_hash = h;
   li_ch0_ed_psk = ApplicationPSK?.i i; }) in
  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID i) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret: "^(print_bytes ets));

  // Expand all keys from the derived early secret
  let (ck, civ) = keygen_13 h ets (PSK.pskInfo_ae pski) in
  dbg ("Client 0-RTT key: "^(print_bytes ck));
  dbg ("Client 0-RTT IV: "^(print_bytes civ));

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_d = StAEInstance r rw in
  early_d

// Called before sending client hello
// (the external style of resumption may become internal to protect ms abstraction)
val ks_client_12_init: ks:ks -> ST (option sessionInfo)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_Init? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

// TODO resumption support
let ks_client_12_init ks =
  dbg "ks_client_12_init";
  let KS #rid st = ks in
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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_12_init_dh ks cr pv cs ems g =
  dbg "ks_server_12_init_dh";
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let CipherSuite kex sa ae = cs in
  let our_share = CommonDH.keygen g in
  let _ = print_share (CommonDH.pubshare our_share) in
  let csr = cr @| sr in
  st := S (S_12_wait_CKE_DH csr (pv, cs, ems) (| g, our_share |));
  CommonDH.pubshare our_share

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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_13_init ks cr cs pskid g_gx =
  dbg ("ks_server_init");
  let KS #region st = ks in
  let S (S_Init sr) = !st in
  let CipherSuite13 ae h = cs in
  let esId, es, bk =
    match pskid with
    | Some id ->
      dbg ("Using negotiated PSK: "^(print_bytes id));
      let i, psk, h, _ = read_psk id in
      let es = HKDF.hkdf_extract h (H.zeroHash h) psk in
      let ll, lb =
        if ApplicationPSK? i then ExtBinder, "ext binder"
        else ResBinder, "res binder" in
      let bId = Binder i ll in
      let bk = HKDF.derive_secret h es lb (H.emptyHash h) in
      dbg ("Binder key: "^(print_bytes bk));
      let bk = finished_13 h bk in
      dbg ("Binder Finished key: "^(print_bytes bk));
      let bk : binderKey bId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Binder bId) (fun _ -> True) region bk in
      i, es, Some (| bId, bk |)
    | None ->
      dbg "No PSK selected.";
      NoPSK h, HKDF.hkdf_extract h (H.zeroHash h) (H.zeroHash h), None
    in
  dbg ("Computed early secret: "^(print_bytes es));
  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("Handshake salt: "^(print_bytes salt));
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
  dbg ("Handshake secret: "^(print_bytes hs));
  st := S (S_13_wait_SH (ae, h) cr sr (| esId, es |) (| hsId, hs |));
  gy, bk

let ks_server_13_0rtt_key ks (log:bytes)
  : ST (recordInstance)
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
    li_ch0_ed_ae = AEAD ae h;
    li_ch0_ed_hash = h;
    li_ch0_ed_psk = empty_bytes;
  }) in
  let log : hashed_log li = log in
  let expandId : expandId li = ExpandedSecret (EarlySecretID esId) ClientEarlyTrafficSecret log in
  let ets = HKDF.derive_secret h es "c e traffic" log in
  dbg ("Client early traffic secret: "^(print_bytes ets));

  // Expand all keys from the derived early secret
  let (ck,civ) = keygen_13 h ets ae in
  dbg ("Client 0-RTT key: "^(print_bytes ck));
  dbg ("Client 0-RTT IV: "^(print_bytes civ));

  let id = ID13 (KeyID expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in
  let early_d = StAEInstance r rw in
  early_d

val ks_server_13_sh: ks:ks -> log:bytes -> ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ S_13_wait_SH? (S?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_server_13_sh ks log =
  dbg ("ks_server_13_sh, hashed log = "^(print_bytes log));
  let KS #region st = ks in
  let S (S_13_wait_SH (ae, h) cr sr _ (| hsId, hs |)) = !st in
  let secretId = HandshakeSecretID hsId in
  let li = LogInfo_SH ({
    li_sh_cr = cr;
    li_sh_sr = sr;
    li_sh_ae = AEAD ae h;
    li_sh_hash = h;
    li_sh_psk = None;
  }) in
  let log : hashed_log li = log in

  let c_expandId = ExpandedSecret secretId ClientHandshakeTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ServerHandshakeTrafficSecret log in

  // Derived handshake secret
  let cts = HKDF.derive_secret h hs "c hs traffic" log in
  dbg ("client handshake traffic secret: "^(print_bytes cts));
  let sts = HKDF.derive_secret h hs "s hs traffic" log in
  dbg ("server handshake traffic secret: "^(print_bytes sts));
  let (ck,civ) = keygen_13 h cts ae in
  dbg ("handshake key[C]: "^(print_bytes ck)^", IV="^(print_bytes civ));
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("handshake key[S]: "^(print_bytes sk)^", IV="^(print_bytes siv));

  // Handshake traffic keys
  let id = ID13 (KeyID c_expandId) in
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HyperHeap.root id (skv @| siv) in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in

  // Finished keys
  let cfkId = FinishedID c_expandId in
  let sfkId = FinishedID s_expandId in
  let cfk1 = finished_13 h cts in
  dbg ("client finished key: "^(print_bytes cfk1));
  let sfk1 = finished_13 h sts in
  dbg ("server finished key: "^(print_bytes sfk1));

  let cfk1 : fink cfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished cfkId) (fun _ -> True) region cfk1 in
  let sfk1 : fink sfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished sfkId) (fun _ -> True) region sfk1 in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  dbg ("Application salt: "^(print_bytes salt));

  // Replace handshake secret with application master secret
  let amsId = ASID saltId in
  let ams : ams amsId = HKDF.hkdf_extract h salt (H.zeroHash h) in
  dbg ("Application secret: "^(print_bytes ams));

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

private val ks_12_record_key: ks:ks -> St recordInstance
let ks_12_record_key ks =
  dbg "ks_12_record_key";
  let KS #region st = ks in
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
  dbg ("keystring (CK, CIV, SK, SIV) = "^(print_bytes expand));
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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))
let ks_server_12_cke_dh ks gy hashed_log =
  dbg "ks_server_12_cke_dh";
  let KS #region st = ks in
  let S (S_12_wait_CKE_DH csr alpha (| g, gx |)) = !st in
  let (pv, cs, ems) = alpha in
  let (| _, gy |) = gy in
  let _ = print_share gy in
  let pmsb = CommonDH.dh_initiator #g gx gy in
  dbg ("PMS: "^(print_bytes pmsb));
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
      dbg ("master secret:"^(print_bytes ms));
      let msId = StandardMS pmsId csr kef in
      msId, ms
      end
    in
  st := S (S_12_has_MS csr alpha msId ms);
  ks_12_record_key ks

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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_resume ks sr pv cs =
  let KS #region st = ks in
  let C (C_12_Resume_CH cr si msId ms) = !st in
  let csr = cr @| sr in
  let ems = si.extended_ms in
  st := C (C_12_has_MS csr (pv, cs, ems) msId ms)

// The two functions below are similar but we decide not to factor them because:
//   1. they use different arguemtns
//   2. they use different return types
//   3. they are called at different locations

val ks_client_13_sh: ks:ks -> sr:random -> cs:cipherSuite -> h:bytes ->
  gy:(g:CommonDH.group & CommonDH.share g) -> accept_psk:option nat ->
  ST (recordInstance)
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SH? (C?.s kss) /\
    // Ensure that the PSK accepted is one offered
    (let C_13_wait_SH _ ei gc = C?.s kss in
     (List.Tot.existsb (fun gx -> dfst gy = dfst gx) gc) /\
     (match ei, accept_psk with
      | [], None -> True
      | _::_ , Some n -> n < List.Tot.length ei
      | _ -> False)))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

// ServerHello log breakpoint (client)
let ks_client_13_sh ks sr cs log (| g, gy|) accept_psk =
  dbg ("ks_client_13_sh hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let C (C_13_wait_SH cr esl gc) = !st in
  let Some gx = List.Tot.find (
      fun ((| g', _ |):(x:CommonDH.group & CommonDH.keyshare g)) -> g = g'
    ) gc in
  let (| g, gx |) = gx in
  let b = print_share gy in
  let gxy = CommonDH.dh_initiator #g gx gy in
  dbg ("DH shared secret: "^(print_bytes gxy));
  let CipherSuite13 ae h = cs in
  let gx = CommonDH.pubshare gx in

  // Early secret: must derive zero here as hash is not known before
  let esId, es =
    match esl, accept_psk with
    | l, Some n ->
      let Some ((| i, es |), pski) : option ((i:esId & es i) * PSK.pskInfo)
        = List.Tot.nth l n in
      dbg ("Recalling PSK early secret: "^(print_bytes es));
      i, es
    | _, None ->
      let es = HKDF.hkdf_extract h (H.zeroHash h) (H.zeroHash h) in
      dbg ("No PSK negotiated. Early secret: "^(print_bytes es));
      NoPSK h, es
  in

  let saltId = Salt (EarlySecretID esId) in
  let salt = HKDF.derive_secret h es "derived" (H.emptyHash h) in
  dbg ("Handshake salt: "^(print_bytes salt));

  let hsId = HSID_DHE saltId g gx gy in
  let hs : hs hsId = HKDF.hkdf_extract h salt gxy in
  dbg ("Handshake secret: "^(print_bytes hs));

  let secretId = HandshakeSecretID hsId in
  let li = LogInfo_SH ({
    li_sh_cr = cr;
    li_sh_sr = sr;
    li_sh_ae = AEAD ae h;
    li_sh_hash = h;
    li_sh_psk = None;
  }) in
  let log: hashed_log li = log in
  let c_expandId = ExpandedSecret secretId ClientHandshakeTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ServerHandshakeTrafficSecret log in

  let cts = HKDF.derive_secret h hs "c hs traffic" log in
  dbg ("client handshake traffic secret: "^(print_bytes cts));
  let sts = HKDF.derive_secret h hs "s hs traffic" log in
  dbg ("server handshake traffic secret: "^(print_bytes sts));
  let (ck,civ) = keygen_13 h cts ae in
  dbg ("handshake key[C]: "^(print_bytes ck)^", IV="^(print_bytes civ));
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("handshake key[S]: "^(print_bytes sk)^", IV="^(print_bytes siv));

  // Finished keys
  let cfkId = FinishedID c_expandId in
  let sfkId = FinishedID s_expandId in
  let cfk1 = finished_13 h cts in
  dbg ("client finished key: "^(print_bytes cfk1));
  let sfk1 = finished_13 h sts in
  dbg ("server finished key: "^(print_bytes sfk1));

  let cfk1 : fink cfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished cfkId) (fun _ -> True) region cfk1 in
  let sfk1 : fink sfkId = HMAC.UFCMA.coerce (HMAC.UFCMA.HMAC_Finished sfkId) (fun _ -> True) region sfk1 in

  let saltId = Salt (HandshakeSecretID hsId) in
  let salt = HKDF.derive_secret h hs "derived" (H.emptyHash h) in
  dbg ("Application salt: "^(print_bytes salt));

  let asId = ASID saltId in
  let ams : ams asId = HKDF.hkdf_extract h salt (H.zeroHash h) in
  dbg ("Application secret: "^(print_bytes ams));

  let id = ID13 (KeyID c_expandId) in
  assert_norm(ID13 (KeyID s_expandId) = peerId id);
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let w = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let rw = StAE.coerce HyperHeap.root id (skv @| siv) in
  let r = StAE.genReader HyperHeap.root rw in
  st := C (C_13_wait_SF (ae, h) (| cfkId, cfk1 |) (| sfkId, sfk1 |) (| asId, ams |));
  StAEInstance r w

(******************************************************************)

let ks_client_13_sf ks (log:bytes)
  : ST (( i:finishedId & sfk:fink i ) * ( i:finishedId & cfk:fink i ) *
        recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))
  =
  dbg ("ks_client_13_sf hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let C (C_13_wait_SF alpha cfk sfk (| asId, ams |)) = !st in
  let (ae, h) = alpha in

  let (| (FinishedID #li _), _ |) = cfk in // TODO loginfo
  let log : hashed_log li = log in
  let secretId = ApplicationSecretID asId in
  let c_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in

  let cts = HKDF.derive_secret h ams "c ap traffic" log in
  dbg ("client application traffic secret: "^(print_bytes cts));
  let sts = HKDF.derive_secret h ams "s ap traffic" log in
  dbg ("server application traffic secret: "^(print_bytes sts));
  let emsId : exportId li = ExportID asId log in
  let ems = HKDF.derive_secret h ams "exp master" log in
  dbg ("exporter master secret: "^(print_bytes ems));

  let (ck,civ) = keygen_13 h cts ae in
  dbg ("application key[C]: "^(print_bytes ck)^", IV="^(print_bytes civ));
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("application key[S]: "^(print_bytes sk)^", IV="^(print_bytes siv));

  let id = ID13 (KeyID c_expandId) in
  assert_norm(peerId id = ID13 (KeyID s_expandId));
  let ckv: StreamAE.key id = ck in
  let civ: StreamAE.iv id  = civ in
  let w = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let skv: StreamAE.key (peerId id) = sk in
  let siv: StreamAE.iv (peerId id)  = siv in
  let rw = StAE.coerce HyperHeap.root id (skv @| siv) in
  let r = StAE.genReader HyperHeap.root rw in

  st := C (C_13_wait_CF alpha cfk (| asId, ams |) (| li, c_expandId, (cts,sts)|));
  (sfk, cfk, StAEInstance r w, (| li, emsId, ems |))

let ks_server_13_sf ks (log:bytes)
  : ST (recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    S? kss /\ C_13_wait_SF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))
  =
  dbg ("ks_server_13_sf hashed_log = "^(print_bytes log));
  let KS #region st = ks in
  let S (S_13_wait_SF alpha cfk _ (| asId, ams |)) = !st in
  let (| (FinishedID #li _), _ |) = cfk in // TODO loginfo
  let (ae, h) = alpha in

  let log : hashed_log li = log in
  let secretId = ApplicationSecretID asId in
  let c_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in
  let s_expandId = ExpandedSecret secretId ClientApplicationTrafficSecret log in

  let cts = HKDF.derive_secret h ams "c ap traffic" log in
  dbg ("client application traffic secret: "^(print_bytes cts));
  let sts = HKDF.derive_secret h ams "s ap traffic" log in
  dbg ("server application traffic secret: "^(print_bytes sts));
  let emsId : exportId li = ExportID asId log in
  let ems = HKDF.derive_secret h ams "exp master" log in
  dbg ("exporter master secret: "^(print_bytes ems));

  let (ck,civ) = keygen_13 h cts ae in
  dbg ("application key[C]: "^(print_bytes ck)^", IV="^(print_bytes civ));
  let (sk,siv) = keygen_13 h sts ae in
  dbg ("application key[S]: "^(print_bytes sk)^", IV="^(print_bytes siv));

  let id = ID13 (KeyID c_expandId) in
  assert_norm(peerId id = ID13 (KeyID s_expandId));
  let skv: StreamAE.key id = sk in
  let siv: StreamAE.iv id  = siv in
  let w = StAE.coerce HyperHeap.root id (skv @| siv) in
  let ckv: StreamAE.key (peerId id) = ck in
  let civ: StreamAE.iv (peerId id)  = civ in
  let rw = StAE.coerce HyperHeap.root id (ckv @| civ) in
  let r = StAE.genReader HyperHeap.root rw in

  st := S (S_13_wait_CF alpha cfk (| asId, ams |) (| li, c_expandId, (cts,sts) |));
  StAEInstance r w, (| li, emsId, ems |)

// Handshake must call this when ClientFinished goes into log
let ks_client_13_cf ks (log:bytes) : ST unit
  (requires fun h0 ->
    let kss = sel h0 (KS?.state ks) in
    C? kss /\ C_13_wait_CF? (C?.s kss))
  (ensures fun h0 r h1 ->
    let KS #rid st = ks in
    modifies (Set.singleton rid) h0 h1
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))
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
  dbg ("Resumption master secret: "^(print_bytes rms));
  st := C (C_13_postHS alpha rekey_info (| li, rmsId, rms |))

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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

let ks_client_12_full_dh ks sr pv cs ems (|g,gx|) =
  let KS #region st = ks in
  let cr = match !st with
    | C (C_12_Full_CH cr) -> cr
    | C (C_12_Resume_CH cr _ _ _) -> cr
    | C (C_13_wait_SH cr _ _ ) -> cr in
  let csr = cr @| sr in
  let alpha = (pv, cs, ems) in
  let gy, pmsb = CommonDH.dh_responder #g gx in
  let () =
    if Flags.debug_KS then
      let _ = print_share gx in
      let _ = print_share gy in
      let _ = IO.debug_print_string ("PMS: "^(Platform.Bytes.print_bytes pmsb)^"\n") in
      ()
    else () in
  let dhpmsId = PMS.DHPMS g gx gy (PMS.ConcreteDHPMS pmsb) in
  let ns =
    if ems then
      C_12_wait_MS csr alpha dhpmsId pmsb
    else
      let kef = kefAlg pv cs false in
      let ms = TLSPRF.extract kef pmsb csr 48 in
      let _ =
        if Flags.debug_KS then
           IO.debug_print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n")
        else false in
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
    /\ modifies_rref rid (Set.singleton (Heap.addr_of (as_ref st))) (HS.HS?.h h0) (HS.HS?.h h1))

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
      let ms = TLSPRF.extract kef pmsb csr 48 in
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
    /\ modifies_rref (KS?.region ks) (Set.singleton (Heap.addr_of (as_ref (KS?.state ks)))) (HS.HS?.h h0) (HS.HS?.h h1))

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
          let ms = TLSPRF.prf (pv,cs) pms (utf8 "extended master secret") log 48 in
          dbg ("extended master secret:"^(print_bytes ms));
          let msId = ExtendedMS pmsId log kef in
          msId, ms
          end
        else
          begin
          let ms = TLSPRF.extract kef pms csr 48 in
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
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
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
    /\ modifies_rref rid !{as_ref st} (HS.HS?.h h0) (HS.HS?.h h1))
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

module Old.KeySchedule

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Seq
open FStar.Bytes
//open FStar.Integers 

open TLS.Result
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
val psk (i:esId) : Tot Type0

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
val es (i:esId) : Tot Type0

// Handshake secret (abstract)
val hs (i:hsId) : Tot Type0

type fink (i:finishedId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Finished i) (fun _ -> True)
let trivial (_: bytes) = True
type binderKey (i:binderId) = HMAC_UFCMA.key (HMAC_UFCMA.HMAC_Binder i) trivial

// TLS 1.3 master secret (abstract)
val ams (i:asId) : Tot Type0

type rekeyId (li:logInfo) = i:expandId li{
  (let ExpandedSecret _ t _ = i in
    ApplicationTrafficSecret? t \/
    ClientApplicationTrafficSecret? t \/
    ServerApplicationTrafficSecret? t)}

val rekey_secrets (#li: _) (i:expandId li) : Tot Type0

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

effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)

val map_ST: ('a -> ST0 'b) -> list 'a -> ST0 (list 'b)

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
 
type ticket13 = t:Ticket.ticket{Ticket.Ticket13? t}
type bkey13 = psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t}
type binder_key = i:binderId & bk:binderKey i
type early_secret = i:esId{~(NoPSK? i)} & es i

// Called from TLS.Handshake.Client, updates both the list 
// of early secrets and computes the binder keys
val ks_client13_get_binder_keys (s:ks_client) (l:list bkey13)
  : ST (ks_client * list binder_key)
  (requires fun h0 -> C_wait_ServerHello? s /\ C_wait_ServerHello?.esl s == [])
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ C_wait_ServerHello? s
    /\ List.Tot.length (C_wait_ServerHello?.esl s') == List.Tot.length l)

val ks_client13_hello_retry 
  (ks0:ks_client{ C_wait_ServerHello? ks0 }) (g:CommonDH.group)
  : ST0 (CommonDH.share g * ks1:ks_client{ C_wait_ServerHello? ks1})

/// Derive the early data key from the first offered PSK
/// Only called if 0-RTT is enabled on the client
val ks_client13_ch (client_state: _) (log:bytes)
  : ST (exportKey * recordInstance)
  (requires fun h0 -> C_wait_ServerHello? client_state
    /\ C_wait_ServerHello?.esl client_state <> [])
  (ensures fun h0 r h1 -> modifies_none h0 h1)

val ks_server12_init_dh: sr:random -> cr:random ->
  pv:protocolVersion -> cs:cipherSuite -> ems:bool ->
  g:CommonDH.group ->
  ST (CommonDH.share g * ks_server)
  (requires fun h0 -> CipherSuite? cs
    /\ (let CipherSuite kex _ _ = cs in
      (kex = Kex_DHE \/ kex = Kex_ECDHE)))
  (ensures fun h0 (gx,s) h1 -> S12_wait_CKE_DH? s)

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

val ks_server13_0rtt_key (s:ks_server) (log:bytes)
  : ST ((li:logInfo & i:exportId li & ems i) * recordInstance)
  (requires fun h0 -> S13_wait_SH? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val ks_server13_sh: s:ks_server -> log:bytes ->
  ST (ks_server * recordInstance)
  (requires fun h0 -> S13_wait_SH? s)
  (ensures fun h0 (s', _) h1 -> modifies_none h0 h1
    /\ S13_wait_SF? s')

let ks_server13_get_sfk (S13_wait_SF _ _ sfk _) = sfk
let ks_server13_get_cfk (S13_wait_CF _ cfk _ _) = cfk

let ks_client12_finished_key (C12_has_MS _ _ _ ms) = TLSPRF.coerce ms
let ks_server12_finished_key (S12_has_MS _ _ _ ms) = TLSPRF.coerce ms

let ks_client12_ms (C12_has_MS _ _ msId ms) = (msId, ms)
let ks_server12_ms (S12_has_MS _ _ msId ms) = (msId, ms)

val ks12_client_key (s:ks_client)
  : ST recordInstance
  (requires fun h0 -> C12_has_MS? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val ks12_server_key (s:ks_server)
  : ST recordInstance
  (requires fun h0 -> S12_has_MS? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val ks_client12_resume (s:ks_client) (sr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (msId:TLSInfo.msId) (ms:bytes)
  : ST ks_client
  (requires fun h0 -> (C12_Full_CH? s \/ C_wait_ServerHello? s))
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C12_has_MS? s')

val ks_server12_resume (sr:random) (cr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (msId:msId) (ms:bytes)
  : ST ks_server
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> modifies_none h0 h1
    /\ S12_has_MS? s)

val ks_server12_cke_dh: s:ks_server ->
  gy:(g:CommonDH.group & CommonDH.share g) ->
  log:bytes ->
  ST ks_server
  (requires fun h0 -> S12_wait_CKE_DH? s /\
    (let S12_wait_CKE_DH _ _ (| g', _ |) = s in
    g' = dfst gy)) // Responder share must be over the same group as initiator's
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ S12_has_MS? s')

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

val ks_client13_sf (s:ks_client) (log:bytes) // [..Finished1]
  : ST (ks_client * ((i:finishedId & sfk:fink i) * (i:finishedId & cfk:fink i) * recordInstance * exportKey))
  (requires fun h0 -> C13_wait_Finished1? s)
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ C13_wait_Finished2? s')

val ks_server13_sf (s:ks_server) (log:bytes) // [..Finished1]
  : ST (ks_server * recordInstance * (li:logInfo & i:exportId li & ems i))
  (requires fun h0 -> S13_wait_SF? s)
  (ensures fun h0 (s',_,_) h1 -> modifies_none h0 h1
    /\ S13_wait_CF? s')

val ks_server13_cf (s:ks_server) (log:bytes)
  : ST ks_server
  (requires fun h0 -> S13_wait_CF? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ S13_postHS? s')

let ks_server13_rms (S13_postHS _ _ rms) = rms

val ks_client13_cf (s:ks_client) (log:bytes)
  : ST ks_client
  (requires fun h0 -> C13_wait_Finished2? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C13_Complete? s')

// Generate a PSK out of the current RMS and incoming ticket nonce
// May be called several times if server sends multiple tickets
val ks_client13_rms_psk (s:ks_client) (nonce:bytes)
  : ST bytes
  (requires fun h0 -> C13_Complete? s)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)

val ks_client12_full_dh (s:ks_client) (sr:random)
  (pv:protocolVersion) (cs:cipherSuite) (ems:bool)
  (g_gx:(g:CommonDH.group & CommonDH.share g))
  : ST (ks_client * CommonDH.share (dfst g_gx))
  (requires fun h0 ->
    C12_Full_CH? s \/ C12_Resume_CH? s \/ C_wait_ServerHello? s)
  (ensures fun h0 (s',_) h1 -> modifies_none h0 h1
    /\ (if ems then C12_wait_MS? s' else C12_has_MS? s'))

val ks_client12_set_session_hash (s:ks_client) (log:bytes)
  : ST (ks_client)
  (requires fun h0 -> C12_wait_MS? s)
  (ensures fun h0 s' h1 -> modifies_none h0 h1
    /\ C12_has_MS? s')

// Used by Epochs to read index of recordInstance
val getId: recordInstance -> GTot id

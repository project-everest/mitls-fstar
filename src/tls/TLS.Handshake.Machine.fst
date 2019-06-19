module TLS.Handshake.Machine

/// The Handshake verified state machine, integrating refinements,
/// monotonic properties, and stateful properties from Transcript,
/// Negotiation, KeySchedule.

// This is client-only WIP, will replace the start of Old.Handshake

open FStar.Error
open FStar.Bytes // still used for cookies, tickets, signatures... 

open Mem
open TLSError
open TLSInfo
open TLSConstants

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module HSM = HandshakeMessages
module LP = LowParse.Low.Base
module Transcript = HSL.Transcript 

// let Secret = Handshake.Secret

// TLS.Config will define a more convenient client-specific configuration
let client_config = config * Negotiation.resumeInfo 

// Helpful refinement within Secret? stating that an index is for a PSK.
assume val is_psk: Idx.id -> bool 

/// message types (move to HandshakeMessages or Repr modules)

type clientHello = HandshakeMessages.clientHello
type serverHello = HandshakeMessages.serverHello
type helloRetryRequest = msg: serverHello {Transcript.is_hrr msg} 
type encryptedExtensions = HandshakeMessages.encryptedExtensions
type finished = HandshakeMessages.finished // TODO shared type, ideally with tighter bound.

/// To be aligned with Transcript:
/// retry info, precise for clients, hashed for servers.

type client_retry_info = {
  ch0: clientHello;
  sh0: helloRetryRequest; }

type full_offer = {
  full_retry: option client_retry_info;
  full_ch: clientHello; // not insisting that ch initially has zeroed binders 
  }

type offer = { 
  hashed_retry: option Transcript.retry;
  ch: clientHello; // not insisting that ch initially has zeroed binders
  } 

let trans (n:nat) = tr: Transcript.transcript_t { Transcript.transcript_size tr <= n }

// setting binders to some default value determined by the PSK
// extension; we may need to prove that this function is idempotent
// and does not affect other accessors.
assume val clear_binders: clientHello -> clientHello 

assume val hash_retry: option client_retry_info -> option Transcript.retry

/// To be adapted within Negotation
/// 
// Offered, depending on first PSK or first ciphersuite.
assume val offered_ha:  clientHello -> EverCrypt.Hash.alg

// detail: those two may also return lists
assume val offered_shares: clientHello -> option Extensions.keyShareClientHello 
assume val offered_psks: clientHello -> option Extensions.offeredPsks 

/// certificate-based credentials (server-only for now)

assume val selected_ha: serverHello -> EverCrypt.Hash.alg // also applicable to HRR 

type serverCredentials = 
  option HandshakeMessages.(certificate13 * certificateVerify13) 
  // where to keep track of the negotiated algorithms? 
  // at least CertificateVerify could be just a ghost 

val deobfuscate: Negotiation.offer -> Negotiation.resumeInfo -> UInt32.t 
let deobfuscate offer resumeInfo = 
  let _, ris = resumeInfo in 
  match Negotiation.find_clientPske offer, ris with
  //  | Some (pski::_), ((_,ticket)::_)  -> PSK.decode_age pski.ticket_age ticket.ticket_age_add 
  | _ -> PSK.default_obfuscated_age 

// witnessed to produce the binder.
// TBC re: prior consistency; we probably need to branch as only the
// initial offer is a function of the config.

let offered0 ((cfg,resume):client_config) (offer:Negotiation.offer) = 
  let ks = offered_shares offer in 
  let now = deobfuscate offer resume in 
  Correct offer == Negotiation.client_offer 
    cfg offer.Parsers.ClientHello.random ks resume now 

let offered ((cfg,resume):client_config) (offer:full_offer) = 
  let ch = offer.full_ch in 
  match offer.full_retry with
  | None -> offered0 (cfg,resume) ch
  | Some retry -> 
    let ks1 = offered_shares ch in 
    let now1 = deobfuscate ch resume in 
    offered0 (cfg,resume) retry.ch0 
    // TBC Negotiation: /\ 
    // digest_ch0 = hash (selected_hashAlg hrr) offer0 /\ 
    // Correct offer == Negotiation.client_retry cfg offer0 ks now 

let accepted 
  (cfg:_) // avoid? unimportant 
  (prior: option Transcript.retry) 
  (offer: Negotiation.offer) 
  (sh: Parsers.ServerHello.serverHello)
  (ee: Parsers.EncryptedExtensions.encryptedExtensions) = 
  Negotiation.accept_ServerHello cfg offer sh 
  // TBC Negotiation: 
  // missing the late processing of encrypted extensions and its callback. 

  // what's actually computed and may be worth caching: 
  // pv cs resume? checkServerExtensions? pski 

assume val accepted13: cfg: config -> full_offer -> serverHello -> Type0

assume val client_complete: full_offer -> serverHello -> encryptedExtensions -> serverCredentials -> Type0


/// From Handshake.Secret, indexing TBC; for now we omit their
/// (opaque) part of the state.

assume type secret_c13_wait_ServerHello 
  (pskis: list (i:_{is_psk i}))
  (groups: list CommonDH.group) 

// we may need an extra ghost in the implementation of the type above.
assume val shares_of_ks:
  #psks  : list (i:_{is_psk i}) ->
  #groups: list CommonDH.group -> 
  secret_c13_wait_ServerHello psks groups -> option Extensions.keyShareClientHello

assume val groups_of_ks: 
  option Extensions.keyShareClientHello -> list CommonDH.group 

assume val pskis_of_psks: option Extensions.offeredPsks -> list (i:_{is_psk i})


/// State machine for the connection handshake (private to Handshake).
/// Each role now has its own type.
///
/// Low*: we'll turn all high-level messages constructor arguments
/// into ghost, possibly using reprs.

// extending the current states in Old.Handshake. Note that there is
// no need to precompute and store tags for the current transcript.
noeq type client_state 
  (region:rgn) // unused for now; worth the trouble? passed only as stateful-invariant argument? 
  (cfg: client_config) 
  // removed the nonce (may also be cached)
=
  // used only for allocating the client state and binding it to its
  // local nonce in the connection table.
  | C_init: 
    TLSInfo.random -> 
    client_state region cfg 

  // waiting for ServerHello (1.3) or ServerHello...ServerHelloDone
  // (1.2); this state may be updated after receiving HRR; it is also
  // used (transiently) for witnessing the pre-condition of the binder
  // HMACs, before providing the actual binders; the Handshake
  // invariant (specifying the Transcript state) does not hold in that
  // intermediate state.
  | C_wait_ServerHello:
    offer: full_offer { offered cfg offer } -> 
    // Witnessed in the binders, then overwritten to add binders or
    // a retry. 

    digest: Transcript.state (offered_ha offer.full_ch) (* ..tch then ..ch *) -> 
    // typically re-used, unless the server pick another algorithm

    ks: KeySchedule.ks -> 
    // in unverified state [Old.KeySchedule.C_13_wait_SH],
    // TODO key-schedule state 
    // ks: secret_c13_wait_ServerHello 
    //   (pskis_of_psks (offered_psks offer.full_ch)) 
    //   (groups_of_ks (offered_shares offer.full_ch)) ->
    // keeping the associated infos, master secrets, and exponents
    // could also use unverified 

    client_state region cfg  

  // waiting for encrypted handshake (1.3 only). The optional binders
  // are now ghost, and the transcript now uses the hash algorithm
  // chosen by the server. 
  | C13_wait_Finished1: 
    offer: full_offer{ offered cfg offer } -> 

    sh: serverHello{ accepted13 cfg offer sh (* not yet authenticated *) } -> 
    digest: Transcript.state (selected_ha sh) (* ..sh, now using the server's ha *) -> 

    ks: KeySchedule.ks -> 
    // in unverified state [Old.KeySchedule.C_13_wait_SF]
    // TODO key-schedule state 
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //sfk: Secret.fink (Secret.sfk_of_hms i) -> 
    client_state region cfg 

  // TODO add optional intermediate model-irrelevant C13_sent_EOED,
  // possibly just making fin2 optional or empty in C13_complete;
  // Old.Handshake currently holds [digestEOED ocr cfin_key] in that
  // state to complete the transaction after installing the new keys.
  
  // waiting for post-handshake messages (1.3 only; TBC rekeying);
  // also used for witnessing the pre-condition of the client finished
  // HMAC (and the client signature TBC) in which case fin2 is not yet
  // set & included in the transcript; we also remain in that state as
  // we receive tickets.
  | C13_complete:
    offer: full_offer{ offered cfg offer } -> 
    sh: serverHello{ accepted13 offer sh } -> 
    digest: Transcript.state (selected_ha sh) (* ..fin1 then ..fin2 *) -> 

    ee: encryptedExtensions -> 
    server_id: serverCredentials ->
    fin1: Ghost.erased finished -> (* received from the server *) 
    fin2: Ghost.erased finished (* sent by the client *) 
    // We keep the finished messages only to specify the transcript digest.
    { client_complete offer sh ee server_id } -> 

    ks: KeySchedule.ks -> 
    // in unverified state [Old.KeySchedule.C_13_wait_CF/postHS]
    // TODO key-schedule state 
    //  i:   Secret.ams_id ->
    //  rms: Secret.secret (rms_of_ams i tr) (* for accepting resumption tickets *) ->
    client_state region cfg  

    // let client_complete offer sh ee svn = 
    //   client_offered cfg offer /\ 
    //   client_accepted13 offer sh /\ 
    //   client_verified13 offer sh ee svc /\ 
    //   (honest_server sh ... ==> server_selected13 offer sh ee svc) 


(*
  // TLS 1.3 #20 aggravation, optional from C13_wait_Finished1
  | C13_sent_EOED: 
    transcript: Ghost.erased (transcript: trans 4 { Transcript.Hello? transcript }) -> 
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //digest (* _EOED *) ->
    //option HSM.cr13 -> 
    st region role cfg resume nonce 

  | C12_wait_CCS1 of digest      // TLS resume, digest to be authenticated by server
  | C12_wait_R_Finished1 of digest // TLS resume, digest to be authenticated by server
  | C12_wait_ServerHelloDone:
    // cr:random ->
    machineState

  | C12_wait_CCS2: // TLS classic
    ks: Secret.ks12_state ->
    digest_Finished1: digest -> // to be authenticated in the server Finished
    machineState

  | C12_wait_Finished2: // TLS classic
    ks: Secret.ks12_state ->
    digest_Finished1: digest -> // to be authenticated in the server Finished
    machineState

  | C_Complete // TODO add state
*)

// we embed in the type above refinements for functional properties
// and witnessed properties, but we also need a stateful invariant.


let client_invariant 
  (#region:rgn) (#cfg: client_config) (#nonce: TLSInfo.random) 
  (state: client_state region cfg)
  (h: HS.mem) 
= 
  match state with 
  | C_init _ -> True 

  | C_wait_ServerHello offer digest ks -> 

    let transcript = Transcript.ClientHello (hash_retry offer.full_retry) offer.full_ch in 
    // let transcript = Ghost.reveal transcript in 
    Transcript.invariant digest transcript h
    // Secret.invariant ks h

  | C13_wait_Finished1 offer sh digest  ->
    let sh : _ = assume False; sh in // mismatch on transcript refinement   
    let transcript = Transcript.Transcript13 (hash_retry offer.full_retry) offer.full_ch sh [] in
    Transcript.invariant digest transcript h
    // Secret.invariant_C13_wait_Finished1 ks

  | _ -> False 

/// We define an update condition on the state that encodes the state
/// machine and ensures stability on selected properties of
/// interest. For example, the transcript is monotonic; and
/// Negotiation's offer and mode are SSA.

let step
  (#region:rgn) (#cfg: client_config) 
  (st0 st1: client_state region cfg)
= //st0 == undo_last_step st1 
  match st0, st1 with 

  // | Cn x, Cn' x' y' -> x == x'  
  | C_init nonce0,
    C_wait_ServerHello offer1 digest1 ks1 -> offer1.full_ch.Parsers.ClientHello.random == nonce0

  | C_wait_ServerHello offer0 digest0 ks0,
    C_wait_ServerHello offer1 digest1 ks1 ->
    // enabling addition of the real binders
    ( offer0.full_retry == offer1.full_retry /\
      clear_binders offer0.full_ch == clear_binders offer1.full_ch)  \/
    // enabling addition of a retry; too lax for now 
    ( match offer0.full_retry, offer1.full_retry with 
      | None, Some hr -> hr.ch0 = offer0.full_ch 
      | _ -> False )

  | C_wait_ServerHello offer0 digest0 ks0,
    C13_wait_Finished1 offer1 sh1 digest1 -> 
    offer1 == offer0
    
  | _, _ -> False 

let mrel 
  (#region:rgn) (#cfg: client_config) =
  FStar.ReflexiveTransitiveClosure.closure (step #region #cfg)

/// We can finally define our main, stateful, monotonic type for the connection handshake
noeq abstract type t (region:rgn) = {
  cfg: client_config;
  nonce: TLSInfo.random;
  state: st:HST.mreference 
    (client_state region cfg) 
    (mrel #region #cfg) 
    { HS.frameOf st = region } }


/// ----------------------------------------------------------------
/// sample SSA properties: the initial and retried ClientHello
/// messages are both stable once defined, except for their binders.

(* Together with transcript injectivity, this is the gist of the
   authentication carried by the binders, of the form 

fun m -> 
  forall transcript.
  m = transcript_hash transcript ==>
  match transcript with
   | TruncatedClientHello retried tch ->
       let crandom = client_random tch in
       token_p (
         fun h0 -> 
         match client_lookup h0 crandom with  
         | None -> False // there is a honest client such that ...
         | Some (cfg & st) ->  
           match retried with
           | None    -> token_ch0 st tch
           | Some hr -> token_ch0 st hr.ch0 /\ token_ch1 st tch )

   | _ -> False // no other messages are MACed with the binder key.
*)

let st_ch0 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ 
  | C13_complete offer _ _ _ _ _ _ -> 
    match offer.full_retry with 
    | None    -> Some (clear_binders offer.full_ch)
    | Some hr -> Some (clear_binders hr.ch0)

let st_ch1 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ 
  | C13_complete offer _ _ _ _ _ _ -> 
    match offer.full_retry with 
    | None    -> None 
    | Some _  -> Some (clear_binders offer.full_ch)

// as a counter-example, this property is not stable:
let st_ch (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ 
  | C13_complete offer _ _ _ _ _ _ -> 
    Some (clear_binders offer.full_ch)

// establishing their stability for every step; to trivial to apply
// below, but apparently not required.
let ssa f st0 st1 = Some? (f st0) ==> f st0 == f st1 

let st_mon 
  (f: (#region:rgn -> #cfg: client_config -> client_state region cfg -> _)) = 
  region:rgn -> cfg: client_config -> 
  st0:client_state region cfg ->
  st1:client_state region cfg -> Lemma (step st0 st1 ==> ssa f st0 st1)
  
let m_ch0: st_mon st_ch0 = fun _ _ _ _ -> () 
let m_ch1: st_mon st_ch1 = fun _ _ _ _ -> () 
// expected to fail
//let m_ch: st_mon st_ch = fun _ _ _ _ -> () 

/// Testing monotonicity, relying on the new closure library; we could
/// probably do it more parametrically to scale up.

let p #region (st:t region) f (o:Negotiation.offer) h0 = 
  f (HS.sel h0 st.state) == Some o 

val witness0 (#region:rgn) (st: t region):  
  Stack clientHello 
    (requires fun h0 -> 
      h0 `HS.contains` st.state /\
      ( match HS.sel h0 st.state with 
        | C_init _ -> False
        | _        -> True ))
    (ensures fun h0 o h1 -> 
      token_p st.state (p st st_ch0 o) /\
      modifies_none h0 h1)
      
let witness0 #region st =
  match st_ch0 !st.state with 
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure 
        (step #region #st.cfg) 
        (fun st -> st_ch0 st == Some o) ();         
      witness_p st.state (p #region st st_ch0 o);
      o )

val witness1 (#region:rgn) (st: t region):  
  Stack clientHello 
    (requires fun h0 -> 
      h0 `HS.contains` st.state /\
      ( match HS.sel h0 st.state with 
        | C_init _ -> False
        | C_wait_ServerHello offer _ _  
        | C13_wait_Finished1 offer _ _ 
        | C13_complete offer _ _ _ _ _ _ -> Some? offer.full_retry ))
    (ensures fun h0 o h1 -> 
      token_p st.state (p st st_ch1 o) /\
      modifies_none h0 h1)
      
let witness1 #region st =
  match st_ch1 !st.state with 
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure 
        (step #region #st.cfg) 
        (fun st -> st_ch1 st == Some o) ();         
      witness_p st.state (p #region st st_ch1 o);
      o )

assume val stuff (#region:rgn) (st: t region): Stack unit 
  (requires fun h0      -> h0 `HS.contains` st.state)
  (ensures  fun h0 _ h1 -> h1 `HS.contains` st.state)
  
let test (#region:rgn) (st: t region): 
  Stack unit 
    (requires fun h0 -> h0 `HS.contains` st.state)
    (ensures fun h0 _ h1 -> True) 
=
  let r = st_ch1 !st.state in 
  if Some? r then 
    let o = witness1 st in 
    stuff st; 
    let r' = st_ch1 !st.state in 
    recall_p st.state (p st st_ch1 o);
    assert(r' == Some o)

/// -------------end of sanity check----------------



                          (* SERVER SIDE *)

type server_retry_info = digest0: bytes & helloRetryRequest
type s_offer = {
  retry: option retry_server_info;
  ch: clientHello; }

// Complete mode for the connection; sufficient to derive all the
// negotiated connection parameters, and shared between clients and
// servers when the connection is safe. 
// 
// As a technicality, it includes only the *tag* supposed to be the
// hash of the initial offer after a retry.

type s13_mode (region:rgn) (cfg:server_config) = {
  offer: s_offer; (* { honest_psk offer ==> client_offered offer } *) 
  sh: serverHello; 
  ee: encryptedExtensions;
  certs: certs:option HandshakeMessage.certificate13
  { 
    // including the nego callback that led to those choices; we may want to keep its [cfg']
    selected cfg offer sh ee certs };
  }

type server_state 
  (region:rgn)
  (cfg: server_config) // much smaller than before
=  
  | S_wait_ClientHello:
    server_state rgn cfg 

  // TLS 1.3, intermediate state to encryption
  | S13_sent_ServerHello:      
    mode: s13_mode -> 
    digest: Transcript.state (selected_ha sh) -> 
//  i: Idx.id -> // Secret.esId ->
//  idh: Idx.id_dhe ->
//  ks: Secret.s13_wait_ServerHello i idh -> 
    server_state region cfg 

//// TLS 1.3 intermediate state
//| S13_wait_EOED 

  | S13_wait_Finished2:
    mode: s13_mode -> 
    digest: Transcript.state (selected_ha sh) (* expected to be MACed in the Client Finished *) -> 
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->  
    fin1: Ghost.erased finished ->
//  ks: keeping fin2key and rms   
    server_state region cfg 

  | S13_complete: 
    mode: s13_mode -> 
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->  
    fin1: Ghost.erased finished ->
    fin2: Ghost.erased finished 
    { client_complete mode } -> 
//  ks: keeping rms    
    server_state region cfg 


//| S_wait_CCS1                // TLS classic
//| S_wait_Finished1 of digest // TLS classic, digest to the MACed by client
//| S_wait_CCS2 of digest      // TLS resume (CCS)
//| S_wait_CF2 of digest       // TLS resume (CF)
//| S_Complete


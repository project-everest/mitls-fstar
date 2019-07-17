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

/// Message types (move to HandshakeMessages or Repr modules)

type clientHello = HandshakeMessages.clientHello
type serverHello = HandshakeMessages.serverHello
type helloRetryRequest = msg: serverHello {Transcript.is_hrr msg} 
type encryptedExtensions = HandshakeMessages.encryptedExtensions
type finished = HandshakeMessages.finished // TODO shared type, ideally with tighter bound.


/// Auxiliary datatypes (shared between states)
/// 
/// Each Handshake state embeds the state of other modules, as
/// follows. (As we verify more, we may use more precise,
/// state-specific types for them.)
///
/// * It is parameterized by a region and a configuration.
///   LATER: add footprint and invariant as we lower the config.

// TLS.Config will define a more convenient client-specific configuration
let client_config = config * Negotiation.resumeInfo 

/// * We keep the receiver private state and a connection-allocated
///   input buffer, also used by a stub to exchange bytes with the TLS record.
///   [I wish we could pass fewer indexes.]
///
///   Note HS needs to select the incoming flight type.

//NS: Unused so far
//    * Where will this state be be held?
//    * Should something like this type be provided by HSL.Receive itself?
//    * LP.slice or const_slice?
noeq type rcv_state = { 
  flt: HSL.Receive.in_progress_flt_t; // The incoming flight we are waiting for; erase? 
  rcv: HSL.Receive.hsl_state; 
  rcv_b: Buffer.buffer UInt8.t; // how to see it as a MITLS.Repr.const_slice?
  rcv_from: UInt32.t;
  rcv_to: UInt32.t;
  // { rcv_from <= rcv_to /\ v rcv_to <= Buffer.length rcv_b }
  } 
//let rcv_inv hsl flt = HSL.Receive.pre hsl.rcv hsl.rcv_b hsl.rcv_from hsl.rcv_to flt

/// * We recompute the transcript from the HS state (with a
///   state-dependent bound on its length) and keep a digest with that
///   current contents.
///
///   This requires that HS state keep message contents, at least
///   ghostly. (Good to try out erasure.)
/// 
///   We do not include the digest in shared state because its
///   allocation is late and algorithm-dependent.
// digest: Transcript.state ha 
// TODO: invariant etc 

/// * TLS.Handshake.Send: we keep send_state. TODO: invariant etc

/// * Old.KeySchedule: most state keep either ks_client_state or
///   ks_server_state (usually knowing exactly its constructor).
///
///   
///   We should start thinking about their invariants and footprints.

// NS: Why are the _is_quic flags important?
noeq type client_keys = { 
  cks_is_quic: bool;
  cks: Old.KeySchedule.ks_client_state; } 

noeq type server_keys = { 
  sks_is_quic: bool;
  sks: Old.KeySchedule.ks_server_state; } 

// TODO we duplicate the [is_quic] bit of config to minimize change in KeySchedule; refactor?
// let Secret = Handshake.Secret

let c_wait_ServerHello_keys = s: client_keys { Old.KeySchedule.C_wait_ServerHello? s.cks }
let c13_wait_Finished1_keys = s: client_keys { Old.KeySchedule.C13_wait_Finished1? s.cks }


// Helpful refinement within Secret? stating that an index is for a PSK.
assume val is_psk: Idx.id -> bool 

/// To be aligned with Transcript:
/// retry info, precise for clients, hashed for servers.

// NS: Why is the ch0 a full clientHello
//     In transcript, it's a anyHashTag
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

// NS: See PB.build_canonical_binders (tch_binders_len tch)
//     and Transcript.truncate (ch:clientHello_with_binders)
//     Is this really meant to be Tot or will Ghost do?
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
  (sh: HandshakeMessages.sh) // refined to exclude HRR 
  (ee: Parsers.EncryptedExtensions.encryptedExtensions) = 
  Negotiation.accept_ServerHello cfg offer sh 
  // TBC Negotiation: 
  // missing the late processing of encrypted extensions and its callback. 

  // what's actually computed and may be worth caching: 
  // pv cs resume? checkServerExtensions? pski 

assume val accepted13: cfg: client_config -> full_offer -> serverHello -> Type0

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
    // typically re-used, unless the server picks another algorithm

    ks: c_wait_ServerHello_keys -> 
    // in unverified state [Old.KeySchedule.C_wait_ServerHello],
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

    ks: c13_wait_Finished1_keys -> 
    // TODO sync key-schedule state 
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //sfk: Secret.fink (Secret.sfk_of_hms i) -> 
    client_state region cfg 

  // waiting for post-handshake messages (1.3 only; TBC rekeying);
  // also used for witnessing the pre-condition of the client finished
  // HMAC (and the client signature TBC) in which case fin2 is not yet
  // set & included in the transcript; we also remain in that state as
  // we receive tickets.
  | C13_complete:
    offer: full_offer{ offered cfg offer } -> 
    sh: serverHello{ accepted13 cfg offer sh } -> 
    digest: Transcript.state (selected_ha sh) (* ..fin1 then ..fin2 *) -> 

    ee: encryptedExtensions -> 
    server_id: serverCredentials ->
    fin1: Ghost.erased finished -> (* received from the server *) 
    fin2: Ghost.erased finished (* sent by the client *) 
    // We keep the finished messages only to specify the transcript digest.
    { client_complete offer sh ee server_id } -> 

    // TLS 1.3 #20 aggravation: optional intermediate model-irrelevant
    // EOED between C13_wait_Finished1 and C13_complete, with
    // transcript [..fin1 EOED]. We add an optional parameter to track
    // it, just making fin2 optional or empty in C13_complete;
    // Old.Handshake currently holds [digestEOED ocr cfin_key] in that
    // state to complete the transaction after installing the new
    // keys.
    eoed_args: (option (
      option HSM.certificateRequest13 & 
      (i:Old.HMAC.UFCMA.finishedId & Old.KeySchedule.fink i))) ->

    ks: client_keys -> 
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

(* OLDER: 
  // TLS 1.3 #20 aggravation, optional between C13_wait_Finished1 and C13_complete, with transcript [..fin1 EOED]
  | C13_sent_EOED: 
    transcript: Ghost.erased (transcript: trans 4 { Transcript.Hello? transcript }) -> 
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //digest (* _EOED *) ->
    //option HSM.cr13 -> 
    st region role cfg resume nonce *)

(* COMMENTED OUT FOR NOW, BUT CLOSE TO WHAT WE NEED. 

  // In the TLS 1.2 states below, using [mode] as a placeholder for the final mode, 
  // but it may be better to recompute its contents on the fly from ch sh etc.
  // 
  // still missing below HSL.Receive.receive_state and HSL.Send.send_state.

  | C12_wait_ServerHelloDone:
    // 1.2 full, waiting for the rest of the first server flight
    ch: clientHello -> 
    sh: serverHello{ accepted12 ch sh } -> 
    digest: Transcript.state (selected_ha sh) -> 
    ks: client_keys -> 
    client_state region cfg 

  | C12_wait_Finished2: 
    // 1.2 full
    // the digest[..Finished1] to be MAC-verified in Finished2 will now be computed as it is received 
    mode12 -> 
    // collapsing into a single state [wait_CCS2 (true)] followed by [wait_Finished2 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript 
    wait_CCS2: bool -> 
    client_state region cfg

  | C12_wait_Finished1:
    // 1.2 resumption, waiting for the server CCS1 and Finished1 
    // we used to pass a digest, but the caller can now recompute it as it receives Finished1
    // we will need digests before (to verify it) and after (for keying)
    mode12 -> 
    // collapsing into a single state [wait_CCS1 (true)] followed by [wait_Finished1 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript 
    wait_CCS1: bool -> 
    client_state region cfg

  | C12_complete: // now with fin2 and stronger properties
    mode12 -> 
    client_state region cfg

// similar to our previous Negotiation.mode but more
// transcript-oriented; still not sufficient to recompute the
// transcript contents--will be required for TLS 1.2 security.

and mode12 = {
  m12_ch: clientHello;
  m12_sh: serverHello{ accepted12 m12_ch m12_sh };

  // currently assigned in [mode] by client_ServerKeyExchange after
  // signature verification; it may be convenient to also keep
  // messages, e.g., ServerKeyExchange and CertificateVerified 
  m12_cr: option HSM.certificateRequest12; 
  m12_ccv: option (Cert.chain13 & signatureScheme (* redundant but convenient? *)); 

  // m12_fin1: Ghost.erased finished; // initially empty
  // m12_fin2: Ghost.erased finished; // initially empty 
  m12_digest: Transcript.state (selected_ha sh);
  m12_ks: client_keys 
}


*)

// we embed in the type above refinements for functional properties
// and witnessed properties, but we also need a stateful invariant.

// NS: What is Secret.invariant?

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

  | C13_wait_Finished1 offer sh digest ks ->
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
    C13_wait_Finished1 offer1 sh1 digest1 ks1 -> 
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

// NS: What does SSA mean in this context?

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

// NS: Projecting various forms of client hellos from the client_staet
let st_ch0 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ _ 
  | C13_complete offer _ _ _ _ _ _ _ _ -> 
    match offer.full_retry with 
    | None    -> Some (clear_binders offer.full_ch)
    | Some hr -> Some (clear_binders hr.ch0)

let st_ch1 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> 
    match offer.full_retry with 
    | None    -> None 
    | Some _  -> Some (clear_binders offer.full_ch)

// as a counter-example, this property is not stable:
let st_ch (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with 
  | C_init _ -> None 
  | C_wait_ServerHello offer _ _  
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> 
    Some (clear_binders offer.full_ch)

// establishing their stability for every step; to trivial to apply
// below, but apparently not required.

// NS: `ssa f st0 st1`: f is invariant across the two states (if set initially)
let ssa f st0 st1 = Some? (f st0) ==> f st0 == f st1 

// NS: could use a more descriptive name here
//     f is preserved across the step relation  
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

// NS: could use a more descriptive name
//     seems to be turning the function f into a heap relation
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
        | C13_wait_Finished1 offer _ _ _ 
        | C13_complete offer _ _ _ _ _ _ _ _ -> Some? offer.full_retry ))
    (ensures fun h0 o h1 -> 
      token_p st.state (p st st_ch1 o) /\
      modifies_none h0 h1)

#push-options "--z3rlimit 100"  // NS: wow, that's a lot for a little proof
let witness1 #region st =
  match st_ch1 !st.state with 
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure 
        (step #region #st.cfg) 
        (fun st -> st_ch1 st == Some o) ();         
      witness_p st.state (p #region st st_ch1 o);
      o )
#pop-options
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

type server_config = config // TBC

type server_retry_info = digest0: bytes & helloRetryRequest
type s_offer = {
  retry: option server_retry_info;
  ch: clientHello; }

// Complete mode for the connection; sufficient to derive all the
// negotiated connection parameters, and shared between clients and
// servers when the connection is safe. 
// 
// As a technicality, it includes only the *tag* supposed to be the
// hash of the initial offer after a retry.

assume val selected: server_config -> s_offer -> serverHello -> encryptedExtensions -> option HandshakeMessages.certificate13 -> Type 

type s13_mode (region:rgn) (cfg:server_config) = {
  offer: s_offer; (* { honest_psk offer ==> client_offered offer } *) 
  sh: serverHello; 
  ee: encryptedExtensions;
  certs: certs:option HandshakeMessages.certificate13
  { 
    // including the nego callback that led to those choices; we may want to keep its [cfg']
    selected cfg offer sh ee certs };
  }
 
noeq type server_state 
  (region:rgn)
  (cfg: server_config) // much smaller than before
=  
  | S_wait_ClientHello:
    server_state region cfg 

  // TLS 1.3, intermediate state to encryption
  | S13_sent_ServerHello:      
    mode: s13_mode region cfg -> 
    digest: Transcript.state (selected_ha mode.sh) -> 
//  i: Idx.id -> // Secret.esId ->
//  idh: Idx.id_dhe ->
//  ks: Secret.s13_wait_ServerHello i idh -> 
    ks: server_keys -> 
    server_state region cfg 
//
//// TLS 1.3 intermediate state
//| S13_wait_EOED 
//
  | S13_wait_Finished2:
    mode: s13_mode region cfg -> 
    digest: Transcript.state (selected_ha mode.sh) (* expected to be MACed in the Client Finished *) -> 
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->  
    fin1: Ghost.erased finished ->
    ks: server_keys -> // keeping fin2key and rms   
    server_state region cfg 

  | S13_complete: 
    mode: s13_mode region cfg -> 
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->  
    fin1: Ghost.erased finished ->
    fin2: Ghost.erased finished ->
//  { client_complete mode } -> 
    ks: server_keys ->
    server_state region cfg 


//| S_wait_CCS1                // TLS classic
//| S_wait_Finished1 of digest // TLS classic, digest to the MACed by client
//| S_wait_CCS2 of digest      // TLS resume (CCS)
//| S_wait_CF2 of digest       // TLS resume (CF)
//| S_Complete


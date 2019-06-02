module TLS.Handshake.Machine

/// The Handshake verified state machine, integrating refinements,
/// monotonic properties, and stateful properties from Transcript,
/// Negotiation, KeySchedule.

// This is client-only WIP, will replace the start of Old.Handshake.

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

// missing indexes? both elements should be Client-specific, with
// resumeInfo only for clients.
let client_config = config * Negotiation.resumeInfo 

// Helpful refinement within Secret?
assume val is_psk: Idx.id -> bool 

// May also depend on the resumeInfo, to be sorted out once we fix the
// config type.
assume val psk_ids_of_config: client_config -> list (i:Idx.id{is_psk i})
assume val groups_of_config: client_config -> list CommonDH.group  

// Offered, depending on first PSK or first ciphersuite.
// May be overwritten by ServerHello 
assume val ha_of_offer: Negotiation.offer -> Spec.Hash.Definitions.hash_alg

// from Handshake.Secret, currently broken
assume type secret_c13_wait_ServerHello 
  (psks  : list (i:_{is_psk i})) 
  (groups: list CommonDH.group)

// we may need an extra ghost in the implementation of the type above.
assume val shares_of_ks:
  #psks  : list (i:_{is_psk i}) ->
  #groups: list CommonDH.group -> 
  secret_c13_wait_ServerHello psks groups -> option Extensions.keyShareClientHello

// will go to Transcript
let trans (n:nat) = tr: Transcript.transcript_t { Transcript.transcript_size tr <= n }


// to be adapted in Nego
assume val nego_find_key_shares: Negotiation.offer -> option Extensions.keyShareClientHello 

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
  let ks = nego_find_key_shares offer in 
  let now = deobfuscate offer resume in 
  Correct offer == Negotiation.client_offer cfg offer.Parsers.ClientHello.random ks resume now 

let offered ((cfg,resume):client_config) (prior:option Transcript.retry) (offer:Negotiation.offer) = 
  match prior with
  | None -> offered0 (cfg,resume) offer 
  | Some (digest_ch0, hrr) -> 
    let ks1 = nego_find_key_shares offer in 
    let now1 = deobfuscate offer resume in 
    exists (offer0: Negotiation.offer).
    offered0 (cfg,resume) offer0 
    // TBC Negotiation: /\ 
    // digest_ch0 = hash (selected_hashAlg hrr) offer0 /\ 
    // Correct offer == Negotiation.client_retry cfg offer0 ks now 

let accepted 
  (cfg:_) // avoid? 
  (prior: option Transcript.retry) 
  (offer: Negotiation.offer) 
  (sh: Parsers.ServerHello.serverHello)
  (ee: Parsers.EncryptedExtensions.encryptedExtensions) = 
  Negotiation.accept_ServerHello cfg offer sh 
  // TBC Negotiation: 
  // missing the late processing of encrypted extensions and its callback. 



/// State machine for the connection handshake (private to Handshake).
/// Each role now has its own type.
///
/// Low*: we'll turn all high-level messages constructor arguments
/// into ghost, possibly using reprs.

noeq type client_state  
  (region:rgn)            // unused for now; worth the trouble? passed only as stateful-invariant argument? 
  (cfg: client_config)    // duplicating Nego? 
  (nonce: TLSInfo.random) // could be a function of the transcript, saving one argument? 
  = 

  // allocation state, initially empty
  | C_init: 
    client_state region cfg nonce 

  // intermediate step for witnessing the truncated transcript, 
  // a pre-condition for the binder HMACs. 
  // TODO The Transcript state should be TruncatedHello. 
  | C_truncated_ClientHello: (*
    retry: _
    ch : _ 
    let ha = ... in
    let transcript = erased (Transcript.ClientHello (Transcript.retry_of retry) (HSM.hsm_of_ch ch)) in 
    Transcript.digest ha transcript   *)
    transcript: Ghost.erased (trans 0) -> 
    offer: Negotiation.offer (* TODO with zeroed binders *) ->
    digest: Transcript.state (ha_of_offer offer) -> 
    ks: secret_c13_wait_ServerHello (psk_ids_of_config cfg) (groups_of_config cfg) 
    { let transcript = Ghost.reveal transcript in 
      transcript == Transcript.Hello None (HSM.M_client_hello offer) /\
      ( exists (now:UInt32.t). (Correct offer == Negotiation.client_offer (fst cfg) nonce (shares_of_ks ks) (snd cfg) now)) }
    -> 
    client_state region cfg nonce 

  // waiting for plaintext ServerHello.
  | C_wait_ServerHello: 
    transcript: Ghost.erased (trans 0) -> 
    offer: Negotiation.offer -> 
    digest: Transcript.state (ha_of_offer offer) -> 
    ks: secret_c13_wait_ServerHello (psk_ids_of_config cfg) (groups_of_config cfg) 
    { let transcript = Ghost.reveal transcript in 
      transcript == Transcript.Hello None (HSM.M_client_hello offer) /\
      //Negotiation.correct_client_offer nego cfg nonce (shares_of_ks ks) resume now
      ( exists (now:UInt32.t). (Correct offer == Negotiation.client_offer (fst cfg) nonce (shares_of_ks ks) (snd cfg) now))
      } -> 
    client_state region cfg nonce 

  // waiting for encrypted handshake (1.3 only)
  | C13_wait_Finished1: 
    transcript: Ghost.erased (trans 1) -> 
    nego: Negotiation.mode ->
    digest: Transcript.state (Negotiation.hashAlg nego) 
    { let transcript = Ghost.reveal transcript in
      let offer = nego.Negotiation.n_offer in (
      exists (sh:_) (now:UInt32.t) (shares:_). 
      Correct offer == Negotiation.client_offer (fst cfg) nonce shares (snd cfg) now /\
      Correct nego == Negotiation.accept_ServerHello (fst cfg) offer sh /\ 
      Transcript.nego_version (HSM.M_client_hello offer) (HSM.M_server_hello sh) == TLS_1p3 /\ 
      transcript == Transcript.Transcript13 
        None (HSM.M_client_hello offer) (HSM.M_server_hello sh) [] )
    }                                 
    -> 
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //sfk: Secret.fink (Secret.sfk_of_hms i) -> 
    client_state region cfg nonce 

  // waiting for post-handshake messages (1.3 only; TBC rekeying)
  // this state is witnessed to produce Finished2, 
  // hencee it does not include it in the transcript. 
  | C13_complete: 
    transcript: Ghost.erased (trans 5) -> 
    nego: Negotiation.mode -> 
    digest: Transcript.state (Negotiation.hashAlg nego)
    { let transcript = Ghost.reveal transcript in 
      let offer = nego.Negotiation.n_offer in (
      exists 
        (now:UInt32.t) 
        (shares:_)
        (sh:_) (ee:_) (* we care about their contributions to the negotiated mode *)
        (fin:_)       (* ignored once verified *) 
        .
      Correct offer == Negotiation.client_offer (fst cfg) nonce shares (snd cfg) now /\
      Correct nego == Negotiation.accept_ServerHello (fst cfg) offer sh /\ 
      Transcript.nego_version (HSM.M_client_hello offer) (HSM.M_server_hello sh) == TLS_1p3 /\ 
      transcript == Transcript.Transcript13 
        None (HSM.M_client_hello offer) (HSM.M_server_hello sh) 
        [ Parsers.Handshake13.M13_encrypted_extensions ee; 
          Parsers.Handshake13.M13_finished fin ] )
      // TBC experiment with branching abstraction? 
    }
    -> 
    //i:   Secret.ams_id ->
    //rms: Secret.secret (rms_of_ams i tr) (* for accepting resumption tickets *) ->
    client_state region cfg nonce 


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
  (state: client_state region cfg nonce)
  (h: HS.mem) 
= 
  match state with 
  | C_init -> True

  | C_truncated_ClientHello transcript offer digest ks 
  | C_wait_ServerHello transcript offer digest ks -> 
    let transcript = Ghost.reveal transcript in 
    Transcript.invariant digest transcript h
    // Secret.invariant ks h

  | C13_wait_Finished1 transcript mode digest ->
    let transcript = Ghost.reveal transcript in 
    Transcript.invariant digest transcript h
    // Secret.invariant_C13_wait_Finished1 ks
  | _ -> False 
  

/// We define an update condition on the state that encodes the state
/// machine and ensures stability on selected properties of
/// interest. For example, the transcript is monotonic; and
/// Negotiation's offer and mode are SSA.

let step
  (#region:rgn) (#cfg: client_config) (#nonce: TLSInfo.random)
  (st0 st1: client_state region cfg nonce)
= //st0 == undo_last_step st1 
  match st0, st1 with 

  // | Cn x, Cn' x' y' -> x == x'  
  | C_init,
    C_truncated_ClientHello transcript0 offer0 digest0 ks0 -> True

  | C_truncated_ClientHello transcript0 offer0 digest0 ks0,
    C_wait_ServerHello      transcript1 offer1 digest1 ks1 ->
    let transcript0 = Ghost.reveal transcript0 in 
    let transcript1 = Ghost.reveal transcript1 in 
    exists (binders:_). 
    Some transcript1 == Transcript.transition_hsm transcript0 binders /\
    //19-05-15 can we avoid the option? 
    
    True //offer1 == transcript_offer transcript1 

  | C_wait_ServerHello      transcript0 offer0 digest0 ks0,
    C13_wait_Finished1      transcript1 mode1 digest1 ->
    let transcript0 = Ghost.reveal transcript0 in 
    let transcript1 = Ghost.reveal transcript1 in (
    exists (sh:_). 
    Some transcript1 == Transcript.transition_hsm transcript0 sh )

  | _, _ -> False 

// sample lemma: the offer is SSA. 

let st_offer
  (#region:rgn) (#cfg: client_config) (#nonce: TLSInfo.random)
  (st0: client_state region cfg nonce) 
= 
  match st0 with 
  | C_wait_ServerHello transcript0 offer0 digest0 ks0 -> Some offer0 
  | C13_wait_Finished1 transcript0 mode0 digest0 -> Some mode0.Negotiation.n_offer
  | _ -> None 

let m_offer 
  (#region:rgn) (#cfg: client_config) (#nonce: TLSInfo.random)
  (st0 st1: client_state region cfg nonce):
  Lemma (
    let o0 = st_offer st0 in
    let o1 = st_offer st1 in
    step st0 st1 /\ Some? o0 ==> o1 == o0)
=
  ()

let mrel 
  (#region:rgn) (#cfg: client_config) (#nonce: TLSInfo.random)
= ReflexiveTransitiveClosure.closure (step #region #cfg #nonce)

/// Main type for the connection handshake
noeq abstract type t (region:rgn) = {
  cfg: client_config;
  nonce: TLSInfo.random;
  state: st:HST.mreference 
    (client_state region cfg nonce) 
    (mrel #region #cfg #nonce) 
    { HS.frameOf st = region } }

/// Testing monotonicity, thanks to the new closure library

let p #region (st:t region) (o:Negotiation.offer) h0 = 
  st_offer (HS.sel h0 st.state) == Some o 

val witness_offer (#region:rgn) (st:t region): 
  Stack 
    (o: Negotiation.offer{ token_p st.state (p st o) })
    (requires fun h0 -> 
      h0 `HS.contains` st.state /\
      (match HS.sel h0 st.state with 
      | C_wait_ServerHello _ _ _ _ 
      | C13_wait_Finished1 _ _ _ -> True
      | _ -> False ))
    (ensures fun h0 o h1 -> modifies_none h0 h1)

let witness_offer #region st =
  match st_offer !st.state with 
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure 
        (step #region #st.cfg #st.nonce) 
        (fun st -> st_offer st == Some o) ();         
      witness_p st.state (p st o);
      o )


(* TODO server-side
  | S_Idle

  | S13_sent_ServerHello:      // TLS 1.3, intermediate state to encryption
    i: Idx.id -> // Secret.esId ->
    idh: Idx.id_dhe ->
    ks: Secret.s13_wait_ServerHello i idh -> machineState


  | S_wait_EOED                // Waiting for EOED
  | S_wait_Finished2 of digest // TLS 1.3, digest to be MACed by client
  | S_wait_CCS1                // TLS classic
  | S_wait_Finished1 of digest // TLS classic, digest to the MACed by client
  | S_wait_CCS2 of digest      // TLS resume (CCS)
  | S_wait_CF2 of digest       // TLS resume (CF)
  | S_Complete
*) 



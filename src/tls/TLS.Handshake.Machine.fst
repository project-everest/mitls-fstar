module TLS.Handshake.Machine

/// The Handshake verified state machine, integrating state,
/// refinements, monotonic properties, and stateful properties from
/// Transcript, Negotiation, KeySchedule, Send, and Receive.
///
///      Client                     TLS 1.3               Server
/// ________________________________________________________________________
///
/// Key  ^ ClientHello
/// Exch | + key_share*
///      | + signature_algorithms*
///      | + psk_key_exchange_modes*
///      v + pre_shared_key*       -------->          ServerHello  ^ Key
///                                                  + key_share*  | Exch
///                                             + pre_shared_key*  v
///
///                                         {EncryptedExtensions}  ^  Server
///                                         {CertificateRequest*}  v  Params
///                                                {Certificate*}  ^
///                                          {CertificateVerify*}  | Auth
///                                                    {Finished}  v
///                                <--------  [Application Data*]
///      ^ {Certificate*}
/// Auth | {CertificateVerify*}
///      v {Finished}              -------->
///
///        [Application Data]      <------->  [Application Data]
///                                <--------            [Ticket]
/// ________________________________________________________________________
/// From the RFC; omitting 0RTT Data and EOED

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
module PF = TLS.Handshake.ParseFlights
module Rcv = TLS.Handshake.Receive

/// Message types (move to HandshakeMessages or Repr modules)

type sh13 = sh: HSM.sh {Negotiation.Version.selected sh == Correct TLS_1p3}

//type clientHello = HandshakeMessages.clientHello
//type serverHello = HandshakeMessages.sh
//type helloRetryRequest = HandshakeMessages.hrr
//type encryptedExtensions = HandshakeMessages.encryptedExtensions
//type finished = HandshakeMessages.finished // TODO shared type, ideally with tighter bound.


/// Auxiliary datatypes (shared between states)
///
/// Each Handshake state embeds the state of other modules, as
/// follows. (As we verify more, we may use more precise,
/// state-specific types for them.)
///
/// * It is parameterized by a region and a configuration.
///   LATER: add footprint and invariant as we lower the config.

// TLS.Config will define a more convenient client-specific configuration
let client_config = Negotiation.client_config

/// * We will not keep Nego state.
///   We may keep [mode] for TLS 1.2 states for now
///
/// * We keep [epochs] for now, to be replaced by multistreams.
///
/// * We keep the receiver private state and a connection-allocated
///   input buffer, also used by a stub to exchange bytes with the TLS record.
///   [I wish we could pass fewer indexes.]
///
///   Note HS needs to select the incoming flight type.

(*
type noeq type rcv_state = {
  flt: HSL.Receive.in_progress_flt_t; // The incoming flight we are waiting for; erase?
  rcv: HSL.Receive.hsl_state;
  rcv_b: Buffer.buffer UInt8.t; // We need a writable slice for buffering fragment; how to view it as a MITLS.Repr.const_slice?
  rcv_from: UInt32.t;
  rcv_to: UInt32.t;
  // { rcv_from <= rcv_to /\ v rcv_to <= Buffer.length rcv_b }
  }
//let rcv_inv hsl flt = HSL.Receive.pre hsl.rcv hsl.rcv_b hsl.rcv_from hsl.rcv_to flt
*)



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
// TODO: invariant etc .

/// * TLS.Handshake.Send: we keep send_state. TODO: invariant etc


/// * Old.KeySchedule: most state keep either ks_client_state or
///   ks_server_state (usually knowing exactly its constructor).
///
///   We should start thinking about their invariants and footprints.

(* NOW IN KEYSCHEDULE:
noeq type client_keys = {
  // The [is_quic] fields duplicate a flag in the current config;
  // they are currently used to select some HKDF, as it was in
  // [KeySchedule.ks]. REFACTOR?
  cks_is_quic: bool;
  cks: Old.KeySchedule.ks_client_state; }
*)
let client_keys = Old.KeySchedule.ks_client_state

// TODO get rid of sks_is_quic, as we did for the client (the caller
// just passes to KeySchedule the config's is_quic as additional
// parameter when required)
noeq type server_keys = {
  sks_is_quic: bool;
  sks: Old.KeySchedule.ks_server_state; }

// let Secret = Handshake.Secret

let c_wait_ServerHello_keys = s: client_keys { Old.KeySchedule.C_wait_ServerHello? s }
let c13_wait_Finished1_keys = s: client_keys { Old.KeySchedule.C13_wait_Finished1? s }

// Helpful refinement within Secret? stating that an index is for a PSK.
assume val is_psk: Idx.id -> bool


/// To be aligned with Transcript.
///
/// Different flavors of retry info, with precise ClientHello for
/// clients and just the hash for stateless servers.

type client_retry_info = {
  ch0: HSM.ch;
  sh0: HSM.valid_hrr; }

type full_offer = {
  full_retry: option client_retry_info;
  full_ch: HSM.ch; // not insisting that ch initially has zeroed binders
  }

type offer = {
  hashed_retry: option Transcript.retry;
  ch: HSM.ch; // not insisting that ch initially has zeroed binders
  }

// see also Transcript.g_transcript_n
let trans (n:nat) = tr: Transcript.transcript_t { Transcript.transcript_size tr <= n }

// not so useful?
let ch_digest ha (ch: HSM.ch) = Transcript.(transcript_hash ha (ClientHello None ch))

/// Ghost function, used for witnessing the more detailed view of the
/// retry held by the client and by the initial server who issued the
/// hrr. As a corollary of Transcript CRF-based injectivity, and in
/// conjunction with [hashed], we obtain unicity of the initial
/// ClientHello.

#push-options "--z3rlimit 32" // what makes it so slow?
let retry_info_digest (r:client_retry_info): GTot Transcript.retry =
  let ha = HSM.hrr_ha r.sh0 in
  let th = Transcript.transcript_hash ha (Transcript.ClientHello None r.ch0) in
  HSM.M_message_hash (Bytes.hide th), r.sh0

let retry_digest o =
  match o with
  | None -> None
  | Some x -> Some (retry_info_digest x)

/// Stateful implementation? As discussed, we need a new Transcript
/// transition ClientHello None ch0 --hrr--> Start (Some (digest_retry
/// {ch0 = ch0; sh0=hrr})). Here is the spec

val extend_hrr
  (#ha:_)
  (sending: Send.send_state)
  (di:Transcript.state ha)
  (retry: client_retry_info) (* its ch0 could be ghost *)
  (msg: HSM.handshake13)
  (tx0: Ghost.erased Transcript.transcript_t):
  ST (result (tx1: Ghost.erased Transcript.transcript_t))
  (requires fun h0 ->
    let tx0 = Ghost.reveal tx0 in
    ha == HSM.hrr_ha retry.sh0 /\
    tx0 == Transcript.ClientHello None retry.ch0 /\
    B.loc_disjoint (Send.footprint sending) (Transcript.footprint di) /\
    Send.invariant sending h0 /\
    Transcript.invariant di tx0 h0)
  (ensures fun h0 r h1 ->
    B.(modifies (Send.footprint sending `B.loc_union` Transcript.footprint di) h0 h1) /\
    Send.invariant sending h1 /\ (
    match r with
    | Error _ -> True
    | Correct tx1 ->
      let tx1 = Ghost.reveal tx1 in
      // enabling ch0 CRF-based injectivity:
      Transcript.hashed ha (Transcript.ClientHello None retry.ch0) /\
      Transcript.invariant di tx1 h1 /\
      tx1 == Transcript.Start(Some (retry_info_digest retry))))

// let hash_retry (o: option client_retry_info) : option Transcript.retry =
//   match o with
//   | None -> None
//   | Some x ->
//     let ha = HSM.hrr_ha x.sh0 in
//     let tag = admit() in //ch_digest ha x.ch0 in
//     Some (HSM.M_message_hash tag, x.sh0)

// detail: those two may also return lists
assume val offered_shares: HSM.ch -> option Extensions.keyShareClientHello
assume val offered_psks: HSM.ch -> option Extensions.offeredPsks

/// certificate-based credentials (server-only for now)

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

let offered0 (cfg:client_config) (offer:Negotiation.offer) =
  let ks = offered_shares offer in
  let now = deobfuscate offer (snd cfg) in
  let random = offer.Parsers.ClientHello.random in
  Correct offer == Negotiation.client_offer cfg random ks now

let offered (cfg:client_config) (offer:full_offer) =
  let ch = offer.full_ch in
   match offer.full_retry with
  | None -> offered0 cfg ch
  | Some retry ->
    let ks1 = offered_shares ch in
    let now1 = deobfuscate ch (snd cfg) in
    offered0 cfg retry.ch0
    // TBC Negotiation: /\
    // digest_ch0 = hash (selected_hashAlg hrr) offer0 /\
    // Correct offer == Negotiation.client_retry cfg offer0 ks now

let accepted
  (cfg:_) // avoid? unimportant
  (prior: option Transcript.retry)
  (offer: Negotiation.offer)
  (sh: HSM.sh) // refined to exclude HRR
  (ee: Parsers.EncryptedExtensions.encryptedExtensions) =
  Negotiation.client_accept_ServerHello cfg offer sh
  // TBC Negotiation:
  // missing the late processing of encrypted extensions and its callback.

  // what's actually computed and may be worth caching:
  // pv cs resume? checkServerExtensions? pski

// TBC
assume val accepted13: (cfg: client_config) -> full_offer -> sh13 -> Type0
// let accepted13 (cfg: client_config) (o:full_offer) (sh:serverHello) =

assume val client_complete: full_offer -> sh13 -> HSM.encryptedExtensions -> serverCredentials -> Type0

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

// Will replace both [machineState] and [hs] in Old.Handshake.
//
// Compared to the old state machine, we can compute a tag from the
// current transcript, so there is less need to precompute and store
// such tags.

/// Stateful parts shared between all states after CH.
///
noeq type msg_state' (region: rgn) (inflight: PF.in_progress_flt_t) random ha  = {
  digest: Transcript.state ha;
  sending: TLS.Handshake.Send.send_state;
  receiving: Rcv.(r:state { PF.length_parsed_bytes r.pf_st == 0 \/ in_progress r == inflight });
  epochs: Old.Epochs.epochs region random; }
// TODO add regional refinements

let msg_state (region: rgn) (inflight: PF.in_progress_flt_t) random ha  =
  ms:msg_state' region inflight random ha{
     B.loc_disjoint (Transcript.footprint ms.digest) (TLS.Handshake.Send.footprint ms.sending) /\
     B.loc_disjoint (Transcript.footprint ms.digest) (Rcv.loc_recv ms.receiving) /\
     B.loc_disjoint (TLS.Handshake.Send.footprint ms.sending) (Rcv.loc_recv ms.receiving)
  }

let msg_state_footprint #region #inflight #random #ha (ms:msg_state region inflight random ha) =
  B.loc_union
    (B.loc_union (Transcript.footprint ms.digest) (TLS.Handshake.Send.footprint ms.sending))
    (Rcv.loc_recv ms.receiving)


let create_msg_state (region: rgn) (inflight: PF.in_progress_flt_t) random ha:
  ST (msg_state region inflight random ha)
  (requires fun h0 -> True)
  (ensures fun h0 mst h1 -> True)
=
  // who should allocate this receive buffer?
  let b = admit() in
  let d, _ = Transcript.create region ha in
  { digest = d;
    sending = Send.send_state0;
    receiving = Receive.create b;
    epochs = Old.Epochs.create region random }



/// Computing (ghost) transcripts from the Client state
///
let transcript_tch (offer: full_offer { HSM.ch_bound offer.full_ch}) =
  let ch: HSM.clientHello_with_binders = offer.full_ch in
  Transcript.TruncatedClientHello (retry_digest offer.full_retry) (HSM.clear_binders ch)
let transcript_offer offer =
  Transcript.ClientHello (retry_digest offer.full_retry) offer.full_ch
let transcript13 offer (sh: sh13) rest =
  Transcript.Transcript13 (retry_digest offer.full_retry) offer.full_ch sh rest
let transcript_complete offer sh ee ccv fin1 fin2 eoed =
  let rest: Transcript.(bounded_list HSM.handshake13 max_transcript_size) =
    HSM.M13_encrypted_extensions ee ::
    (match ccv with Some(c,cv) -> [HSM.M13_certificate c; HSM.M13_certificate_verify cv] | None -> []) @
    (if Bytes.length fin1 = 0 then [] else [HSM.M13_finished fin1]) @
    // TODO add EOED when 0RTT is offered && not is_quic
    (if Bytes.length fin2 = 0 then [] else [HSM.M13_finished fin2]) in
  transcript13 offer sh rest


/// Summary of the negotiated mode for TLS 1.2, similar to our previous Negotiation.mode but more
/// transcript-oriented; still not sufficient to recompute the
/// transcript contents--will be required for TLS 1.2 security.

noeq type mode12 = {
  // currently assigned in [mode] by client_ServerKeyExchange after
  // signature verification; it may be convenient to also keep
  // messages, e.g., ServerKeyExchange and CertificateVerified
  m12_cr: option HSM.certificateRequest12;
  m12_ccv: option (Cert.chain13 & signatureScheme (* redundant but convenient? *));
  // m12_fin1: Ghost.erased finished; // initially empty
  // m12_fin2: Ghost.erased finished; // initially empty
  m12_ks: client_keys
}

/// Datatype for the handshake-client state machine.
///
/// [region] is used for all handshake state (at least when not model)
/// and in particularity for stashing intermediate data
///
/// [cfg] is the fixed client configuration (maybe stashed later).
///
/// Each state include enough data to reconstruct the transcript
/// currently hashes in the digest, as well as some derived,
/// negotiated parameters, which may in principle be recomputed from
/// the transcript.
///
/// JP: convention is C_ when we don't know yet whether we're doing 12 or 13.
/// C12 / C13 are for when we know which version we've negotiated.

#restart-solver
#set-options "--query_stats"
noeq type client_state
  (region:rgn)
  (cfg: client_config)
=
  // Used only for allocating the client state and binding it to its
  // local nonce in the connection table.
  | C_init:
    // JP: random would be a good candidate to start lowering; this will include
    // conversions with repr.value (), but that's a fixed cost. This will be the
    // first occurrence of a stashed value. Be aware that this will touch a lot
    // of modules, including the connection table and the crypto model.
    random: TLSInfo.random ->
    client_state region cfg

  // Waiting for ServerHello (1.3) or ServerHello...ServerHelloDone
  // (1.2).  This state may be updated after receiving HRR; it is also
  // used (transiently) for witnessing the pre-condition of the binder
  // HMACs, before providing the actual binders; the Handshake
  // invariant (specifying the Transcript state) need not hold in that
  // intermediate state.  The transcript is ..tch, then ..ch; we may
  // need to reallocate the digest in case the server picks another
  // ha.
  | C_wait_ServerHello:
    offer: full_offer { offered cfg offer } ->
    // Witnessed in the binders, then overwritten to add binders or a retry.

    ms: msg_state region PF.F_c_wait_ServerHello (offer.full_ch.HSM.random) (Negotiation.offered_ha offer.full_ch) ->
    ks: c_wait_ServerHello_keys ->
    // JP: this is the crypto-modeling stuff
    // TODO sync key-schedule state
    // ks: secret_c13_wait_ServerHello
    //   (pskis_of_psks (offered_psks offer.full_ch))
    //   (groups_of_ks (offered_shares offer.full_ch)) ->
    // keeping the associated infos, master secrets, and exponents
    client_state region cfg

  // Waiting for encrypted handshake (1.3). The optional binders
  // are now ghost, and the transcript now uses the hash algorithm
  // chosen by the server.
  // The transcript is ..SH; its digest now uses the server's ha.
  | C13_wait_Finished1:
    offer: full_offer{ offered cfg offer } ->
    sh: sh13{ accepted13 cfg offer sh (* not yet authenticated *) } ->
    ms: msg_state region PF.F_c13_wait_Finished1 (offer.full_ch.HSM.random) (Negotiation.selected_ha sh) ->
    ks: c13_wait_Finished1_keys ->
    // TODO sync key-schedule state
    //i:   Secret.hs_id ->
    //ams: Secret.ams (Secret.ams_of_hms i) ->
    //cfk: Secret.fink (Secret.cfk_of_hms i) ->
    //sfk: Secret.fink (Secret.sfk_of_hms i) ->
    client_state region cfg

  // Waiting for post-handshake messages (1.3; TBC rekeying);
  // also used for witnessing the pre-condition of the client finished
  // HMAC (and the client signature TBC) in which case fin2 is not yet
  // set & included in the transcript; we also remain in that state as
  // we receive tickets.
  // The transcript is ..Fin1 then ..Fin2.
  | C13_complete:
    offer: full_offer{ offered cfg offer } ->
    sh: sh13{ accepted13 cfg offer sh } ->
    ee: HSM.encryptedExtensions ->
    server_id: serverCredentials ->
    fin1: Ghost.erased HSM.finished -> (* received from the server *)
    fin2: Ghost.erased HSM.finished (* sent by the client *)
    // We keep the (ghost, high-level) finished messages only to specify the
    // transcript for the client_invariant below (in turn needed by
    // HSL.Transcript.invariant).
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

    ms: msg_state region PF.F_c13_wait_Finished1 (offer.full_ch.HSM.random) (Negotiation.selected_ha sh) ->
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
//
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

  //
  // STATES FOR TLS 1.2 -- comment out for proof experiments.
  //
  // In the TLS 1.2 states below, using [mode] as a placeholder for the final mode,
  // but it may be better to recompute its contents on the fly from ch sh etc.
  //
  // still missing below Rcv.receive_state and HSL.Send.send_state.

  // 1.2 full, waiting for the rest of the first server flight
  | C12_wait_ServerHelloDone:
    ch: HSM.ch ->
    sh: HSM.sh (*{ accepted12 ch sh }*) ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.HSM.random (Negotiation.selected_ha sh) ->
    ks: client_keys ->
    client_state region cfg

  // 1.2 full
  // the digest[..Finished1] to be MAC-verified in Finished2 will now be computed as it is received
  | C12_wait_Finished2:
    ch: HSM.ch ->
    sh: HSM.sh (*{ accepted12 ch sh }*) ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.HSM.random (Negotiation.selected_ha sh) ->
    m:mode12 ->
    // collapsing into a single state [wait_CCS2 (true)] followed by [wait_Finished2 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript
    wait_CCS2: bool ->
    client_state region cfg

  // 1.2 resumption, waiting for the server CCS1 and Finished1
  // we used to pass a digest, but the caller can now recompute it as it receives Finished1
  // we will need digests before (to verify it) and after (for keying)
  | C12_wait_Finished1:
    ch: HSM.ch ->
    sh: HSM.sh (*{ accepted12 ch sh }*) ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.HSM.random (Negotiation.selected_ha sh) ->
    mode12 ->
    // collapsing into a single state [wait_CCS1 (true)] followed by [wait_Finished1 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript
    wait_CCS1: bool ->
    client_state region cfg

  | C12_complete: // now with fin2 and stronger properties
    ch: HSM.ch ->
    sh: HSM.sh (*{ accepted12 ch sh }*) ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.HSM.random (Negotiation.selected_ha sh) ->
    mode12 ->
    client_state region cfg


/// We embed in the type above various refinements for functional
/// properties and witnessed properties, but we also need monotonic
/// properties and a stateful invariant.

//19-07-19 TODO collect invariant for the sending, receiving, and
//keying parts of the state.

let client_footprint
  (#region:rgn) (#cfg: client_config)
  (state: client_state region cfg)
=
  match state with
  | C_init _ -> B.loc_none
  | C_wait_ServerHello _ ms ks -> msg_state_footprint ms
  | C13_complete _ _ _ _ _ _ _ ms ks -> msg_state_footprint ms

  | _ -> B.loc_none  // TODO: Complete this

let client_invariant
  (#region:rgn) (#cfg: client_config)
  (state: client_state region cfg)
  (h: HS.mem)
=
  match state with
  | C_init _ -> True

  | C_wait_ServerHello offer ms ks ->
    // JP: the HSL.Transcript invariant is a relation between a heap, a state
    // and a (ghost) transcript. So, we reconstruct the transcript here (because
    // we can always do so) and use it to state the invariant.
    let transcript = Transcript.ClientHello (retry_digest offer.full_retry) offer.full_ch in
    Transcript.invariant ms.digest transcript h /\

    Receive.invariant ms.receiving h

    // KeySchedule.invariant ks h

  | C13_wait_Finished1 offer sh ms ks ->
    // let sh = admit() in // : _ = assume False; sh in // mismatch on transcript refinement
    let transcript = Transcript.Transcript13 (retry_digest offer.full_retry) offer.full_ch sh [] in
    Transcript.invariant ms.digest transcript h
    // KeySchedule.invariant_C13_wait_Finished1 ks

  | C13_complete offer sh ee server_id fin1 fin2 eoed_args ms ks ->
    True // for TCing experiment

  | _ -> False // TBC

/// We define an update condition on the state that encodes the state
/// machine and ensures stability on selected properties of
/// interest. For example, the transcript is monotonic; and
/// Negotiation's offer and mode are SSA.

let client_step
  (#region:rgn) (#cfg: client_config)
  (st0 st1: client_state region cfg)
= //st0 == undo_last_step st1
  match st0, st1 with

  // | Cn x, Cn' x' y' -> x == x'
  | C_init nonce0,
    C_wait_ServerHello offer1 ms1 ks1 -> offer1.full_ch.Parsers.ClientHello.random == nonce0

  | C_wait_ServerHello offer0 ms0 ks0,
    C_wait_ServerHello offer1 ms1 ks1 ->
    // enabling addition of the real binders
    ( offer0.full_retry == offer1.full_retry /\
      offer0.full_ch == HSM.clear_binders offer1.full_ch)  \/
    // enabling addition of a retry; too lax for now
    ( match offer0.full_retry, offer1.full_retry with
      | None, Some hr -> hr.ch0 = offer0.full_ch
      | _ -> False )

  | C_wait_ServerHello offer0 ms0 ks0,
    C13_wait_Finished1 offer1 sh1 ms1 ks1 ->
    offer1 == offer0

  | _, _ -> False // TBC

let client_mrel
  (#region:rgn) (#cfg: client_config) =
  FStar.ReflexiveTransitiveClosure.closure (client_step #region #cfg)

type client_mref rgn cfg =
  st:HST.mreference (client_state rgn cfg) (client_mrel #rgn #cfg)
  { HS.frameOf st = rgn }


/// ----------------------------------------------------------------
/// sample monotonic properties: the initial and retried ClientHello
/// messages are both stable once defined, except for their binders.
/// (We will add other similar, single-static-assignments properties.)

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

// reading the initial client hello, once defined.
let st_ch0 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with
  | C_init _ -> None
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> (
    match offer.full_retry with
    | None    -> Some (HSM.clear_binders offer.full_ch)
    | Some hr -> Some (HSM.clear_binders hr.ch0) )

  | _ -> None // TBC 1.2

// reading the second client hello, once defined
let st_ch1 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with
  | C_init _ -> None
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> (
    match offer.full_retry with
    | None    -> None
    | Some _  -> Some (HSM.clear_binders offer.full_ch) )

  | _ -> None // TBC 1.2

// as a counter-example, this property is not stable:
let st_ch (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with
  | C_init _ -> None
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> Some (HSM.clear_binders offer.full_ch)
  | _ -> None // TBC 1.2

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
  st1:client_state region cfg -> Lemma (client_step st0 st1 ==> ssa f st0 st1)

// 19-09-05 broken by adding clear_binders? The proof now depends on it being idempotent.
#push-options "--admit_smt_queries true"

// Via the type above, m_ch0 is a relation between two states...
let m_ch0: st_mon st_ch0 = fun _ _ _ _ -> ()
let m_ch1: st_mon st_ch1 = fun _ _ _ _ -> ()
// expected to fail
//let m_ch: st_mon st_ch = fun _ _ _ _ -> ()

/// Testing monotonicity, relying on the new closure library; we could
/// probably do it more parametrically to scale up.

let assigned_to #region #cfg (st:client_mref region cfg) f (o:Negotiation.offer) h0 =
  f (HS.sel h0 st) == Some o

// ... intuitively, witness0 gives the stateful equivalent of m_ch0 with the
// monotonicity property exposed in the post-condition.
val witness0 (#region:rgn) (#cfg:client_config) (st:client_mref region cfg):
  Stack HSM.ch
    (requires fun h0 -> match HS.sel h0 st with
        | C_wait_ServerHello _ _ _
        | C13_wait_Finished1 _ _ _ _
        | C13_complete _ _ _ _ _ _ _ _ _ -> h0 `HS.contains` st
        | _ -> False )
    (ensures fun h0 o h1 ->
      token_p st (st_ch0 `(assigned_to st)` o) /\
      modifies_none h0 h1)

#push-options "--z3rlimit 100" // NS: wow, that's a lot for a little proof
let witness0 (#region:rgn) (#cfg:client_config) (st:client_mref region cfg) =
  match st_ch0 !st with
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure
        (client_step #region #cfg)
        (fun st -> st_ch0 st == Some o) ();
      witness_p st (assigned_to #region st st_ch0 o);
      o )
#pop-options

val witness1 (#region:rgn) (#cfg:client_config) (st:client_mref region cfg):
  Stack HSM.ch
    (requires fun h0 ->
      h0 `HS.contains` st /\
      ( match HS.sel h0 st with
        | C_wait_ServerHello offer _ _
        | C13_wait_Finished1 offer _ _ _
        | C13_complete offer _ _ _ _ _ _ _ _ -> Some? offer.full_retry
        | _ -> False ))
    (ensures fun h0 o h1 ->
      token_p st (assigned_to st st_ch1 o) /\
      modifies_none h0 h1)

#push-options "--z3rlimit 100" // NS: wow, that's a lot for a little proof
let witness1 #region #cfg st =
  match st_ch1 !st with
  | Some o -> (
      ReflexiveTransitiveClosure.stable_on_closure
        (client_step #region #cfg)
        (fun st -> st_ch1 st == Some o) ();
      witness_p st (assigned_to #region st st_ch1 o);
      o )
#pop-options

assume val stuff (#region:rgn) (#cfg:client_config) (st: client_mref region cfg): Stack unit
  (requires fun h0      -> h0 `HS.contains` st)
  (ensures  fun h0 _ h1 -> h1 `HS.contains` st)

let test (#region:rgn) (#cfg:client_config) (st: client_mref region cfg):
  Stack unit
    (requires fun h0 -> h0 `HS.contains` st)
    (ensures fun h0 _ h1 -> True)
=
  let r = st_ch1 !st in
  if Some? r then
    let o = witness1 st in
    stuff st;
    let r' = st_ch1 !st in
    recall_p st (assigned_to st st_ch1 o);
    assert(r' == Some o)

#pop-options

/// -------------end of sanity check----------------

#restart-solver

/// Starting to port the auxiliary accessors previously defined and
/// used in Old.Handshake; many of them could often be shown to be
/// monotonic. We will need more to cut direct dependencies on [mode].

//#set-options "--max_ifuel 2 --z3rlimit 20 --query_stats"
let client_nonce (#region:rgn) (#cfg:client_config) (s:client_state region cfg) =
  //allow_inversion (client_state region cfg);
  match s with
  | C_init random -> random
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ _ _ -> offer.full_ch.HSM.random
  | C12_wait_ServerHelloDone ch _ _ _
  | C12_wait_Finished2 ch _ _ _ _
  | C12_wait_Finished1 ch _ _ _ _
  | C12_complete ch _ _ _ -> ch.HSM.random

let random_of #region #cfg (s:client_state region cfg) = client_nonce s

let client_epochs_of (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}):
  Old.Epochs.epochs region (client_nonce s)
=
 match s with
  | C_wait_ServerHello _ ms _
  | C13_wait_Finished1 _ _ ms _
  | C13_complete _ _ _ _ _ _ _ ms _
  | C12_wait_ServerHelloDone _ _ ms _
  | C12_wait_Finished2 _ _ ms _ _
  | C12_wait_Finished1 _ _ ms _ _
  | C12_complete _ _ ms _ -> ms.epochs



                          (* SERVER SIDE *)

type server_config = config // TBC

//TODO share with Transcript
type server_retry_info = digest0: bytes & HSM.valid_hrr
type s_offer = {
  retry: option server_retry_info;
  ch: HSM.ch; }

// Complete mode for the connection; sufficient to derive all the
// negotiated connection parameters, and shared between clients and
// servers when the connection is safe.
//
// As a technicality, it includes only the *tag* supposed to be the
// hash of the initial offer after a retry.

assume val selected:
  server_config ->
  s_offer ->
  HSM.sh ->
  HSM.encryptedExtensions ->
  option HandshakeMessages.certificate13 -> Type

noeq type s13_mode (region:rgn) (cfg:server_config) = {
  offer: s_offer; (* { honest_psk offer ==> client_offered offer } *)
  sh: sh13;
  ee: HSM.encryptedExtensions;
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
    ms: msg_state region PF.F_c_wait_ServerHello (mode.offer.ch.HSM.random) (Negotiation.selected_ha mode.sh) ->
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
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->
    fin1: Ghost.erased HSM.finished ->
    ms: msg_state region PF.F_c_wait_ServerHello (mode.offer.ch.HSM.random) (Negotiation.selected_ha mode.sh) ->
    // ms.digest is expected to be MACed in the Client Finished
    ks: server_keys -> // keeping fin2key and rms
    server_state region cfg

  | S13_complete:
    mode: s13_mode region cfg ->
    ssv: Ghost.erased HandshakeMessages.certificateVerify13 ->
    fin1: Ghost.erased HSM.finished ->
    fin2: Ghost.erased HSM.finished ->
//  { client_complete mode } ->
    ms: msg_state region PF.F_c_wait_ServerHello (mode.offer.ch.HSM.random) (Negotiation.selected_ha mode.sh) ->
    ks: server_keys ->
    server_state region cfg

 //| S_wait_CCS1                // TLS classic
//| S_wait_Finished1 of digest // TLS classic, digest to the MACed by client
//| S_wait_CCS2 of digest      // TLS resume (CCS)
//| S_wait_CF2 of digest       // TLS resume (CF)
//| S_Complete


let server_step
  (#region:rgn) (#cfg: server_config)
  (st0 st1: server_state region cfg)
= True // TODO

let server_mrel (#region:rgn) (#cfg: server_config) =
  FStar.ReflexiveTransitiveClosure.closure (server_step #region #cfg)

type server_mref rgn cfg =
  st:HST.mreference (server_state rgn cfg) (server_mrel #rgn #cfg)
  { HS.frameOf st = rgn }

let server_invariant #region #config (ss: server_state region config) h = True

assume val server_nonce (#region:rgn) (#cfg:server_config) (s:server_state region cfg): TLSInfo.random

assume val server_epochs_of (#region:rgn) (#cfg:server_config) (s:server_state region cfg):
  Old.Epochs.epochs region (server_nonce s)

                              (* API *)

/// We finally define our main (refined, monotonic, stateful) type for connection handshakes

noeq type state =
  | Client:
    client_rgn: rgn ->
    client_cfg: client_config ->
    client_state: client_mref client_rgn client_cfg -> state

  | Server:
    server_rgn: rgn ->
    server_cfg: server_config ->
    server_state: server_mref server_rgn server_cfg -> state

let nonceT s h =
  match s with
  | Client region config r -> client_nonce (HS.sel h r)
  | Server region config r -> server_nonce (HS.sel h r)


let invariant s h =
  match s with
  | Client region config r -> client_invariant (HS.sel h r) h
  | Server region config r -> server_invariant (HS.sel h r) h

let frame s = match s with
  | Client rgn _ _
  | Server rgn _ _ -> rgn

assume val epochsT (s:_) (h:_): Old.Epochs.epochs (frame s) (nonceT s h)


let state_entry (n: TLSInfo.random) = state // TODO refinement witness reading stable n

/// TODO
/// - define a model-only global table from disjoint nonces to those connections.
/// - define a constructor adding a model-only nonce value and
///   witnessing its table registration. This is the main connection
///   type at the API.

type client = s:state {Client? s}
type server = s:state {Server? s}

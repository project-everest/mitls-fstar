module TLS.Handshake.Machine

/// The verified state machine for the Handshake, integrating state,
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

// v1: support for TLS 1.2 is disabled.

open Mem
open TLS.Result
open TLSInfo
open TLSConstants

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module Msg = HandshakeMessages
module KS = Old.KeySchedule
module Epochs = Old.Epochs

module LP = LowParse.Low.Base
//let make_slice = LowParse.Low.Base.make_slice

module PF = TLS.Handshake.ParseFlights // only for flight names
module Recv = TLS.Handshake.Receive
module Send = TLS.Handshake.Send

// [msg_state] holds state for {Send, Recv, Transcript, Epochs}
open TLS.Handshake.Messaging

/// Auxiliary datatypes (shared between machine states)
///
/// Each Handshake state embeds the state of other handshake modules
/// in state-passing style, as follows. (As we verify more, we may use
/// more precise, state-specific types for them.)
///
/// * It is parameterized by a region and a configuration.

// TLS.Config will define a more convenient client-specific configuration
let client_config = Negotiation.client_config


/// * Old.KeySchedule: most state keep either ks_client_state or
///   ks_server_state (usually with a refinement for its known
///   constructor).
///
///   We should start thinking about their invariants and footprints,
///   subject to conditional idealization.

let client_keys = KS.ks_client
let c_wait_ServerHello_keys = s:client_keys{ KS.C_wait_ServerHello? s }
let c13_wait_Finished1_keys = s:client_keys{ KS.C13_wait_Finished1? s }
let c13_wait_Finished2_keys = s:client_keys{ KS.C13_wait_Finished2? s }
let c13_complete_keys       = s:client_keys{ KS.C13_Complete? s }

let server_keys = KS.ks_server
let s13_wait_ServerHello_keys    = s:server_keys{ KS.S13_wait_SH? s }
let s13_wait_ServerFinished_keys = s:server_keys{ KS.S13_wait_SF? s }
let s13_wait_ClientFinished_keys = s:server_keys{ KS.S13_wait_CF? s }
let s13_complete_keys            = s:server_keys{ KS.S13_postHS? s }

// Helpful refinement within Secret? stating that an index is for a PSK.
assume val is_psk: Idx.id -> bool

/// From Handshake.Secret, indexing TBC; for now we omit their
/// (opaque) part of the state. Unused?

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


/// Different flavors of retry info, includiing the full ClientHello
/// for clients and just its hash for stateless servers.
///
/// These definitions could go to Transcript.

type client_retry_info = {
  ch0: Msg.ch;
  sh0: Msg.valid_hrr;
}

type full_offer = {
  full_retry: option client_retry_info;
  full_ch: Msg.ch; // not insisting that ch initially has zeroed binders
}

type offer = {
  hashed_retry: option Transcript.retry;
  ch: Msg.ch; // not insisting that ch initially has zeroed binders
}

//NS: Is this abbreviation really necessary?
//Transcript.transcript_n is similar but provides an equality rather than [<=]
let trans (n:nat) = tr: Transcript.transcript_t { Transcript.transcript_size tr <= n }

// not so useful?
let ch_digest ha (ch: Msg.ch) = Transcript.transcript_hash ha (Transcript.ClientHello None ch)

/// Ghost function, used for witnessing the more detailed view of the
/// retry held by the client and by the initial server who issued the
/// hrr. As a corollary of Transcript CRF-based injectivity, and in
/// conjunction with [hashed], we obtain unicity of the initial
/// ClientHello.

#push-options "--z3rlimit 32" // what makes it so slow?
let retry_info_digest (r:client_retry_info): GTot Transcript.retry =
  let ha = Msg.hrr_ha r.sh0 in
  let th = Transcript.transcript_hash ha (Transcript.ClientHello None r.ch0) in
  Msg.M_message_hash (Bytes.hide th), r.sh0

let retry_digest o =
  match o with
  | None -> None
  | Some x -> Some (retry_info_digest x)

// let hash_retry (o: option client_retry_info) : option Transcript.retry =
//   match o with
//   | None -> None
//   | Some x ->
//     let ha = Msg.hrr_ha x.sh0 in
//     let tag = admit() in //ch_digest ha x.ch0 in
//     Some (Msg.M_message_hash tag, x.sh0)

/// Certificate-based credentials (for now only to identify the server)

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


/// Main negotiation properties, witnessed before MACing/signing for
/// mutual authenticating between connection peers.

// [offered] is the negotiation property authenticated by the client binders.
//
// TBC re: prior consistency; we probably need to branch as only the
// initial offer is a function of the config.

let offered0 (cfg:client_config) (offer:Negotiation.offer) =
  let ks = Negotiation.find_clientKeyShares offer in
  let now = deobfuscate offer (snd cfg) in
  let random = offer.Parsers.ClientHello.random in
  Correct offer == Negotiation.client_offer cfg random ks now

let offered (cfg:client_config) (offer:full_offer) =
  let ch = offer.full_ch in
   match offer.full_retry with
  | None -> offered0 cfg ch
  | Some retry ->
    let ks1 = Negotiation.find_clientKeyShares ch in
    let now1 = deobfuscate ch (snd cfg) in
    offered0 cfg retry.ch0
    // TBC Negotiation: /\
    // digest_ch0 = hash (selected_hashAlg hrr) offer0 /\
    // Correct offer == Negotiation.client_retry cfg offer0 ks now

let accepted
  (cfg:_) // avoid? unimportant
  (prior: option Transcript.retry)
  (offer: Negotiation.offer)
  (sh: Msg.sh) // refined to exclude HRR
  (ee: Parsers.EncryptedExtensions.encryptedExtensions) =
  Negotiation.client_accept_ServerHello cfg offer sh
  // TBC Negotiation:
  // missing the late processing of encrypted extensions and its callback.

  // what's actually computed and may be worth caching:
  // pv cs resume? checkServerExtensions? pski

assume val accepted13:
  (cfg: client_config) ->
  full_offer ->
  Transcript.sh13 ->
  Type0
// let accepted13 (cfg: client_config) (o:full_offer) (sh:serverHello) =

assume val client_complete: full_offer -> Transcript.sh13 -> Msg.encryptedExtensions -> serverCredentials -> Type0


/// Sub-states of C13_Complete to account for EOED and Fin2 being sent.
// Is it really worth merging wait_CF and complete in a single state?
// To be reviewed (Cedric thinks yes, Antoine thinks no - we are still
// missing client auth with an additional sub-state.)
noeq type client13_finished_state ch sh ee server_id =
| Finished_pending:
  cfk: (i:_ & KS.fink i) ->
  ks: c13_wait_Finished2_keys ->
  eoed_sent: bool{True (* not (offered_0rtt ch) ==> not eoed *)} ->
  client13_finished_state ch sh ee server_id
| Finished_sent:
  fin2: Ghost.erased Msg.finished { client_complete ch sh ee server_id } ->
  ks: c13_complete_keys ->
  client13_finished_state ch sh ee server_id




/// State machine for the connection handshake (private to Handshake).
/// Each role now has its own type.
///
/// Low*: we'll turn all high-level messages constructor arguments
/// into ghost, possibly using reprs.

// Compared to the old state machine, we can compute a tag from the
// current transcript, so there is less need to precompute and store
// such tags.


/// Computing (ghost) transcripts from machine states; these nested
/// specifications are enforced by in the stateful machine invariant,
/// and used to relate signed digests to the handshake state.

let transcript_tch (offer: full_offer { Msg.ch_bound offer.full_ch}) =
  let ch: Msg.clientHello_with_binders = offer.full_ch in
  Transcript.TruncatedClientHello (retry_digest offer.full_retry) (Msg.clear_binders ch)

let transcript_offer offer =
  Transcript.ClientHello (retry_digest offer.full_retry) offer.full_ch

let transcript13 offer (sh: Transcript.sh13) rest =
  Transcript.Transcript13 (retry_digest offer.full_retry) offer.full_ch sh rest

let transcript13_complete offer sh ee ccv fin1 (substate: client13_finished_state offer sh ee ccv) =
  let rest: Transcript.bounded_list Msg.handshake13 Transcript.max_transcript_size =
    Msg.M13_encrypted_extensions ee ::
    (match ccv with Some(c,cv) -> [Msg.M13_certificate c; Msg.M13_certificate_verify cv] | None -> []) @
    (if Bytes.length fin1 = 0 then [] else [Msg.M13_finished fin1]) @
    // TODO we should know whether EOED has been sent or not (when 0RTT is offered && not is_quic)
    (match substate with
    | Finished_pending _ _ b -> if b then [Msg.M13_end_of_early_data ()] else []
    | Finished_sent fin2 _ -> [Msg.M13_finished fin2]) in
  transcript13 offer sh rest


/// Summary of the negotiated mode for TLS 1.2, similar to our previous Negotiation.mode but more
/// transcript-oriented; still not sufficient to recompute the
/// transcript contents--will be required for TLS 1.2 security.

noeq type mode12 = {
  // currently assigned in [mode] by client_ServerKeyExchange after
  // signature verification; it may be convenient to also keep
  // messages, e.g., ServerKeyExchange and CertificateVerified
  m12_cr: option Msg.certificateRequest12;
  m12_ccv: option (Cert.chain13 & signatureScheme (* redundant but convenient? *));
  // m12_fin1: Ghost.erased finished; // initially empty
  // m12_fin2: Ghost.erased finished; // initially empty
  m12_ks: client_keys
}

    // TLS 1.3 #20 aggravation: optional intermediate model-irrelevant
    // EOED between C13_wait_Finished1 and C13_complete, with
    // transcript [..fin1 EOED]. We add an optional parameter to track
    // it, just making fin2 optional or empty in C13_complete;
    // Old.Handshake currently holds [digestEOED ocr cfin_key] in that
    // state to complete the transaction after installing the new
    // keys.


/// Main datatype for the handshake-client state machine.
///
/// [region] includes the footprint of all handshake state for the
/// connection (at least when not model) and in particular its stash
/// of allocated data.
///
/// [cfg] is the fixed client configuration (maybe stashed later).
///
/// Each state include enough data to reconstruct the transcript
/// currently hashes in the digest, as well as some derived,
/// negotiated parameters, which may in principle be recomputed from
/// the transcript.
///
/// JP: global handshake convention is C_ when we don't know yet
/// whether we're doing 12 or 13.  C12 / C13 are for when we know
/// which version we've negotiated.

//#set-options "--query_stats"
noeq type client_state
  (region:rgn)
  (cfg: client_config)
=
  // Initial state, used for allocating the client state and binding
  // it to its local nonce in the connection table.
  | C_init:
    // JP: random would be a good candidate to start lowering; this will include
    // conversions with repr.value (), but that's a fixed cost. This will be the
    // first occurrence of a stashed value. Be aware that this will touch a lot
    // of modules, including the connection table and the crypto model.
    random: TLSInfo.random ->
    client_state region cfg

  // Waiting for ServerHello (1.3) or ServerHello...ServerHelloDone (1.2).
  // This state may be updated after receiving HelloRetryRequestRR;
  // This state is also updated (transiently) for witnessing the pre-condition of
  // the binder MACs, before providing the actual binders; the
  // Handshake invariant (specifying the Transcript state) need not
  // hold in that intermediate state.
  // The transcript is [..tch] then [..ch] with subcases depending on HRR.
  // We may need to reallocate the digest in case the server picks another ha.
  | C_wait_ServerHello:
    offer: full_offer { offered cfg offer } ->
    // Witnessed in the binders, then overwritten to add binders or a retry.

    ms: msg_state region PF.F_c_wait_ServerHello (offer.full_ch.Msg.random) (Negotiation.offered_ha offer.full_ch) ->
    ks: c_wait_ServerHello_keys ->
    // JP: this is the crypto-modeling stuff
    // TODO sync key-schedule state
    // ks: secret_c13_wait_ServerHello
    //   (pskis_of_psks (offered_psks offer.full_ch))
    //   (groups_of_ks (offered_shares offer.full_ch)) ->
    // keeping the associated infos, master secrets, and exponents
    client_state region cfg

  // Waiting for the encrypted handshake flight (1.3).
  // The transcript is [..sh] and its digest now uses the hash
  // algorithm chosen by the server.
  | C13_wait_Finished1:
    offer: full_offer{ offered cfg offer } ->
    sh: Transcript.sh13{ accepted13 cfg offer sh (* not yet authenticated *) } ->
    ms: msg_state region PF.F_c13_wait_Finished1 (offer.full_ch.Msg.random) (Negotiation.selected_ha sh) ->
    ks: c13_wait_Finished1_keys ->
    client_state region cfg

  // Waiting for post-handshake messages (1.3; TBC rekeying).
  // This state is first written (transiently) with a dummy Finished1
  // for witnessing the precondition of the Client finished (and the
  // client signature TBC), then updated with the resulting tag.
  // This state is updated after verifying the Server finished.
  // We remain in the resulting final state as we receive tickets.
  // The (stable) transcript is [..Finished1] then [..Finished2].
  | C13_complete:
    offer: full_offer{ offered cfg offer } ->
    sh: Transcript.sh13{ accepted13 cfg offer sh } ->
    ee: Msg.encryptedExtensions ->
    server_id: serverCredentials ->
    fin1: Ghost.erased Msg.finished ->
    ms: msg_state region PF.F_c13_wait_Finished1 (offer.full_ch.Msg.random) (Negotiation.selected_ha sh) ->
    fin_state: client13_finished_state offer sh ee server_id ->
    client_state region cfg
    // let client_complete offer sh ee svn =
    //   client_offered cfg offer /\
    //   client_accepted13 offer sh /\
    //   client_verified13 offer sh ee svc /\
    //   (honest_server sh ... ==> server_selected13 offer sh ee svc)

  //
  // STATES FOR TLS 1.2 -- comment out for proof experiments.
  //
  // In the TLS 1.2 states below, using [mode] as a placeholder for the final mode,
  // but it may be better to recompute its contents on the fly from ch sh etc.
  //
  // still missing below Recv.receive_state and HSL.Send.send_state.

  // 1.2 resumption, waiting for the server CCS1 and Finished1
  // we used to pass a digest, but the caller can now recompute it as it receives Finished1
  // we will need digests before (to verify it) and after (for keying)
  | C12_wait_Finished1:
    ch: Msg.ch ->
    sh: Transcript.sh12 ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.Msg.random (Negotiation.selected_ha sh) ->
    ks: client_keys { KS.C12_has_MS? ks } ->
    mode12 ->
    // collapsing into a single state [wait_CCS1 (true)] followed by [wait_Finished1 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript
    wait_CCS1: bool ->
    client_state region cfg

  // 1.2 full, waiting for the rest of the first server flight
  // No key schedule state created yet
  | C12_wait_ServerHelloDone:
    ch: Msg.ch ->
    sh: Transcript.sh12 ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.Msg.random (Negotiation.selected_ha sh) ->
    client_state region cfg

  // 1.2 full
  // the digest[..Finished1] to be MAC-verified in Finished2 will now be computed as it is received
  | C12_wait_Finished2:
    ch: Msg.ch ->
    sh: Transcript.sh12 ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.Msg.random (Negotiation.selected_ha sh) ->
    ks: client_keys{KS.C12_has_MS? ks \/ KS.C12_wait_MS? ks} ->
    m:mode12 ->
    // collapsing into a single state [wait_CCS2 (true)] followed by [wait_Finished2 (false)]
    // no need to track missing fin messages, as they are used just for recomputing the transcript
    wait_CCS2: bool ->
    client_state region cfg

  | C12_complete: // now with fin2 and stronger properties
    ch: Msg.ch ->
    sh: Transcript.sh12 ->
    ms: msg_state region PF.F_c12_wait_ServerHelloDone ch.Msg.random (Negotiation.selected_ha sh) ->
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
  | C13_complete _ _ _ _ _ ms _ -> msg_state_footprint ms
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
    let transcript = transcript_offer offer in
    msg_invariant ms transcript h
    // KeySchedule.invariant ks h

  | C13_wait_Finished1 offer sh ms ks ->
    // let sh = admit() in // : _ = assume False; sh in // mismatch on transcript refinement
    let transcript = transcript13 offer sh [] in
    msg_invariant ms transcript h
    // KeySchedule.invariant_C13_wait_Finished1 ks

  | C13_complete offer sh ee server_id fin1 ms sub_state ->
    let transcript = transcript13_complete offer sh ee server_id fin1 sub_state in
    msg_invariant ms transcript h

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
      offer0.full_ch == Msg.clear_binders offer1.full_ch)  \/
    // enabling addition of a retry; too lax for now
    ( match offer0.full_retry, offer1.full_retry with
      | None, Some hr -> hr.ch0 = offer0.full_ch
      | _ -> False )

  | C_wait_ServerHello offer0 ms0 ks0,
    C13_wait_Finished1 offer1 sh1 ms1 ks1 ->
    offer1 == offer0

  (* Sub state-machine for sending EOED and finished *)
  | C13_complete offer0 sh0 ee0 sid0 fin0 ms0 sub0,
    C13_complete offer1 sh1 ee1 sid1 fin1 ms1 sub1 ->
    offer1 == offer0 /\ sh1 == sh0 /\ ee1 == ee0 /\ sid1 == sid0 /\ fin1 == fin0 /\
    (match sub0, sub1 with
    | Finished_pending cfk0 ks0 false, Finished_pending cfk1 ks1 true ->
      cfk1 == cfk0 /\ ks1 == ks0
    | Finished_pending _ _ _, Finished_sent fin2 ks -> True
    | _ -> False)
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
  | C13_complete offer _ _ _ _ _ _ -> (
    match offer.full_retry with
    | None    -> Some (Msg.clear_binders offer.full_ch)
    | Some hr -> Some (Msg.clear_binders hr.ch0) )

  | _ -> None // TBC 1.2

// reading the second client hello, once defined
let st_ch1 (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with
  | C_init _ -> None
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ -> (
    match offer.full_retry with
    | None    -> None
    | Some _  -> Some (Msg.clear_binders offer.full_ch) )

  | _ -> None // TBC 1.2

// as a counter-example, this property is not stable:
let st_ch (#region:rgn) (#cfg: client_config) (st: client_state region cfg) =
  match st with
  | C_init _ -> None
  | C_wait_ServerHello offer _ _
  | C13_wait_Finished1 offer _ _ _
  | C13_complete offer _ _ _ _ _ _ -> Some (Msg.clear_binders offer.full_ch)
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
  Stack Msg.ch
    (requires fun h0 -> match HS.sel h0 st with
        | C_wait_ServerHello _ _ _
        | C13_wait_Finished1 _ _ _ _
        | C13_complete _ _ _ _ _ _ _ -> h0 `HS.contains` st
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
  Stack Msg.ch
    (requires fun h0 ->
      h0 `HS.contains` st /\
      ( match HS.sel h0 st with
        | C_wait_ServerHello offer _ _
        | C13_wait_Finished1 offer _ _ _
        | C13_complete offer _ _ _ _ _ _ -> Some? offer.full_retry
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
  | C13_complete offer _ _ _ _ _ _ -> offer.full_ch.Msg.random
  | C12_wait_ServerHelloDone ch _ _
  | C12_wait_Finished2 ch _ _ _ _ _
  | C12_wait_Finished1 ch _ _ _ _ _
  | C12_complete ch _ _ _ -> ch.Msg.random

let client_ha
  (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}):
  Transcript.ha
=
  match s with
  | C_wait_ServerHello offer ms ks -> Negotiation.offered_ha offer.full_ch
  | C13_wait_Finished1 offer sh ms ks -> Negotiation.selected_ha sh
  | C13_complete offer sh _ _ _ _ _ -> Negotiation.selected_ha sh
//| C12_wait_ServerHelloDone _ _ ms _
//| C12_wait_Finished2 _ _ ms _ _
//| C12_wait_Finished1 _ _ ms _ _
//| C12_complete _ _ ms _ -> ms
  | _ -> admit()

let client_flight
  (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}):
  PF.in_progress_flt_t
=
  match s with
  | C_wait_ServerHello offer ms ks        -> PF.F_c_wait_ServerHello
  | C13_wait_Finished1 offer sh ms ks     -> PF.F_c13_wait_Finished1
  | C13_complete offer sh _ _ _ _ _ -> PF.F_c13_wait_Finished1
//| C12_wait_ServerHelloDone _ _ ms _
//| C12_wait_Finished2 _ _ ms _ _
//| C12_wait_Finished1 _ _ ms _ _
//| C12_complete _ _ ms _ -> ms
  | _ -> admit()


// it is awkward to provide generic getters ands setters for ms due to
// its dependencies

type client_ms_t (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}) =
  msg_state region (client_flight s) (client_nonce s) (client_ha s)


let client_ms (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}): client_ms_t s
=
  match s with
  | C_wait_ServerHello _ ms _ -> ms
  | C13_wait_Finished1 _ _ ms _ -> ms
  | C13_complete _ _ _ _ _ ms _ -> ms
  | _ -> admit()
//| C12_wait_ServerHelloDone _ _ ms _ -> ms
//| C12_wait_Finished2 _ _ ms _ _ -> ms
//| C12_wait_Finished1 _ _ ms _ _ -> ms
//| C12_complete _ _ ms _ -> ms

let set_client_ms
  (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)})
  (ms1: client_ms_t s):
  s:client_state region cfg {~(C_init? s)}
=
  match s with
  | C_wait_ServerHello offer ms0 ks ->
    C_wait_ServerHello offer ms1 ks
  | C13_wait_Finished1 offer sh ms0 ks ->
    C13_wait_Finished1 offer sh ms1 ks
  | C13_complete offer sh ee server_id fin1 ms0 ks ->
    C13_complete offer sh ee server_id fin1 ms1 ks
  | _ -> admit()

let client_epochs
  (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}):
  Old.Epochs.epochs region (client_nonce s)
=
  (client_ms s).epochs

let client_sto
  (#region:rgn) (#cfg:client_config) (s:client_state region cfg {~(C_init? s)}):
  Send.send_state
=
  (client_ms s).sending



// 19-09-12 TODO we could return the whole Certificate13 message
// contents; for now we ignore its extensions.
let client_server_certificates (#region:rgn) (#cfg:client_config) (s:client_state region cfg): option Cert.chain13 =
  match s with
  | C13_complete _ _ _ (Some (certs,_)) _ _ _ -> Some certs.Parsers.Certificate13.certificate_list
// TBC TLS 1.2
//| C12_wait_ServerHelloDone _ _ ms _
//| C12_wait_Finished2 _ _ ms _ _
//| C12_complete _ _ ms _ -> ms.epochs
  | _ -> None


                          (* SERVER SIDE *)

type server_config = config // TBC

type s_offer = {
  retry: option Transcript.retry;
  s_ch: Msg.ch;
}

// Complete mode for the connection; sufficient to derive all the
// negotiated connection parameters, and shared between clients and
// servers when the connection is safe.
//
// As a technicality, it includes only the *tag* supposed to be the
// hash of the initial offer after a retry.

// Witness from certificate callback
assume val selected_cert:
  server_config ->
  s_offer ->
  Msg.sh ->
  Msg.encryptedExtensions ->
  TLS.Callbacks.cert_type ->
  Type

// Witness from certificate formatting callback
assume val formatted_cert:
  TLS.Callbacks.cert_type ->
  Msg.certificate13 ->
  Type

// Witness from certificate signing callback
assume val signed_tx:
  s_offer ->
  Msg.sh ->
  Msg.encryptedExtensions ->
  Msg.certificate13 ->
  Msg.certificateVerify13 ->
  Type

type s13_cert_info cfg ch sh ee =
| NoServerCert
| ServerCert:
  pointer: TLS.Callbacks.cert_type{selected_cert cfg ch sh ee pointer} ->
  chain: Msg.certificate13{formatted_cert pointer chain} ->
  verify: Msg.certificateVerify13{signed_tx ch sh ee chain verify} ->
  s13_cert_info cfg ch sh ee

noeq type s13_mode (region:rgn) (cfg:server_config) =
| S13_mode:
  offer: s_offer -> (* { honest_psk offer ==> client_offered offer } *)
  sh: Transcript.sh13 ->
  ee: Msg.encryptedExtensions ->
  cert: s13_cert_info cfg offer sh ee ->
  s13_mode region cfg

// The transcript prefix associated with a mode
let s13_mode_transcript #r #cfg (m:s13_mode r cfg) : Transcript.transcript_t =
  assume false; // bounded_list
  Transcript.Transcript13 m.offer.retry m.offer.s_ch m.sh
    (match m.cert with NoServerCert -> []
    | ServerCert _ chain verify ->
      [Msg.M13_certificate chain;
       Msg.M13_certificate_verify verify])

noeq type server_state
  (region:rgn)
  (cfg:server_config)
  =
  | S_wait_ClientHello:
    random: TLSInfo.random ->
    recv: Recv.(r:state {
      PF.length_parsed_bytes r.pf_st == 0 \/
      in_progress r == PF.F_s_Idle }) ->
    server_state region cfg

  // Stateful HRR
  | S13_sent_HelloRetryRequest:
    random: TLSInfo.random ->
    retry: Transcript.retry ->
    ms: msg_state region PF.F_s_Idle random
      (Negotiation.selected_ha (snd retry)) ->
    server_state region cfg

  // TLS 1.3, intermediate state to encryption
  | S13_sent_ServerHello:
    offer: s_offer ->
    sh: Transcript.sh13 ->
    ee: Msg.encryptedExtensions ->
    accept_0rtt: bool ->
    ms: msg_state region
      (if accept_0rtt then PF.F_s13_wait_EOED else PF.F_s13_wait_Finished2)
      (offer.s_ch.Msg.random) (Negotiation.selected_ha sh) ->
    cert: option Negotiation.cert_choice ->
    ks: s13_wait_ServerFinished_keys ->
    server_state region cfg

  | S13_wait_Finished2:
    mode: s13_mode region cfg ->
    fin1: Ghost.erased Msg.finished ->
    eoed_done: bool{True (*not (accepted_0rtt mode) ==> eoed_done==true*)} ->
    ms: msg_state region
     (if eoed_done then PF.F_s13_wait_Finished2 else PF.F_s13_wait_EOED)
     (mode.offer.s_ch.Msg.random) (Negotiation.selected_ha mode.sh) ->
    ks: s13_wait_ClientFinished_keys ->
    server_state region cfg

  | S13_complete:
    mode: s13_mode region cfg ->
    fin1: Ghost.erased Msg.finished ->
    fin2: Ghost.erased Msg.finished ->
    ms: msg_state region PF.F_s_Idle (* PF.F_s13_postHS *)
    (mode.offer.s_ch.Msg.random) (Negotiation.selected_ha mode.sh) ->
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
  =
  match st0, st1 with
  | S_wait_ClientHello r0 _, S13_sent_HelloRetryRequest r1 _ _ ->
    r1 == r0
  | S13_sent_HelloRetryRequest r0 retry m0,
    S13_sent_ServerHello offer sh ee _ m1 _ _ ->
    offer.retry == Some retry
  | S_wait_ClientHello _ _, S13_sent_ServerHello _ _ _ _ _ _ _
  | S13_sent_ServerHello _ _ _ _ _ _ _, S13_wait_Finished2 _ _ _ _ _
  | S13_wait_Finished2 _ _ _ _ _, S13_complete _ _ _ _ _
    -> True
  | S13_wait_Finished2 m0 sfin0 false ms0 ks0,
    S13_wait_Finished2 m1 sfin1 true ms1 ks1 -> // Received EOED
    m1 == m0 /\ sfin1 == sfin0 /\ ks1 == ks0 /\
    True // transcript is updated with EOED
  | _ -> False

let server_mrel (#region:rgn) (#cfg: server_config) =
  FStar.ReflexiveTransitiveClosure.closure (server_step #region #cfg)

type server_mref rgn cfg =
  st:HST.mreference (server_state rgn cfg) (server_mrel #rgn #cfg)
  { HS.frameOf st = rgn }

let server_footprint
  (#region:rgn) (#cfg: server_config)
  (state: server_state region cfg)
=
  match state with
  | _ -> B.loc_none  // TBC!

let server_invariant #region #config (ss: server_state region config) h = True

let server_nonce (#region:rgn) (#cfg:server_config) (s:server_state region cfg)
  : TLSInfo.random =
  match s with
  | S_wait_ClientHello random _ -> random
  | S13_sent_HelloRetryRequest random _ _ -> random
  | S13_sent_ServerHello _ sh _ _ _ _ _ -> Msg.sh_random sh
  | S13_wait_Finished2 mode _ _ _ _
  | S13_complete mode _ _ _ _ -> Msg.sh_random mode.sh
  | _ -> admit()

let server_ha (#region:rgn) (#cfg:server_config) (s:server_state region cfg)
  : Transcript.ha =
  match s with
  | S13_sent_HelloRetryRequest _ retry _ -> Negotiation.selected_ha (snd retry)
  | S13_sent_ServerHello _ sh _ _ _ _ _ -> Negotiation.selected_ha sh
  | S13_wait_Finished2 mode _ _ _ _
  | S13_complete mode _ _ _ _ -> Negotiation.selected_ha mode.sh
  | _ -> admit()

let server_flight (#region:rgn) (#cfg:server_config) (s:server_state region cfg)
  : PF.in_progress_flt_t =
  match s with
  | S_wait_ClientHello _ _
  | S13_sent_HelloRetryRequest _ _ _
  | S13_sent_ServerHello _ _ _ _ _ _ _ -> PF.F_s_Idle
  | S13_wait_Finished2 _ _ eoed _ _ ->
    if eoed then PF.F_s13_wait_Finished2 else PF.F_s13_wait_EOED
  | S13_complete _ _ _ _ _ ->
    // FIXME(adl) post-HS
    PF.F_s_Idle
  | _ -> admit()

type server_ms_t (#region:rgn) (#cfg:server_config) (s:server_state region cfg) =
  msg_state region (server_flight s) (server_nonce s) (server_ha s)

let server_ms (#region:rgn) (#cfg:server_config) (s:server_state region cfg)
  : server_ms_t s
  = assume false;
  match s with
  | S13_sent_HelloRetryRequest _ _ ms -> ms
  | S13_sent_ServerHello _ _ _ _ ms _ _ -> ms
  | S13_wait_Finished2 _ _ _ ms _ -> ms
  | S13_complete _ _ _ ms _ -> ms
  | _ -> admit()

let set_server_ms
  (#region:rgn) (#cfg:server_config) (s:server_state region cfg {~(S_wait_ClientHello? s)})
  (ms1: server_ms_t s):
  s:server_state region cfg {~(S_wait_ClientHello? s)}
  = assume false;
  match s with
  | S13_sent_HelloRetryRequest a b _ ->
    S13_sent_HelloRetryRequest a b ms1
  | S13_sent_ServerHello a b c z _   d e ->
    S13_sent_ServerHello a b c z ms1 d e
  | S13_wait_Finished2 a b c _   d ->
    S13_wait_Finished2 a b c ms1 d
  | S13_complete a b c _   d ->
    S13_complete a b c ms1 d
  | _ -> admit()

let server_epochs (#region:rgn) (#cfg:server_config) (s:server_state region cfg)
  : Epochs.epochs region (server_nonce s)
  = (server_ms s).epochs

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

type client = s:state {Client? s}
type server = s:state {Server? s}

let nonceT s h =
  match s with
  | Client region config r -> client_nonce (HS.sel h r)
  | Server region config r -> server_nonce (HS.sel h r)

let nonce (s:state)
  : ST TLSInfo.random
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> h0 == h1 /\ r == nonceT s h1)
  = assume false;
  match s with
  | Client _ _ r -> client_nonce !r
  | Server _ _ r -> server_nonce !r

let initT s h =
  match s with
  | Client _ _ r -> C_init? (HS.sel h r)
  | Server _ _ r -> S_wait_ClientHello? (HS.sel h r)

let is_init (s:state)
  : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> h0 == h1 /\ r == initT s h1)
  = assume false;
  match s with
  | Client _ _ r -> C_init? !r
  | Server _ _ r -> S_wait_ClientHello? !r

let invariant s h =
  match s with
  | Client region config r ->
    h `HS.contains` r /\
    B.loc_disjoint (B.loc_mreference r) (client_footprint (HS.sel h r)) /\
    client_invariant (HS.sel h r) h

  | Server region config r ->
    h `HS.contains` r /\
    B.loc_disjoint (B.loc_mreference r) (server_footprint (HS.sel h r)) /\
    server_invariant (HS.sel h r) h

let frame s = match s with
  | Client rgn _ _
  | Server rgn _ _ -> rgn

let epochsT s h
  : GTot (Epochs.epochs (frame s) (nonceT s h))
  = assume false;
  match s with
  | Client region config r -> client_epochs (HS.sel h r)
  | Server region config r -> server_epochs (HS.sel h r)

let epochs st n
  : ST (Epochs.epochs (frame st) n)
  (requires fun h0 -> n == nonceT st h0)
  (ensures fun h0 e h1 -> h0 == h1
    /\ e == epochsT st h1)
  = assume false;
  match st with
  | Client r c s ->
    let s = !s in
    client_epochs s
  | Server r c s ->
    let s = !s in
    server_epochs s

//let epochs_es s n = (epochs s n).Epochs.es

// FIXME(adl) used by TLS, but not well-defined
let version_of (s:state) =
  assume false;
  match s with
  | Client _ _ st ->
    let st = !st in
    TLS_1p3
  | Server _ _ st ->
    let st = !st in
    TLS_1p3

// used in FFI, TBC
let get_server_certificates (s:client) :
  ST (option Cert.chain13)
  (requires fun h0 -> Client? s /\ invariant s h0)
  (ensures fun h0 r h1 ->
    modifies_none h0 h1 /\
    invariant s h1)
=
  match s with
  | Client region config r -> client_server_certificates #region !r

let state_entry (n: TLSInfo.random) = state // TODO refinement witness reading stable n

/// TODO
/// - define a model-only global table from disjoint nonces to those connections.
/// - define a constructor adding a model-only nonce value and
///   witnessing its table registration. This is the main connection
///   type at the API.

(**** Key output interface (floating) **)

// ADL: moved here for now to share between client and server
#push-options "--admit_smt_queries true"
let register (#region:rgn) (#n:random) (epochs:Epochs.epochs region n)
  (keys:KS.recordInstance) : St unit
  =
  let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
    let h = Negotiation.Fresh ({ Negotiation.session_nego = None }) in
    Epochs.recordInstanceToEpoch #region #n h keys in // just coercion
    // New Handshake does
    // let KeySchedule.StAEInstance #id r w = keys in
    // Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h (Handshake.Secret.StAEInstance #id r w) in
  Epochs.add_epoch epochs ep // actually extending the epochs log

let export (#region:rgn) (#n:random) (epochs:Epochs.epochs region n)
  (xk:KS.exportKey) : St unit
  =
  trace "exporting a key" LowStar.Printf.done;
  FStar.Monotonic.Seq.i_write_at_end epochs.Epochs.exporter xk
#pop-options


(**** Shared binders definitions (move to TLS.Handshake.Binders?) ***)

let binder = Parsers.PskBinderEntry.pskBinderEntry
let binder_for (bkey:Negotiation.bkey13) =
  b:binder { Bytes.length b ==  EverCrypt.Hash.Incremental.hash_length (Negotiation.ha_bkey13 bkey) }
let rec binders_for (l:list Negotiation.bkey13) (l':list binder) =
  (match l, l' with
  | [], [] -> True
  | key::t, binder::t' -> Bytes.length binder ==  Hashing.hash_length (Negotiation.ha_bkey13 key)
    /\ binders_for t t'
  | _ -> False)

let btag (bkey:Negotiation.bkey13) = Hashing.tag (Negotiation.ha_bkey13 bkey)

// FIXME add ghost truncated client hello, Transcript.hashed, UFCMA.maced
assume val compute_binder:
  bkey: Negotiation.bkey13 ->
  tch_hash: Bytes.lbytes (Hashing.hash_length (Negotiation.ha_bkey13 bkey)) ->
  binder_for bkey

assume val verify_binder:
  bkey: Negotiation.bkey13 ->
  tch_hash: Bytes.lbytes (Hashing.hash_length (Negotiation.ha_bkey13 bkey)) ->
  binder: binder_for bkey ->
  bool

#push-options "--max_ifuel 1"
let rec binder_key_list_bytesize (bkeys: list KS.binder_key) =
  match bkeys with
  | bkey::bkeys -> 1 + EverCrypt.Hash.Incremental.hash_length (TLSInfo.binderId_hash (dfst bkey)) + binder_key_list_bytesize bkeys
  | [] -> 0
#pop-options

#push-options "--max_ifuel 1"
let rec bkey_list_bytesize (bkeys: list Negotiation.bkey13) =
  match bkeys with
  | bkey::bkeys -> 1 + EverCrypt.Hash.Incremental.hash_length (Negotiation.ha_bkey13 bkey) + bkey_list_bytesize bkeys
  | [] -> 0
#pop-options

module Binders = ParsersAux.Binders
module R = LowParse.Repr

// FIXME(adl) annoying and unnecessary conversion to repr for hashing
// (also limited to the size of the allocated size buffer, which can't be dynamic)
// When the interface of TLS.Handhshake.Client/Server uses repr_pos, delete this
#push-options "--admit_smt_queries true"
let get_handshake_repr (m:Msg.handshake)
  : StackInline (b:R.const_slice & MITLS.Repr.Handshake.pos b)
  (requires fun h0 -> True)
  (ensures fun h0 (| _, r |) h1 ->
    B.modifies B.loc_none h0 h1 /\
    R.value (R.as_ptr_spec r) == m)
  =
  let b = B.alloca 0z 8192ul in
  push_frame ();
  let len = Msg.handshake_size32 m in
  let slice = LP.make_slice b len in
  let Some r = MITLS.Repr.Handshake.serialize slice 0ul m in
  pop_frame ();
  (| R.of_slice slice, r |)

let get_handshake13_repr (m:Msg.handshake13)
  : StackInline (b:R.const_slice & MITLS.Repr.Handshake13.pos b)
  (requires fun h0 -> True)
  (ensures fun h0 (|_, r|) h1 ->
    B.modifies B.loc_none h0 h1 /\
    R.value (R.as_ptr_spec r) == m)
  =
  let b = B.alloca 0z 8192ul in
  push_frame ();
  let len = Msg.handshake13_size32 m in
  let slice = LP.make_slice b len in
  let Some r = MITLS.Repr.Handshake13.serialize slice 0ul m in
  pop_frame ();
  (| R.of_slice slice, r |)
#pop-options

let expected_initial_transcript (re:option Transcript.retry) ch =
  let open TLS.Handshake.Transcript in
  if Msg.ch_bound ch then TruncatedClientHello re (Msg.clear_binders ch)
  else ClientHello re ch

// ADL: I rewrote this to cover all transcript transitions from Start to Hello
// Note that this does not guarantee that the hash for the retry digest matches ha
// The returned digest is for the truncated CH if it contains binders,
// or the full CH if it does not
#push-options "--admit_smt_queries true"
let transcript_start (region:rgn) ha (re:option Transcript.retry)
  (ch:Msg.clientHello) (ignore_binders:bool)
  : ST (Transcript.state ha)
  (requires fun h0 -> region `disjoint` Mem.tls_tables_region)
  (ensures fun h0 s h1 ->
    let open TLS.Handshake.Transcript in
    transcript s h1 == expected_initial_transcript re ch /\
    invariant s h1 /\
    region_of s == region /\
    B.modifies (footprint s) h0 h1 /\
    B.fresh_loc (footprint s) h0 h1)
  =
  push_frame ();
  let di = Transcript.create region ha in
  begin
    match re with
    | None -> ()
    | Some (chh, hrr) ->
      let t0 = chh in
      let t1 = Msg.M_server_hello hrr in
      let (| _, r0 |) = get_handshake_repr t0 in
      let (| _, r1 |) = get_handshake_repr t1 in
      let label = Transcript.LR_HRR r0 r1 in
      Transcript.extend di label
  end;
  let (| _, chr |) = get_handshake_repr (Msg.M_client_hello ch) in
  let label =
    if not ignore_binders && Binders.ch_bound ch then Transcript.LR_TCH chr
    else Transcript.LR_ClientHello chr in
  Transcript.extend di label;
//  di
//  let tag = transcript_extract di in
  pop_frame (); di
//  (tag, di)
#pop-options

// Used to replace CH0 with M_message_hash - ignores binders
#push-options "--admit_smt_queries true"
let hash_ch0 (region:rgn) ha (ch:Msg.clientHello) =
  push_frame ();
  let di = Transcript.create region ha in
  let (| _, chr |) = get_handshake_repr (Msg.M_client_hello ch) in
  let label = Transcript.LR_ClientHello chr in
  Transcript.extend di label;
  let tag = transcript_extract di in
  // FIXME(adl) free_transcript di
  pop_frame ();
  Msg.M_message_hash tag
#pop-options

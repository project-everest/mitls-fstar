module TLS.Handshake.Client

open Mem
open TLSConstants
open TLSInfo
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.Machine

module B = LowStar.Buffer // not FStar.Bytes
module CH = Parsers.ClientHello
// module E = Extensions
module Epochs = Old.Epochs
module HSM = HandshakeMessages
module PF = TLS.Handshake.ParseFlights // avoidable?
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HS = FStar.HyperStack
// module H = Hashing.Spec
module Transcript = HSL.Transcript
module Receive = TLS.Handshake.Receive

#set-options "--admit_smt_queries true"

let config_of #region (Client _ cfg _) = fst cfg

// include TLS.Handshake.State

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("HS | "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_HS then print else (fun _ -> ())


/// floating; imported from State on demand

// indexing to be reviewed
val register:
  #region:rgn -> #n:random -> Epochs.epochs region n ->
  KS.recordInstance -> St unit

let register #region #n epochs keys =
    let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
      let h = Negotiation.Fresh ({ Negotiation.session_nego = None }) in
      Epochs.recordInstanceToEpoch #region #n h keys in // just coercion
      // New Handshake does
      // let KeySchedule.StAEInstance #id r w = keys in
      // Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h (Handshake.Secret.StAEInstance #id r w) in
    Epochs.add_epoch epochs ep // actually extending the epochs log

val export:
  #region:rgn -> #n:random -> Epochs.epochs region n ->
  KS.exportKey -> St unit

let export #region #n epochs xk =
  trace "exporting a key";
  FStar.Monotonic.Seq.i_write_at_end epochs.Epochs.exporter xk


// high-level transcript; floating
// TODO add precise type & move to Transcript
let transcript_extract #ha (di:Transcript.state ha) tx: St Bytes.bytes =
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  Transcript.extract_hash di btag tx;
  FStar.Bytes.of_buffer ltag btag

(*** Hello messages ***)

(*
val map_ST2: 'c -> ('c -> 'a -> KS.ST0 'b) -> list 'a -> KS.ST0 (list 'b)
let rec map_ST2 env f x = match x with
  | [] -> []
  | a::tl -> f env a :: map_ST2 env f tl

type btag (binderKey:(i:HMAC.binderId & bk:KS.binderKey i)) =
  HMAC.tag (HMAC.HMAC_Binder (let (|i,_|) = binderKey in i))

private let compute_binder (bkey:(i:HMAC.binderId & bk:KS.binderKey i)) tag
  : ST (btag bkey)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1) =
  let _,bk = bkey in
  HMAC.mac bkey tag

let client_Binders #region (hs:t region) (offer:HSM.clientHello) =
  match snd hs.cfg with
  | (_, []) ->
    Send.send_ch hs.log (HSL.Msg (HSM.M_client_hello offer))
  | (_, pskl) ->
    let binderKeys = KS.ks_client13_get_binder_keys hs.ks pskl in
    let blen = E.bindersLen offer.CH.extensions in
    HSL.send_truncated hs.log (HSL.Msg (HSM.M_client_hello offer)) blen;
    let binders = map_ST2 hs compute_binder binderKeys in
    let bb = PSK.offeredPsks_binders_serializer32 binders in
    HSL.send_raw hs.log bb;
    // Nego ensures that EDI is not sent in a 2nd ClientHello
 *)

/// Create a transcript digest for the truncated client Hello.
let client_transcript (region:rgn) ha tch =
  let di, transcript0 = Transcript.create region ha in
  let transcript1 = Transcript.extend di (admit() (*of tch*)) transcript0 in
  let tag = transcript_extract di transcript1 in
  (tag, di)

let btag (bkey:Negotiation.bkey13) =
  Bytes.bytes
  // Hacl.Hash.Definitions.hash_t (Negotiation.ha_bkey13 bkey)

// TODO sort it out within KeySchedule
assume val compute_binder:
  bkey:Negotiation.bkey13 ->
  tag: btag bkey -> btag bkey

/// Compute binder MACs for the PSKs; in rare cases we allocate an
/// auxiliary transcripts for other hash algorithms.
//TODO type; tch & logical payload
val client_Binders:
  region:rgn ->
  ha0: EverCrypt.Hash.Incremental.alg ->
  di: Transcript.state ha0 ->
  tch: full_offer ->
  bkey: list Negotiation.bkey13 ->
  ST Bytes.bytes
  (requires fun h0 ->
    Transcript.invariant di (transcript_tch tch) h0)
  (ensures fun h0 b h1 ->
    modifies_none h0 h1)

let rec client_Binders region ha0 di0 tch bkeys =
  match bkeys with
  | [] -> Bytes.empty_bytes
  | bkey::bkeys ->
    let ha = Negotiation.ha_bkey13 bkey in
    let tx: Transcript.g_transcript_n (Ghost.hide 0) = Ghost.hide (transcript_tch tch) in
    let tag =
      if ha = ha0 then
        transcript_extract di0 tx
      else
        let tag, di = client_transcript region ha tch in
        // TODO Transcript.free di
        tag in
    let binder = compute_binder bkey tag in
    Bytes.append binder (client_Binders region ha0 di0 tch bkeys )

let initial_ha offer =
  match offer.Parsers.ClientHello.cipher_suites with
  | [] -> EverCrypt.Hash.Incremental.SHA2_256
  | cs::_ ->
    match cipherSuite_of_name cs with
    | Some (CipherSuite.CipherSuite13 _ ha) -> ha
    | _ -> EverCrypt.Hash.Incremental.SHA2_256

let client_ClientHello (Client region config r) =
  let (cfg,resume) = config in
  let C_init random = !r in
  let groups =
    match cfg.max_version with
    | TLS_1p3 -> trace "offering ClientHello 1.3"; Some cfg.offer_shares
    | _       -> trace "offering ClientHello 1.2"; None in
    // groups = None indicates a 1.2 handshake
    // groups = Some [] is valid, may be used to deliberately trigger HRR
  let ks, shares = KS.ks_client_init random groups in

  // Compute & send the ClientHello offer
  // lower: we'll instead pass the sending state for writing the offer.
  match Negotiation.client_ClientHello config random shares with
  | Error z -> Error z
  | Correct offer0 -> (
    let full_offer = {full_retry = None; full_ch = offer0} in
    // TODO: output CH, including dummy binders if it offers PSKs (no transcript yet)
    // Send.send_tch sending offer0;

    // TODO assert we have a slice with this serialized offer

    // allocate digest state with a reasonable default hash algorithm
    let ha = initial_ha offer0 in
    let tag, di = client_transcript region ha offer0 in
    let tx_tch = Ghost.hide (transcript_tch full_offer) in
    let sending = Send.send_state0 in
    let receiving = Receive.(create (alloc_slice region)) in
    let epochs = Epochs.create region random in
    let ms: msg_state region ParseFlights.F_c_wait_ServerHello random ha = {
      digest = di;
      sending = sending;
      receiving = receiving;
      epochs = epochs;
    } in
    // write transient state for witnessing offer0 (used for binders)
    r := C_wait_ServerHello ({full_retry=None; full_ch=offer0}) ms ks;

    // TODO below: postcondition stating the transcript is at [ClientHello None offer1], and computing ha from offer1 too
    let (| offer1, ha, digest |) : (_ & ha:_ & Transcript.state ha) = (
      match resume with
      | (_,[]) -> (| offer0, ha, di |)
      | (_,psks) -> (
        let binders = client_Binders region ha di full_offer psks in

        // TODO patch both the offer and its serialization in [sending]
        let offer1 = offer0 in
        let tx1 = Transcript.(extend di (admit()) (* LR_CompleteTCH of [binder] *) tx_tch) in
        let sending =
          if Negotiation.find_early_data offer0 then (
            trace "setting up 0RTT";
            let digest_CH = transcript_extract di tx1  in
            // TODO consider doing export & register within KS
            let early_exporter_secret, edk = KS.ks_client13_ch cfg.is_quic ks digest_CH in
            export epochs early_exporter_secret;
            register epochs edk;
            Send.signals sending (Some (true, false)) false )
          else sending in
        (| offer1, ha, di |))) in

    r := C_wait_ServerHello ({full_retry=None; full_ch=offer1}) ms ks;
    Correct () )

let client_HelloRetryRequest (Client region config r) hrr =
  let C_wait_ServerHello offer ms ks = !r in
  let open Parsers.HelloRetryRequest in
  trace("HelloRetryRequest with extensions " ^ Nego.string_of_hrres hrr.extensions);
  let ch1 = offer.full_ch in
  let share, ks =
  match Negotiation.group_of_hrr hrr with
  | None ->
    // this case should only ever happen in QUIC stateless retry address validation
    // FIXME(adl) deprecated in current QUIC with transport retry
    trace "Server did not specify a group in HRR, re-using the previous choice"; None, ks
  | Some ng ->
    let Some g = CommonDH.group_of_namedGroup ng in
      let s, ks = KS.ks_client13_hello_retry ks g in
      Some (| g, s |), ks
  in
  match Nego.client_HelloRetryRequest ch1 hrr share with
  | Error z -> Receive.InError z
  | Correct ch2 ->
    // TODO: adapt from the code above
    // does it make sense to send binders with the wrong hash algorithm?

    // WAS: (assuming the server's required share had already been sent)
    // client_Binders hs ch2;
//    client_Binders hs ch2;
//    hs.state := C13_sent_CH2 ch1 hri;
//    hs.nego.Nego.state := Nego.C_Offer ch2;
    Receive.InAck false false

(*
let client_HelloRetryRequest (Client region config r) hrr =
  trace "client_HelloRetryRequest";
  let C_wait_ServerHello offer ms ks = !r in
  let share, ks =
    match Negotiation.group_of_hrr hrr with
    | None ->
      // this case should only ever happen in QUIC stateless retry address validation
      // FIXME(adl) deprecated in current QUIC with transport retry
      trace "Server did not specify a group in HRR, re-using the previous choice"; None, ks
    | Some ng ->
        let Some g = CommonDH.group_of_namedGroup ng in
        let s, ks = KS.ks_client13_hello_retry ks g in
        Some (| g, s |), ks
    in
  match Negotiation.client_HelloRetryRequest offer.full_ch hrr share with
  | Error z -> Receive.InError z
  | Correct offer2 -> (

    // // Note: we stay in Wait_ServerHello
    // // Only the Nego state machine was moved by HRR
    Receive.InAck false false )
*)

let client_ServerHello (Client region config r) sh =
  trace "client_ServerHello";
  let cfg,_ = config in
  let C_wait_ServerHello offer ms ks = !r in
  match Negotiation.client_accept_ServerHello cfg offer.full_ch sh with
  | Error z -> Receive.InError z
  | Correct (cs,pski) -> (
    match cs with
    | CipherSuite13 ae ha -> (
      trace "Running TLS 1.3";
      let server_share = Negotiation.find_serverKeyShare sh in
      let transcript_sh = Transcript.extend ms.digest (admit() (*sh*)) (Ghost.hide (transcript_offer offer)) in
      //assert(transcript_sh == transcript13 offer sh []);
      let digest_ServerHello = transcript_extract ms.digest transcript_sh in
      let hs_keys, ks = KS.ks_client13_sh
        region
        ks
        cfg.is_quic
        sh.Parsers.RealServerHello.random
        (CipherSuite13 ae ha)
        digest_ServerHello
        server_share
        pski in
      register ms.epochs hs_keys; // register new epoch
      if Negotiation.find_early_data offer.full_ch then (
        // Skip the 0-RTT epoch on the reading side
        Epochs.incr_reader ms.epochs;
        match pski with
        | None ->
          trace "0-RTT rejected early (no PSK was selected)";
          Epochs.incr_writer ms.epochs
        | Some _ ->
          trace "0RTT potentially accepted (wait for EE to confirm)";
          // No EOED in QUIC, so we immediately enable HSK
          if cfg.is_quic then Epochs.incr_writer ms.epochs )
      else // No EOED to send in 0-RTT epoch
        Epochs.incr_writer ms.epochs; // Next flight (CFin) will use HSK

      Epochs.incr_reader ms.epochs; // Client 1.3 HSK switch to handshake key for decrypting EE etc...
      // assume(
      //   selected_ha sh == offered_ha offer.full_ch /\
      //   PF.length_parsed_bytes ms.receiving.Receive.pf_st == 0
      //   );
      // let ms: msg_state region PF.F_c_wait_ServerHello (offer.full_ch.HSM.random) (selected_ha sh) = ms in
      // let ms: msg_state region PF.F_c13_wait_Finished1 (offer.full_ch.HSM.random) (selected_ha sh) = {ms with receiving = ms.receiving } in
      let ms = { ms with receiving = ms.receiving } in
      r := C13_wait_Finished1 offer sh ms ks;
      Receive.InAck true false // Client 1.3 HSK
    )
    | CipherSuite kex sa ae -> (
      trace "Running classic TLS";
      trace ("Offered SID="^(Bytes.print_bytes offer.full_ch.CH.session_id)^" Server SID="^(Bytes.print_bytes sh.Parsers.RealServerHello.session_id));
      Receive.InError (fatalAlert Handshake_failure, "TLS 1.2 TBC")
      // if Negotiation.resume_12 mode then
      // begin // 1.2 resumption
      //   trace "Server accepted our 1.2 ticket.";
      //   let Some (tid, Ticket.Ticket12 pv cs ems msId ms) = fst (Negotiation.resume s.nego) in
      //   let pv' = mode.Negotiation.n_protocol_version in
      //   let cs' = mode.Negotiation.n_cipher_suite in
      //   let sr = mode.Negotiation.n_server_random in
      //   let nst = Negotiation.sendticket_12 mode in
      //   if pv = pv' && cs = cs' then // TODO check full session
      //   begin
      //     let adk = KS.ks_client12_resume s.ks sr pv cs ems msId ms in
      //     let digestSH = HSL.hash_tag #ha s.log in
      //     register s adk;
      //     s.state := (if nst then C_wait_NST true else C_wait_CCS (true, digestSH));
      //     InAck false false
      //   end
      //   else
      //     InError (fatalAlert Handshake_failure, "inconsistent protocol version or ciphersuite during resumption")
      // end
      // else
      // begin // 1.2 full handshake
      //   s.state := C_wait_ServerHelloDone;
      //   InAck false false
      // end
      ))

// let client_ServerHello_HRR s ch1 hri sh =
//   trace "client_ServerHello";
//   match Nego.check_retry ch1 hri sh with
//   | Error z -> InError z
//   | Correct () ->
//     client_ServerHello s sh

(*** TLS 1.3 ***)

let client13_Finished2 (Client region config r) (*ocr*) =

  let C13_complete offer sh ee server_id fin1 fin2 eoed_args ms ks = !r in
  let ha = selected_ha sh in
  let hlen = Hacl.Hash.Definitions.hash_len ha in
  let btag: Hacl.Hash.Definitions.hash_t ha = B.alloca 0uy 64ul in // large enough for any digest

  // TODO: support certificate-based client authentication
  // let digest =
  //   match ocr with
  //   | Some cr ->
  //     let open Parsers.Certificate13 in
  //     let c = ({certificate_request_context = Bytes.empty_bytes; certificate_list = []}) in
  //     HandshakeLog.send_tag #ha hs.log (HSL.Msg13 (HSM.M13_certificate c))
  //   | None -> digestServerFinished in

  // prepare & send Finished2
  let transcript_Finished1: Transcript.g_transcript_n (Ghost.hide 0) = Ghost.hide (transcript13 offer sh []) in
  Transcript.extract_hash ms.digest btag transcript_Finished1;
  let digest_Finished1 = Bytes.of_buffer hlen btag in

  // to be updated, possibly using btag as output buffer.
  // may use an abstract accessor instead: (i:HMAC.finishedId & cfk:KS.fink i)
  let Old.KeySchedule.C13_wait_Finished2 _ (| cfin_id, cfin_key |) _ _ = ks in
  let cvd = HMAC.mac cfin_key digest_Finished1 in
  let fin2 = Ghost.hide #finished cvd in

  match Send.send_tag13 ms.digest transcript_Finished1 ms.sending (HSM.M13_finished cvd) btag with
  | Error z -> Error z
  | Correct (sending, transcript_Finished2) ->

  let digest_Finished2 = FStar.Bytes.of_buffer hlen btag in
  let ks = KS.ks_client13_cf ks digest_Finished2 in // post-handshake keying
  Epochs.incr_reader ms.epochs; // to ATK
  let sending = Send.signals sending (Some (true, false)) true in

  let ms = { ms with sending = sending } in
  // updating [ms.sending fin2 ks]
  r := C13_complete offer sh ee server_id fin1 fin2 eoed_args ms ks;
  Correct ()

let client13_nego_cb cfg ee =
  trace ("Received encrypted extensions "^Negotiation.string_of_ees ee);
  trace ("Negotiation callback to process application extensions.");
  let uexts = List.Tot.filter Parsers.EncryptedExtension.EE_Unknown_extensionType? ee in
  // the length check below could be statically excluded from the definition of filtering
  if not (Parsers.EncryptedExtensions.check_encryptedExtensions_list_bytesize uexts)
  then
    fatal Internal_error "encrypted extensions are too large"
  else
  let uexts_bytes = Parsers.EncryptedExtensions.encryptedExtensions_serializer32 uexts in
  // to be simplified (see TLS.Callbacks)
  let cb = cfg.nego_callback in
  let open TLS.Callbacks in
  match cb.negotiate cb.nego_context TLS_1p3 uexts_bytes None with
  | Nego_abort    -> fatal Handshake_failure "application requested to abort the handshake"
  | Nego_retry _  -> fatal Internal_error "client application requested a server retry"
  | Nego_accept _ -> Correct ()

// annoying differently refined bytes, to be reviewed
type cert_repr = Parsers.ASN1Cert.aSN1Cert // aka b:bytes {length b < 16777216} but with another syntax
private let coerce_asncert (x:Parsers.ASN1Cert.aSN1Cert): cert_repr = x
private let coerce_crt crt = List.Tot.map coerce_asncert crt

// process the certificate chain and verify the server signature
let client13_c_cv cfg offer ha transcript_ee (digest: Transcript.state ha)
  (c: HSM.certificate13)
  (cv: HSM.certificateVerify13) =
  let transcript_c = Transcript.extend digest (admit()(*c*)) transcript_ee in
  let digest_signed = transcript_extract digest transcript_c in
  let transcript_cv = Transcript.extend digest (admit()(*cv*)) transcript_c in

  // TODO ensure that valid_offer mandates signature extensions for 1.3
  let sal = match Negotiation.find_signature_algorithms offer with
  | Some sal -> sal
  | None -> [] in
    let sa = cv.HSM.algorithm in
    let chain = Some (c, sa) in
    if not (List.Tot.mem sa sal)
    then
      fatal Bad_certificate "The server signed with an algorithm we did not offer"
    else
      let tbs = Negotiation.to_be_signed TLS_1p3 TLSConstants.Server None digest_signed in
      let chain = coerce_crt (Cert.chain_down c.HSM.certificate_list) in
      if not (TLS.Callbacks.cert_verify_cb cfg.cert_callbacks chain sa tbs cv.HSM.signature)
      then (
        trace("Certificate & signature 1.3 callback failed");
        fatal Bad_certificate "Failed to validate signature or certificate" )
      else (
        trace("Certificate & signature 1.3 callback succeeded");
        Correct transcript_cv )

let client13_Finished1 hs ee client_cert_request server_cert_certverify finished
=
  let Client region (cfg,_) r = hs in
  match client13_nego_cb cfg ee with
  | Error z -> Receive.InError z
  | Correct _ ->
  match client_cert_request with
  | Some _ -> Receive.InError (fatalAlert Handshake_failure,"unsupported client certificate request")
  | None ->

  let C13_wait_Finished1 offer sh ms ks = !r in
  let ha = selected_ha sh in
  let hlen = Hacl.Hash.Definitions.hash_len ha in
  let btag: Hacl.Hash.Definitions.hash_t ha = B.alloca 0uy 64ul in // large enough for any digest
  let transcript_ee: Ghost.erased Transcript.transcript_t = Transcript.extend ms.digest
    (admit()(* LR for ee *))
    (Ghost.hide (transcript13 offer sh [])) in
  let psk_based = Some? (Negotiation.find_serverPske sh) in
  let verified_server =
    match server_cert_certverify with
    | None ->
        if not psk_based then
          fatal Handshake_failure "missing certificate chain and sigature"
        else
          // relying on a previously received & verified server
          // certificate chain & signature recorded for this PSK; TODO
          // confirm this context is available to the application.
          Correct transcript_ee

    | Some (c,cv) ->
        if psk_based then
          fatal Handshake_failure "unexpected certificate chain and signature"
        else
          client13_c_cv cfg offer.full_ch ha transcript_ee ms.digest c cv
  in
  match verified_server with
  | Error z -> Receive.InError z
  | Correct transcript_maced -> (
    // let oc =
    // let open Parsers.Certificate13 in
    // match oc with | None -> None | Some c -> Some c.certificate_list in
    // let cfg = Negotiation.local_config hs.nego in
    // match Negotiation.clientComplete_13 hs.nego ee ocr oc ocv digestCert with

  let digest_maced = transcript_extract ms.digest transcript_maced in
  let transcript_Finished1 = Transcript.(extend ms.digest (admit()(*finished*)) transcript_maced) in
  let digest_Finished1 = transcript_extract ms.digest transcript_Finished1 in
  let ks, (sfin_key, cfin_key, app_keys, exporter_master_secret) = KS.ks_client13_sf cfg.is_quic ks digest_Finished1 in
  // ADL: 4th returned value is the exporter master secret.
  // should be passed to application somehow --- store in Nego? We need agreement.

  let (| finId, sfin_key |) = sfin_key in
  if not (HMAC.verify sfin_key digest_maced digest_maced)
  then
    Receive.InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digest_maced)
  else (
    export ms.epochs exporter_master_secret;
    register ms.epochs app_keys; // ATKs are ready to use in both directions

    if Negotiation.zeroRTT sh && not cfg.is_quic // EOED emitting (not used for QUIC)
    then (
      trace "Early data accepted; emitting EOED.";
      match Send.send13 #ha ms.digest #(Ghost.hide 0) (admit()) ms.sending (HSM.M13_end_of_early_data ()) with
      | Correct (sending, transcript) -> (
        let sending = Send.signals sending (Some (false, false)) false in
        let eoed_args = Some (None, cfin_key) in
        let fin1 = Ghost.hide Bytes.empty_bytes in
        let fin2 = Ghost.hide Bytes.empty_bytes in
        r := C13_complete offer sh ee server_cert_certverify fin1 fin2 eoed_args ms ks; // digestEOED ocr cfin_key;
        Receive.InAck false false )
      | Error z -> Receive.InError z )
    else (
      (if Negotiation.zeroRTT sh
      then trace "Early data accepted (QUIC, no EOED)."
      else trace "Early data rejected");
      // TODO write r before this call!
      match client13_Finished2 hs with
      | Error z   -> Receive.InError z
      | Correct _ -> Receive.InAck true false // Client 1.3 ATK; next the client will read again to send Finished, writer++, and the Complete signal
      )))

let client13_NewSessionTicket (Client region config r) st13 =
  let open TLS.Callbacks in
  let open Parsers.NewSessionTicket13 in
  let open Parsers.NewSessionTicketExtension in
  let tid = st13.ticket in
  let nonce = st13.ticket_nonce in
  let age_add = st13.ticket_age_add in
  trace ("Received ticket: "^Bytes.hex_of_bytes tid^" nonce: "^Bytes.hex_of_bytes nonce);

  let C13_complete offer sh ee server_id _fin1 _fin2 _eoed_args _ms ks = !r in
  let cs = sh.Parsers.RealServerHello.cipher_suite in
  let Some cs = CipherSuite.cipherSuite_of_name cs in // add static refinement?
  let ed = List.Tot.find NSTE_early_data? st13.extensions in
  let now = UInt32.uint_to_t (FStar.Date.secondsFromDawn()) in
  let info = TicketInfo_13 TLS.Callbacks.({
    ticket_nonce = Some nonce;
    time_created = now;
    ticket_age_add = age_add;
    allow_early_data = Some? ed;
    allow_dhe_resumption = true;
    allow_psk_resumption = true;
    early_cs = cs;
    identities = (Bytes.empty_bytes, Bytes.empty_bytes); // TODO certs
  }) in

  let psk = KS.ks_client13_rms_psk ks nonce in
  let Some sni = Bytes.iutf8_opt (Negotiation.get_sni offer.full_ch) in
  let cfg = fst config in
  let valid_ed =
    if cfg.is_quic then
      (match ed with
      | None -> true
      | Some (NSTE_early_data x) -> x = 0xfffffffful
      | _ -> false)
    else true in
  if valid_ed then
    (let tcb = cfg.ticket_callback in
    tcb.new_ticket tcb.ticket_context sni tid info psk;
    Receive.InAck false false)
  else
    Receive.InError (fatalAlert Illegal_parameter, "QUIC tickets must allow 0xFFFFFFFF bytes of early data")

let early_rejected (Client region config r) =
  match !r with
  | C13_wait_Finished1 offer sh _ _
  | C13_complete offer sh _ _ _ _ _ _ _ ->
    Negotiation.find_early_data offer.full_ch &&
    not (List.Tot.existsb Parsers.ServerHelloExtension.SHE_early_data? sh.Parsers.RealServerHello.extensions)
  | _ -> false

(*** TLS 1.2 ***)

private let convert_kex = function
  | Kex_RSA -> Correct HSM.Rsa
  | Kex_DHE -> Correct HSM.Dhe
  | Kex_ECDHE -> Correct HSM.Ecdhe
  | _ -> fatal Internal_error "Incorrect key exchange selected for 1.2"

let client12_ServerHelloDone hs c ske_bytes ocr =
  trace "processing ...ServerHelloDone";
  Receive.InError (fatalAlert Internal_error, "TBC")
  // let kex = Negotiation.kexAlg (Negotiation.getMode hs.nego) in
  // match convert_kex kex with
  // | Error z -> InError z
  // | Correct kex ->
  // match HSM.serverKeyExchange_parser32 kex ske_bytes with
  // | None -> InError (fatalAlert Decode_error, "invalid client key exchange")
  // | Some (ske, _) ->
  // match Negotiation.client_ServerKeyExchange hs.nego c kex ske ocr with
  // | Error z -> InError z
  // | Correct mode -> (
  //   (match ocr with
  //   | None -> ()
  //   | Some cr ->
  //     trace "processing certificate request (TODO)";
  //     HSL.send hs.log (HSL.Msg12 (HSM.M12_certificate [])));
  //   let nst = Negotiation.sendticket_12 mode in
  //   let gy = Some?.v (mode.Negotiation.n_server_share) in // already set in KS
  //   let gx =
  //     KS.ks_client12_full_dh hs.ks
  //     mode.Negotiation.n_server_random
  //     mode.Negotiation.n_protocol_version
  //     mode.Negotiation.n_cipher_suite
  //     (Negotiation.emsFlag mode) // a flag controlling the use of ems
  //     gy in
  //   let (|g, _|) = gy in
  //   let gxb = CommonDH.serialize_raw gx in
  //   let open Parsers.ClientKeyExchange in
  //   let cke : clientKeyExchange kex =
  //     match kex with
  //     | HSM.Ecdhe -> Cke_ecdhe gxb
  //     | HSM.Dhe -> Cke_dhe gxb in
  //   let msg = HSM.M12_client_key_exchange (
  //     clientKeyExchange_serializer32 kex cke) in
  //   let ha = verifyDataHashAlg_of_ciphersuite (mode.Negotiation.n_cipher_suite) in
  //   let digestClientKeyExchange = HSL.send_tag #ha hs.log (HSL.Msg12 msg) in
  //   let cfin_key, app_keys = KS.ks_client12_set_session_hash hs.ks digestClientKeyExchange in
  //   register hs app_keys;
  //   // we send CCS then Finished;  we will use the new keys only after CCS
  //   let cvd = TLSPRF.finished12 ha cfin_key Client digestClientKeyExchange in
  //   let fin = HSM.M12_finished cvd in
  //   let digestClientFinished = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 fin) false in
  //   hs.state := (
  //     if nst then
  //        C_wait_NST false
  //     else
  //       C_wait_CCS (false, digestClientFinished));
  //   InAck false false)

let client12_R_ServerFinished hs f digestNewSessionTicket digestServerFinished =
  trace "client_R_ServerFinished";
  Receive.InError (fatalAlert Internal_error, "TBC")
  // let sfin_key = KS.ks12_finished_key hs.ks in
  // let mode = Negotiation.getMode hs.nego in
  // let ha = verifyDataHashAlg_of_ciphersuite mode.Negotiation.n_cipher_suite in
  // let expected_svd = TLSPRF.finished12 ha sfin_key Server digestNewSessionTicket in
  // if f = expected_svd
  // then (
  //   let cvd = TLSPRF.finished12 ha sfin_key Client digestServerFinished in
  //   let _ = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 (HSM.M12_finished cvd)) true in
  //   hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
  //   InAck false false // send_CCS_tag buffers the complete
  // )
  // else
  //   InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digestNewSessionTicket)

let client12_ServerFinished hs f digestClientFinished =
  Receive.InError (fatalAlert Internal_error, "TBC")
  // let sfin_key = KS.ks12_finished_key hs.ks in
  // let mode = Negotiation.getMode hs.nego in
  // let ha = verifyDataHashAlg_of_ciphersuite mode.Negotiation.n_cipher_suite in
  // let expected_svd = TLSPRF.finished12 ha sfin_key Server digestClientFinished in
  // //let expected_svd = TLSPRF.verifyData (mode.Negotiation.n_protocol_version,mode.Negotiation.n_cipher_suite) sfin_key Server digestClientFinished in
  // if f = expected_svd
  // then (
  //   hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
  //   InAck false true // Client 1.2 ATK
  //   )
  // else
  //   InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digestClientFinished)

let client12_NewSessionTicket hs (resume:bool) (digest:Hashing.anyTag) (st: HSM.newSessionTicket12) =
  let open Parsers.NewSessionTicket12 in
  let open TLS.Callbacks in
  trace ("Processing ticket: "^Bytes.print_bytes st.ticket);
  Receive.InError (fatalAlert Internal_error, "TBC")
  // hs.state := C_wait_CCS (resume, digest);
  // let cfg = Negotiation.local_config hs.nego in
  // let tcb = cfg.ticket_callback in
  // let mode = Negotiation.getMode hs.nego in
  // let Some sni = Bytes.iutf8_opt (Negotiation.get_sni mode.Negotiation.n_offer) in

  // let (_msId, ms) = KS.ks12_ms hs.ks in
  // let info = TLS.Callbacks.TicketInfo_12 (
  //   mode.Negotiation.n_protocol_version,
  //   mode.Negotiation.n_cipher_suite,
  //   Negotiation.emsFlag mode) in

  // tcb.new_ticket tcb.ticket_context sni st.ticket info ms;
  // InAck false false

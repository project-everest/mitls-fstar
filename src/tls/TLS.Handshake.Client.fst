module TLS.Handshake.Client

open Mem
open TLSConstants
open TLSInfo
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.Machine

module B = LowStar.Buffer // not FStar.Bytes
module CH = Parsers.ClientHello
module E = Extensions
module Epochs = Old.Epochs
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HS = FStar.HyperStack
module H = Hashing.Spec

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


(*** Version-agnostic messages ***)


(*
type btag (binderKey:(i:HMAC.binderId & bk:KS.binderKey i)) =
  HMAC.tag (HMAC.HMAC_Binder (let (|i,_|) = binderKey in i))

private let compute_binder hs (bkey:(i:HMAC.binderId & bk:KS.binderKey i))
  : ST (btag bkey)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1) =
  let (| bid, bk |) = bkey in
  let digest_CH0 = HSL.hash_tag #(binderId_hash bid) hs.log in
  HMAC.mac bk digest_CH0

val map_ST2: 'c -> ('c -> 'a -> KS.ST0 'b) -> list 'a -> KS.ST0 (list 'b)
let rec map_ST2 env f x = match x with
  | [] -> []
  | a::tl -> f env a :: map_ST2 env f tl
*)


(*
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

let transcript_extract #ha (di:HSL.Transcript.state ha) tx: St Bytes.bytes =
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  HSL.Transcript.extract_hash di btag tx;
  FStar.Bytes.of_buffer ltag btag

/// Create a fresh transcript digest, hash the truncated client Hello,
/// and compute the MAC for a given PSK.
//TODO tch & logical payload
let client_Binder region (bkey:Negotiation.bkey13) tch =
  let ha = Negotiation.ha_bkey13 bkey in
  let di, tx0 = HSL.Transcript.create region ha in
  let tx1 = HSL.Transcript.extend di tch tx0 in
  let tag = transcript_extract di tx1 in
  let binder = KS.mk_binder #region bkey in // vs HMAC.mac bk tag, hiding tricky indexing
  tx1, ha, di, binder

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
  // TODO allocate non-empty output slice!
  let sending = Send.send_state0 in
  match Negotiation.client_ClientHello config random shares with
  | Error z -> Error z
  | Correct offer0 -> (
    let epochs = Epochs.create region random in
    let receiving_buffer = LowStar.Buffer.alloca 0uy 12000ul in
    let receiving = TLS.Handshake.Receive.create receiving_buffer in

    // TODO: write CH, including dummy binders if it offers PSKs.
    // Send.send_ch sending offer;

    // TODO assert we have a slice with this serialized offer

    // TODO: postcondition stating the transcript is at [ClientHello None offer1], and computing ha from offer1 too
    let (| offer1, ha, digest |) : (_ & ha:_ & HSL.Transcript.state ha) = (
      match resume with
      | (_,[]) -> (
        let ha = EverCrypt.Hash.Incremental.SHA2_256 in // a reasonable default
        let di, tx0 = HSL.Transcript.create region ha in
        let tx1 = HSL.Transcript.(extend di (admit()) (* LR_ClientHello of offer *) tx0) in
        (| offer0, ha, di |) )

      | (_,(psk0::psks)) -> (
        // TODO intermediate write to hs for witnessing the binder's
        // logical payload; this requires a dummy digest.
        let tx1, ha, di, binder = client_Binder region psk0 (admit()) (* LR_TCH of offer *) in
        // TODO iterate on the other binders [psks], deallocating their auxiliary digests
        // TODO patch both the offer and its serialization in [sending]
        let offer1 = offer0 in
        let tx2 = HSL.Transcript.(extend di (admit()) (* LR_CompleteTCH of [binder] *) tx1) in
        let sending =
        if Negotiation.find_early_data offer0 then (
          trace "setting up 0RTT";
          let digest_CH = transcript_extract di tx2  in
          // TODO consider doing export & register within KS
          let early_exporter_secret, edk = KS.ks_client13_ch cfg.is_quic ks digest_CH in
          export epochs early_exporter_secret;
          register epochs edk;
          Send.signals sending (Some (true, false)) false )
        else sending in
        (| offer1, ha, di |))) in

    let ms: msg_state region ParseFlights.F_c_wait_ServerHello random ha = {
      digest = digest;
      sending = sending;
      receiving = receiving;
      epochs = epochs;
    } in
    r := C_wait_ServerHello ({full_retry=None; full_ch=offer1}) ms ks;
    Correct () )

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
    // TODO: adapt from the code above
    // does it make sense to send binders with the wrong hash algorithm?

    // WAS: (assuming the server's required share had already been sent)
    // client_Binders hs ch2;
    // // Note: we stay in Wait_ServerHello
    // // Only the Nego state machine was moved by HRR
    Receive.InAck false false )

let client_ServerHello (Client region config r) sh =
  trace "client_ServerHello";
  let cfg,_ = config in
  let C_wait_ServerHello offer ms ks = !r in
  match Negotiation.client_accept_ServerHello config offer.full_ch sh with
  | Error z -> Receive.InError z
  | Correct (cs,pski) -> (
    match cs with
    | CipherSuite13 ae ha -> (
      trace "Running TLS 1.3";
      let server_share = Negotiation.find_serverKeyShare sh in
      let digest_ServerHello = HSL.hash_tag #ha s.log in
      let hs_keys, ks = KS.ks_client13_sh
        s.ks
        cfg.is_quic
        sh.RealServerHello.random
        (CipherSuite13 ae ha)
        digest_ServerHello
        server_share
        pski in
      register sms.epochs hs_keys; // register new epoch
      if Negotiation.zeroRTToffer offer.full_ch then (
        // Skip the 0-RTT epoch on the reading side
        Epochs.incr_reader s.epochs;
        match mode.Negotiation.n_pski with
        | None ->
          trace "0-RTT rejected early (no PSK was selected)";
          Epochs.incr_writer s.epochs
        | Some _ ->
          trace "0RTT potentially accepted (wait for EE to confirm)";
          // No EOED in QUIC, so we immediately enable HSK
          if cfg.is_quic then Epochs.incr_writer ms.epochs )
      else // No EOED to send in 0-RTT epoch
        Epochs.incr_writer ms.epochs; // Next flight (CFin) will use HSK

      Epochs.incr_reader ms.epochs; // Client 1.3 HSK switch to handshake key for decrypting EE etc...
      r := C13_wait_Finished1 offer sh ms ks;
      Receive.InAck true false // Client 1.3 HSK
    )
    | CipherSuite kex sa ae -> (
      trace "Running classic TLS";
      trace ("Offered SID="^(Bytes.print_bytes mode.Negotiation.n_offer.CH.session_id)^" Server SID="^(Bytes.print_bytes mode.Negotiation.n_sessionID));
      if Negotiation.resume_12 mode then
      begin // 1.2 resumption
        trace "Server accepted our 1.2 ticket.";
        let Some (tid, Ticket.Ticket12 pv cs ems msId ms) = fst (Negotiation.resume s.nego) in
        let pv' = mode.Negotiation.n_protocol_version in
        let cs' = mode.Negotiation.n_cipher_suite in
        let sr = mode.Negotiation.n_server_random in
        let nst = Negotiation.sendticket_12 mode in
        if pv = pv' && cs = cs' then // TODO check full session
        begin
          let adk = KS.ks_client12_resume s.ks sr pv cs ems msId ms in
          let digestSH = HSL.hash_tag #ha s.log in
          register s adk;
          s.state := (if nst then C_wait_NST true else C_wait_CCS (true, digestSH));
          InAck false false
        end
        else
          InError (fatalAlert Handshake_failure, "inconsistent protocol version or ciphersuite during resumption")
      end
      else
      begin // 1.2 full handshake
        s.state := C_wait_ServerHelloDone;
        InAck false false
      end ))

(*** TLS 1.2 ***)

private let convert_kex = function
  | Kex_RSA -> Correct HSM.Rsa
  | Kex_DHE -> Correct HSM.Dhe
  | Kex_ECDHE -> Correct HSM.Ecdhe
  | _ -> fatal Internal_error "Incorrect key exchange selected for 1.2"

let client_ServerHelloDone hs c ske_bytes ocr =
  trace "processing ...ServerHelloDone";
  let kex = Negotiation.kexAlg (Negotiation.getMode hs.nego) in
  match convert_kex kex with
  | Error z -> InError z
  | Correct kex ->
  match HSM.serverKeyExchange_parser32 kex ske_bytes with
  | None -> InError (fatalAlert Decode_error, "invalid client key exchange")
  | Some (ske, _) ->
  match Negotiation.client_ServerKeyExchange hs.nego c kex ske ocr with
  | Error z -> InError z
  | Correct mode -> (
    (match ocr with
    | None -> ()
    | Some cr ->
      trace "processing certificate request (TODO)";
      HSL.send hs.log (HSL.Msg12 (HSM.M12_certificate [])));
    let nst = Negotiation.sendticket_12 mode in
    let gy = Some?.v (mode.Negotiation.n_server_share) in // already set in KS
    let gx =
      KS.ks_client12_full_dh hs.ks
      mode.Negotiation.n_server_random
      mode.Negotiation.n_protocol_version
      mode.Negotiation.n_cipher_suite
      (Negotiation.emsFlag mode) // a flag controlling the use of ems
      gy in
    let (|g, _|) = gy in
    let gxb = CommonDH.serialize_raw gx in
    let open Parsers.ClientKeyExchange in
    let cke : clientKeyExchange kex =
      match kex with
      | HSM.Ecdhe -> Cke_ecdhe gxb
      | HSM.Dhe -> Cke_dhe gxb in
    let msg = HSM.M12_client_key_exchange (
      clientKeyExchange_serializer32 kex cke) in
    let ha = verifyDataHashAlg_of_ciphersuite (mode.Negotiation.n_cipher_suite) in
    let digestClientKeyExchange = HSL.send_tag #ha hs.log (HSL.Msg12 msg) in
    let cfin_key, app_keys = KS.ks_client12_set_session_hash hs.ks digestClientKeyExchange in
    register hs app_keys;
    // we send CCS then Finished;  we will use the new keys only after CCS
    let cvd = TLSPRF.finished12 ha cfin_key Client digestClientKeyExchange in
    let fin = HSM.M12_finished cvd in
    let digestClientFinished = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 fin) false in
    hs.state := (
      if nst then
         C_wait_NST false
      else
        C_wait_CCS (false, digestClientFinished));
    InAck false false)

let client_R_ServerFinished hs f digestNewSessionTicket digestServerFinished =
  trace "client_R_ServerFinished";
  let sfin_key = KS.ks12_finished_key hs.ks in
  let mode = Negotiation.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite mode.Negotiation.n_cipher_suite in
  let expected_svd = TLSPRF.finished12 ha sfin_key Server digestNewSessionTicket in
  if f = expected_svd
  then (
    let cvd = TLSPRF.finished12 ha sfin_key Client digestServerFinished in
    let _ = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 (HSM.M12_finished cvd)) true in
    hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
    InAck false false // send_CCS_tag buffers the complete
  )
  else
    InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digestNewSessionTicket)

let client_ServerFinished hs f digestClientFinished =
  let sfin_key = KS.ks12_finished_key hs.ks in
  let mode = Negotiation.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite mode.Negotiation.n_cipher_suite in
  let expected_svd = TLSPRF.finished12 ha sfin_key Server digestClientFinished in
  //let expected_svd = TLSPRF.verifyData (mode.Negotiation.n_protocol_version,mode.Negotiation.n_cipher_suite) sfin_key Server digestClientFinished in
  if f = expected_svd
  then (
    hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
    InAck false true // Client 1.2 ATK
    )
  else
    InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digestClientFinished)

let client_NewSessionTicket_12 (hs:hs) (resume:bool) (digest:Hashing.anyTag) (st: HSM.newSessionTicket12)
  : St incoming =
  let open Parsers.NewSessionTicket12 in
  let open TLS.Callbacks in
  trace ("Processing ticket: "^Bytes.print_bytes st.ticket);

  hs.state := C_wait_CCS (resume, digest);
  let cfg = Negotiation.local_config hs.nego in
  let tcb = cfg.ticket_callback in
  let mode = Negotiation.getMode hs.nego in
  let Some sni = Bytes.iutf8_opt (Negotiation.get_sni mode.Negotiation.n_offer) in

  let (_msId, ms) = KS.ks12_ms hs.ks in
  let info = TLS.Callbacks.TicketInfo_12 (
    mode.Negotiation.n_protocol_version,
    mode.Negotiation.n_cipher_suite,
    Negotiation.emsFlag mode) in

  tcb.new_ticket tcb.ticket_context sni st.ticket info ms;
  InAck false false

(*** TLS 1.3 ***)

let client_ClientFinished_13 hs digestServerFinished ocr cfin_key =
  let mode = Negotiation.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite (mode.Negotiation.n_cipher_suite) in
  let digest =
    match ocr with
    | Some cr ->
      let open Parsers.Certificate13 in
      let c = ({certificate_request_context = Bytes.empty_bytes; certificate_list = []}) in
      HandshakeLog.send_tag #ha hs.log (HSL.Msg13 (HSM.M13_certificate c))
    | None -> digestServerFinished in
  let (| finId, cfin_key |) = cfin_key in
  let cvd = HMAC.mac cfin_key digest in
  let digest_CF = HSL.send_tag #ha hs.log (HSL.Msg13 (HSM.M13_finished cvd)) in
  KS.ks_client13_cf hs.ks digest_CF; // For Post-HS
  Epochs.incr_reader hs.epochs; // to ATK
  HSL.send_signals hs.log (Some (true, false)) true; //was: Epochs.incr_writer hs.epochs
  hs.state := C_Complete // full_mode (cvd,svd); do we still need to keep those?

let client_ServerFinished_13 hs ee ocr oc ocv
  svd digestCert digestCertVerify digestServerFinished =
  let oc =
    let open Parsers.Certificate13 in
    match oc with | None -> None | Some c -> Some c.certificate_list in
  let cfg = Negotiation.local_config hs.nego in
  match Negotiation.clientComplete_13 hs.nego ee ocr oc ocv digestCert with
  | Error z -> InError z
  | Correct mode ->
    // ADL: 4th returned value is the exporter master secret.
       // should be passed to application somehow --- store in Nego? We need agreement.
       let (sfin_key, cfin_key, app_keys, exporter_master_secret) = KS.ks_client13_sf hs.ks digestServerFinished in
       let (| finId, sfin_key |) = sfin_key in
       if not (HMAC.verify sfin_key digestCertVerify svd)
       then InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^Bytes.print_bytes digestCertVerify )
       else
       begin
         export hs exporter_master_secret;
         register hs app_keys; // ATKs are ready to use in both directions

         // EOED emitting (not used for QUIC)
         if Negotiation.zeroRTT mode && not cfg.is_quic then
         begin
           trace "Early data accepted; emitting EOED.";
           let ha = Negotiation.hashAlg mode in
           let digestEOED = HSL.send_tag #ha hs.log (HSL.Msg13 (HSM.M13_end_of_early_data ())) in
           HSL.send_signals hs.log (Some (false, false)) false;
           hs.state := C13_sent_EOED digestEOED ocr cfin_key;
           InAck false false
         end
         else
         begin
           (if Negotiation.zeroRTT mode then trace "Early data accepted (QUIC, no EOED)."
           else trace "Early data rejected");
           client_ClientFinished_13 hs digestServerFinished ocr cfin_key;
           InAck true false // Client 1.3 ATK; next the client will read again to send Finished, writer++, and the Complete signal
         end
       end // moving to C_Complete

let c13_NewSessionTicket hs st13 =
  let open TLS.Callbacks in
  let open Parsers.NewSessionTicket13 in
  let open Parsers.NewSessionTicketExtension in
  let tid = st13.ticket in
  let nonce = st13.ticket_nonce in
  let age_add = st13.ticket_age_add in
  trace ("Received ticket: "^Bytes.hex_of_bytes tid^" nonce: "^Bytes.hex_of_bytes nonce);

  match !hs.state with
  | C13_complete offer sh ee server_id _fin1 _fin2 _eoed_args _ms ks ->
    let cs = sh.RealServerHello.cipher_suite in
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
    let cfg = fst hs.cfg in
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
    InAck false false)
  else
    InError (fatalAlert Illegal_parameter, "QUIC tickets must allow 0xFFFFFFFF bytes of early data")


let early_rejected st =
  match !st.cstate with
  | C13_wait_Finished1 offer sh _ _
  | C13_complete offer sh _ _ _ _ _ _ _ ->
    Negotiation.find_early_data offer.full_ch &&
    not (List.Tot.existb SHE_early_data? sh.Parsers.RealServerHello.extensions)
  | _ -> false

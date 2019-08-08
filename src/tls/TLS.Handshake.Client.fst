module TLS.Handshake.Client

open Mem
open TLSConstants
open TLSInfo
open TLSError
open FStar.HyperStack.ST
open TLS.Handshake.State

module B = FStar.Bytes
module CH = Parsers.ClientHello
module E = Extensions
module Epochs = Old.Epochs
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module HSL = HandshakeLog
module Nego = Negotiation
module HS = FStar.HyperStack
module H = Hashing.Spec

#set-options "--admit_smt_queries true"

(*** Version-agnostic messages ***)

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

private let client_Binders (hs:hs) (offer:HSM.clientHello) =
  match Nego.resume hs.nego //$ use instead the hs.client_config
  with
  | (_, []) ->
    HSL.send hs.log (HSL.Msg (HSM.M_client_hello offer))
  | (_, pskl) ->
    let binderKeys = KS.ks_client13_get_binder_keys hs.ks pskl in
    let blen = E.bindersLen offer.CH.extensions in
    HSL.send_truncated hs.log (HSL.Msg (HSM.M_client_hello offer)) blen;
    let binders = map_ST2 hs compute_binder binderKeys in
    let bb = PSK.offeredPsks_binders_serializer32 binders in
    HSL.send_raw hs.log bb;

    // Nego ensures that EDI is not sent in a 2nd ClientHello
    if Nego.find_early_data offer then
     begin
      trace "setting up 0RTT";
      let (| bid, _ |) :: _ = binderKeys in
      let ha = binderId_hash bid in
      let digest_CH = HSL.hash_tag #ha hs.log in
      let early_exporter_secret, edk = KS.ks_client13_ch hs.ks digest_CH in
      export hs early_exporter_secret;
      register hs edk;
      HSL.send_signals hs.log (Some (true, false)) false
     end

let client_ClientHello hs =
  let groups =
    match (config_of hs).max_version with
    | TLS_1p3 ->
      trace "offering ClientHello 1.3"; Some (config_of hs).offer_shares
    | _ ->
      trace "offering ClientHello 1.2"; None
    in
  // If groups = None, this is a 1.2 handshake
  // Note that groups = Some [] is valid (e.g. to trigger HRR deliberately)
  let shares = KS.ks_client_init hs.ks groups in

  // Compute & send the ClientHello offer
  match Nego.client_ClientHello hs.nego shares with
  | Error z -> Error z
  | Correct offer ->
    // Compute and send PSK binders & 0-RTT signals
    client_Binders hs offer;
    // we may still need to keep parts of ch
    hs.state := C_wait_ServerHello; //$ full_offer digest ks
    Correct ()

let client_HelloRetryRequest hs hrr =
  let open Parsers.HelloRetryRequest in
  trace("Got HRR, extensions: " ^ Nego.string_of_hrres hrr.extensions);
  let ch1 = Nego.getOffer hs.nego in
  match Nego.group_of_hrr hrr with
  | None -> InError (fatalAlert Illegal_parameter, "HRR is missing new group")
  | Some ng ->
    let Some g = CommonDH.group_of_namedGroup ng in
    let s = KS.ks_client13_hello_retry hs.ks g in
    match Nego.client_HelloRetryRequest ch1 hrr (| g, s |) with
    | Error z -> InError z
    | Correct (hri, ch2) ->
      client_Binders hs ch2;
      hs.state := C13_sent_CH2 ch1 hri;
      hs.nego.Nego.state := Nego.C_Offer ch2;
      InAck false false

let client_ServerHello s sh =
  trace "client_ServerHello";
  match Nego.client_ServerHello s.nego sh with
  | Error z -> InError z
  | Correct mode ->
    let pv = mode.Nego.n_protocol_version in
    let cfg = Nego.local_config s.nego in
    let ha = Nego.hashAlg mode in
    let ka = Nego.kexAlg mode in
    HandshakeLog.setParams s.log pv ha (Some ka) None (*?*);
    match pv with
    | TLS_1p3 ->
      begin
        trace "Running TLS 1.3";
        let digest_ServerHello = HSL.hash_tag #ha s.log in
        let hs_keys = KS.ks_client13_sh s.ks
          mode.Nego.n_server_random
          mode.Nego.n_cipher_suite
          digest_ServerHello
          mode.Nego.n_server_share
          mode.Nego.n_pski in
        register s hs_keys; // register new epoch
        if Nego.zeroRTToffer mode.Nego.n_offer then
         begin
          // Skip the 0-RTT epoch on the reading side
          Epochs.incr_reader s.epochs;
          match mode.Nego.n_pski with
          | None ->
            trace "0-RTT rejected early (no PSK was selected)";
            Epochs.incr_writer s.epochs
          | Some _ ->
            trace "0RTT potentially accepted (wait for EE to confirm)";
            // No EOED in QUIC, so we immediately enable HSK
            if cfg.is_quic then Epochs.incr_writer s.epochs
         end
        else // No EOED to send in 0-RTT epoch
          Epochs.incr_writer s.epochs; // Next flight (CFin) will use HSK
        s.state := C13_wait_Finished1;
        Epochs.incr_reader s.epochs; // Client 1.3 HSK switch to handshake key for decrypting EE etc...
        InAck true false // Client 1.3 HSK
      end
    | _ ->
      begin
        trace "Running classic TLS";
        trace ("Offered SID="^(B.print_bytes mode.Nego.n_offer.CH.session_id)^" Server SID="^(B.print_bytes mode.Nego.n_sessionID));
        if Nego.resume_12 mode then
         begin // 1.2 resumption
          trace "Server accepted our 1.2 ticket.";
          let Some (tid, Ticket.Ticket12 pv cs ems msId ms) = fst (Nego.resume s.nego) in
          let pv' = mode.Nego.n_protocol_version in
          let cs' = mode.Nego.n_cipher_suite in
          let sr = mode.Nego.n_server_random in
          let nst = Nego.sendticket_12 mode in
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
         end
      end

let client_ServerHello_HRR s ch1 hri sh =
  trace "client_ServerHello";
  match Nego.check_retry ch1 hri sh with
  | Error z -> InError z
  | Correct () ->
    client_ServerHello s sh

(*** TLS 1.2 ***)

private let convert_kex = function
  | Kex_RSA -> Correct HSM.Rsa
  | Kex_DHE -> Correct HSM.Dhe
  | Kex_ECDHE -> Correct HSM.Ecdhe
  | _ -> fatal Internal_error "Incorrect key exchange selected for 1.2"

let client_ServerHelloDone hs c ske_bytes ocr =
  trace "processing ...ServerHelloDone";
  let kex = Nego.kexAlg (Nego.getMode hs.nego) in
  match convert_kex kex with
  | Error z -> InError z
  | Correct kex ->
  match HSM.serverKeyExchange_parser32 kex ske_bytes with
  | None -> InError (fatalAlert Decode_error, "invalid client key exchange")
  | Some (ske, _) ->
  match Nego.client_ServerKeyExchange hs.nego c kex ske ocr with
  | Error z -> InError z
  | Correct mode -> (
    (match ocr with
    | None -> ()
    | Some cr ->
      trace "processing certificate request (TODO)";
      HSL.send hs.log (HSL.Msg12 (HSM.M12_certificate [])));
    let nst = Nego.sendticket_12 mode in
    let gy = Some?.v (mode.Nego.n_server_share) in // already set in KS
    let gx =
      KS.ks_client12_full_dh hs.ks
      mode.Nego.n_server_random
      mode.Nego.n_protocol_version
      mode.Nego.n_cipher_suite
      (Nego.emsFlag mode) // a flag controlling the use of ems
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
    let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
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
  let mode = Nego.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite mode.Nego.n_cipher_suite in
  let expected_svd = TLSPRF.finished12 ha sfin_key Server digestNewSessionTicket in
  if f = expected_svd
  then (
    let cvd = TLSPRF.finished12 ha sfin_key Client digestServerFinished in
    let _ = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 (HSM.M12_finished cvd)) true in
    hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
    InAck false false // send_CCS_tag buffers the complete
  )
  else
    InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^B.print_bytes digestNewSessionTicket)

let client_ServerFinished hs f digestClientFinished =
  let sfin_key = KS.ks12_finished_key hs.ks in
  let mode = Nego.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite mode.Nego.n_cipher_suite in
  let expected_svd = TLSPRF.finished12 ha sfin_key Server digestClientFinished in
  //let expected_svd = TLSPRF.verifyData (mode.Nego.n_protocol_version,mode.Nego.n_cipher_suite) sfin_key Server digestClientFinished in
  if f = expected_svd
  then (
    hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
    InAck false true // Client 1.2 ATK
    )
  else
    InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^B.print_bytes digestClientFinished)

let client_NewSessionTicket_12 (hs:hs) (resume:bool) (digest:Hashing.anyTag) (st: HSM.newSessionTicket12)
  : St incoming =
  let open Parsers.NewSessionTicket12 in
  let open TLS.Callbacks in
  trace ("Processing ticket: "^B.print_bytes st.ticket);

  hs.state := C_wait_CCS (resume, digest);
  let cfg = Nego.local_config hs.nego in
  let tcb = cfg.ticket_callback in
  let mode = Nego.getMode hs.nego in
  let Some sni = B.iutf8_opt (Nego.get_sni mode.Nego.n_offer) in

  let (_msId, ms) = KS.ks12_ms hs.ks in
  let info = TLS.Callbacks.TicketInfo_12 (
    mode.Nego.n_protocol_version,
    mode.Nego.n_cipher_suite,
    Nego.emsFlag mode) in

  tcb.new_ticket tcb.ticket_context sni st.ticket info ms;
  InAck false false

(*** TLS 1.3 ***)

let client_ClientFinished_13 hs digestServerFinished ocr cfin_key =
  let mode = Nego.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
  let digest =
    match ocr with
    | Some cr ->
      let open Parsers.Certificate13 in
      let c = ({certificate_request_context = B.empty_bytes; certificate_list = []}) in
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
  let cfg = Nego.local_config hs.nego in
  match Nego.clientComplete_13 hs.nego ee ocr oc ocv digestCert with
  | Error z -> InError z
  | Correct mode ->
    // ADL: 4th returned value is the exporter master secret.
       // should be passed to application somehow --- store in Nego? We need agreement.
       let (sfin_key, cfin_key, app_keys, exporter_master_secret) = KS.ks_client13_sf hs.ks digestServerFinished in
       let (| finId, sfin_key |) = sfin_key in
       if not (HMAC.verify sfin_key digestCertVerify svd)
       then InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^B.print_bytes digestCertVerify )
       else
       begin
         export hs exporter_master_secret;
         register hs app_keys; // ATKs are ready to use in both directions

         // EOED emitting (not used for QUIC)
         if Nego.zeroRTT mode && not cfg.is_quic then
         begin
           trace "Early data accepted; emitting EOED.";
           let ha = Nego.hashAlg mode in
           let digestEOED = HSL.send_tag #ha hs.log (HSL.Msg13 (HSM.M13_end_of_early_data ())) in
           HSL.send_signals hs.log (Some (false, false)) false;
           hs.state := C13_sent_EOED digestEOED ocr cfin_key;
           InAck false false
         end
         else
         begin
           (if Nego.zeroRTT mode then trace "Early data accepted (QUIC, no EOED)."
           else trace "Early data rejected");
           client_ClientFinished_13 hs digestServerFinished ocr cfin_key;
           InAck true false // Client 1.3 ATK; next the client will read again to send Finished, writer++, and the Complete signal
         end
       end // moving to C_Complete

let client_NewSessionTicket_13 hs st13 =
  let open TLS.Callbacks in
  let open Parsers.NewSessionTicket13 in
  let open Parsers.NewSessionTicketExtension in
  let tid = st13.ticket in
  let nonce = st13.ticket_nonce in
  let age_add = st13.ticket_age_add in
  trace ("Received ticket: "^(B.hex_of_bytes tid)^" nonce: "^(B.hex_of_bytes nonce));
  let mode = Nego.getMode hs.nego in
  let CipherSuite13 ae h = mode.Nego.n_cipher_suite in
  let ed = List.Tot.find NSTE_early_data? st13.extensions in

  let now = UInt32.uint_to_t (FStar.Date.secondsFromDawn()) in
  let info = TicketInfo_13 TLS.Callbacks.({
    ticket_nonce = Some nonce;
    time_created = now;
    ticket_age_add = age_add;
    allow_early_data = Some? ed;
    allow_dhe_resumption = true;
    allow_psk_resumption = true;
    early_cs = mode.Nego.n_cipher_suite;
    identities = (B.empty_bytes, B.empty_bytes); // TODO certs
  }) in

  let psk = KS.ks_client13_rms_psk hs.ks nonce in
  let Some sni = B.iutf8_opt (Nego.get_sni mode.Nego.n_offer) in
  let cfg = Nego.local_config hs.nego in
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

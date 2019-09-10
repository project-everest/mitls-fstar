module TLS.Handshake.Server

open Mem
open TLSConstants
open TLSInfo
open TLSError

open FStar.Bytes
open FStar.HyperStack.ST
open TLS.Handshake.Machine

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
module SH = Parsers.RealServerHello


#set-options "--admit_smt_queries true"

private let serverHello (m:Nego.mode) =
  let open Nego in
  HSM.M_server_hello (HSM.serverHello_of_sh SH.({
    version = minPV TLS_1p2 m.n_protocol_version;
    random = m.n_server_random;
    session_id = m.n_sessionID;
    cipher_suite = name_of_cipherSuite m.n_cipher_suite;
    compression_method = NullCompression;
    extensions = m.n_server_extensions;
   }))

private let verify_binder (hs:hs) (bkey:(i:HMAC.binderId & bk:KS.binderKey i))
  (tag:HMAC.tag (HMAC.HMAC_Binder (dfst bkey))) tlen
  : ST bool
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let (| bid, bk |) = bkey in
  let digest_CH0 = HSL.hash_tag_truncated #(binderId_hash bid) hs.log tlen in
  HMAC.verify bk digest_CH0 tag

private let consistent_truncation (x:option E.offeredPsks) =
  match x with
  | None -> true
  | Some psk -> List.length psk.E.identities = List.length psk.E.binders

// When sending a TLS 1.2 flight
private let server_ServerHelloDone (hs:hs) : St incoming =
  trace "Sending ...ServerHelloDone";
  let mode = Nego.getMode hs.nego in
  let cr = mode.Nego.n_offer.CH.random in
  let csr = cr @| mode.Nego.n_server_random in
  let Some (chain, sa) = mode.Nego.n_server_cert in // Server cert chosen in Nego.server_ClientHello
  match mode.Nego.n_server_share with
  | None ->
    InError (fatalAlert Handshake_failure, perror __SOURCE_FILE__ __LINE__ "no shared supported group")
  | Some (| g, gy |)  ->
    let sv = CommonDH.serialize gy in
    let tbs = Nego.to_be_signed mode.Nego.n_protocol_version Server (Some csr) sv in
    match Nego.sign hs.nego tbs with
    | Error z -> InError z
    | Correct sig ->
      let ske = sv @| Parsers.CertificateVerify13.certificateVerify13_serializer32 sig in
      HandshakeLog.send hs.log (HSL.Msg12 (HSM.M12_certificate (Cert.chain_down chain)));
      HandshakeLog.send hs.log (HSL.Msg12 (HSM.M12_server_key_exchange ske));
      HandshakeLog.send hs.log (HSL.Msg12 (HSM.M12_server_hello_done ()));
      hs.state := S_wait_CCS1;
      InAck false false // Server 1.2 ATK

let server_ClientHello_resume12 hs offer mode app_exts : St incoming =
  trace "accepted TLS 1.2 resumption";
  let pv = mode.Nego.n_protocol_version in
  let cr = mode.Nego.n_offer.CH.random in
  let ha = Nego.hashAlg mode in
  let ka = Nego.kexAlg mode in
  HSL.setParams hs.log pv ha (Some ka) None;
  
  let Some tid = Nego.find_sessionTicket offer in
  let Some (pv, cs, ems, msId, ms) = Ticket.check_ticket12 tid in
  let adk = KS.ks_server12_resume hs.ks cr pv cs ems msId ms in
  register hs adk;
  
  match Nego.server_ServerShare hs.nego None app_exts with
  | Error z -> InError z
  | Correct mode ->
    let digestSessionTicket =
      if Nego.sendticket_12 mode then
         // Save hashing the SH if we don't send a ticket
         let _ = HSL.send hs.log (HSL.Msg (serverHello mode)) in
         let ticket =
           let open Parsers.NewSessionTicket12 in
           {lifetime_hint = 3600ul; ticket = tid; } in
         HSL.send_tag #ha hs.log (HSL.Msg12 (HSM.M12_new_session_ticket ticket))
      else
        HSL.send_tag #ha hs.log (HSL.Msg (serverHello mode))
      in
    let digestServerFinished =
      let fink = KS.ks12_finished_key hs.ks in
      let svd = TLSPRF.finished12 ha fink Server digestSessionTicket in
      HSL.send_CCS_tag #ha hs.log (HSL.Msg12 (HSM.M12_finished svd)) true in
    hs.state := S_wait_CCS2 digestServerFinished;
    InAck false false

let server_ClientHello_12 hs offer mode app_exts : St incoming =
  match Nego.kexAlg mode with
  | Kex_DHE | Kex_ECDHE ->
    let Some g = Nego.chosenGroup mode in
    let cr = mode.Nego.n_offer.CH.random in
    let pv = mode.Nego.n_protocol_version in
    let cs = mode.Nego.n_cipher_suite in
    let cfg = Nego.local_config hs.nego in
    let ems = cfg.extended_master_secret && (Nego.emsFlag mode) in
    let gy = KS.ks_server12_init_dh hs.ks cr pv cs ems g in
    match Nego.server_ServerShare hs.nego (Some (| g, gy |)) app_exts with
    | Error z -> InError z
    | Correct mode ->
      let ha = Nego.hashAlg mode in
      let ka = Nego.kexAlg mode in
      HSL.setParams hs.log pv ha (Some ka) None;
      server_ServerHelloDone hs
  | _ -> InError (fatalAlert Handshake_failure, "Unsupported RSA key exchange")

let server_ClientHello_13 hs offer mode app_exts : St incoming =
  let cs = mode.Nego.n_cipher_suite in
  let cr = mode.Nego.n_offer.CH.random in
  let g_gx = mode.Nego.n_client_share in
  let oshare =
    match mode.Nego.n_pski with
    | None ->
      let server_share, None = KS.ks_server13_init hs.ks cr cs None g_gx in
      Correct server_share
    | Some i ->
      trace ("accepted TLS 1.3 psk #"^string_of_int i);
      let Some psks = Nego.find_clientPske offer in
      let tlen = E.offeredPsks_binders_size32 psks.E.binders in
      let Some id = List.Tot.nth psks.E.identities i in
      let Some tag = List.Tot.nth psks.E.binders i in
      let pskid = Some (PSK.coerce id.E.identity) in
      let server_share, Some binderKey = KS.ks_server13_init hs.ks cr cs pskid g_gx in
      if verify_binder hs binderKey tag tlen
      then Correct server_share
      else fatal Bad_record_mac "binder verification failed"
    in
  match oshare with
  | Error z -> InError z
  | Correct oshare ->
    match Nego.server_ServerShare hs.nego oshare app_exts with
    | Error z -> InError z
    | Correct mode ->
      let ha = Nego.hashAlg mode in
      let ka = Nego.kexAlg mode in
      HSL.setParams hs.log TLS_1p3 ha (Some ka) None;
      let ha = verifyDataHashAlg_of_ciphersuite mode.Nego.n_cipher_suite in
      let digestClientHelloBinders = HSL.hash_tag #ha hs.log in
      let digestServerHello = HSL.send_tag #ha hs.log (HSL.Msg (serverHello mode)) in
      let zeroing = Nego.zeroRTT mode in
      if zeroing  then (
         let early_exporter_secret, zero_keys =
           KS.ks_server13_0rtt_key hs.ks digestClientHelloBinders in
         export hs early_exporter_secret;
         register hs zero_keys;
         Epochs.incr_reader hs.epochs // Be ready to read 0-RTT data
      );
      // signal key change after writing ServerHello
      HSL.send_signals hs.log (Some (false, zeroing)) false;
      trace "derive handshake keys";
      let hs_keys = KS.ks_server13_sh hs.ks digestServerHello in
      register hs hs_keys;
      hs.state := S13_sent_ServerHello;
      InAck zeroing false

// Only if we are sure this is the 1st CH
let server_ClientHello1 hs offer : St incoming =
  match Nego.server_ClientHello hs.nego offer with
  | Error z -> InError z
  | Correct (Nego.ServerRetry hrr) ->
    // Create a cookie, for stateless retry
    let ha = TLS.Cookie.hrr_ha hrr in 
    let digest = HandshakeLog.hash_tag #ha hs.log in 
    let hrr = TLS.Cookie.append digest empty_bytes hrr in
    let m = HSM.M_server_hello (HSM.serverHello_of_hrr hrr) in
    HSL.send hs.log (HSL.Msg m);
    hs.state := S13_wait_CH2 offer hrr;
    InAck false false
  | Correct (Nego.ServerMode mode cert app_exts) ->
    if Nego.resume_12 mode then
       server_ClientHello_resume12 hs offer mode app_exts
    else if mode.Nego.n_protocol_version = TLS_1p3 then
      server_ClientHello_13 hs offer mode app_exts
    else
      server_ClientHello_12 hs offer mode app_exts

// Only if this is a 2nd CH (stateful or stateless)
let server_ClientHello2 hs ch1 hrr ch2 app_cookie =
  let open Parsers.OfferedPsks in
  let binders = Nego.find_clientPske ch2 in
  trace ("Processing ClientHello2" ^ (match binders with
    | None -> "" | Some opsk -> " with "
    ^ string_of_int (List.length opsk.binders) ^ " binder(s)"));
  Nego.trace_offer ch2;
  match Nego.server_ClientHello2 hs.nego ch1 hrr ch2 app_cookie with
  | Error z -> InError z
  | Correct (Nego.ServerMode mode _ app_exts) ->
    server_ClientHello_13 hs ch2 mode app_exts

// May be 1st or 2nd CH (depending on cookie)
let server_ClientHello hs offer =
  let open Parsers.OfferedPsks in
  let binders = Nego.find_clientPske offer in
  trace ("Processing ClientHello1" ^ (match binders with
    | None -> "" | Some opsk -> " with "
    ^ string_of_int (List.length opsk.binders) ^ " binder(s)"));
  Nego.trace_offer offer;
  if not (consistent_truncation binders)
    then InError (fatalAlert Illegal_parameter, "unexpected number of binders")
  else
    match Nego.find_cookie offer with
    | None -> server_ClientHello1 hs offer
    | Some c ->
      match TLS.Cookie.decrypt c with
      | Error z -> InError (fatalAlert Handshake_failure, "failed to decrypt cookie")
      | Correct (digest, extra, hrr) ->
        trace ("Loaded stateless retry cookie with app_data="^hex_of_bytes extra);
        trace ("Setting transcript to CH1 hash "^hex_of_bytes digest);
        HandshakeLog.load_stateless_cookie hs.log hrr digest;
	// FIXME(adl) need to compute ch1 from ch2 + hrr
	// or weaken authentication (e.g. exists ch1. Nego.valid_retry ch1 hrr ch2)
	server_ClientHello2 hs offer hrr offer extra

(*** TLS 1.2 ***)

private let convert_kex = function
  | Kex_RSA -> Correct HSM.Rsa
  | Kex_DHE -> Correct HSM.Dhe
  | Kex_ECDHE -> Correct HSM.Ecdhe
  | _ -> fatal Internal_error "Incorrect key exchange selected for 1.2"

(* receive ClientKeyExchange; CCS *)
let server_ClientCCS1 hs cke digestCCS1 =
    // FIXME support optional client c and cv
    // let ems = n.n_extensions.ne_extended_ms in // ask Nego?
    trace ("process Client CCS (hash = "^hex_of_bytes digestCCS1);
    let mode = Nego.getMode hs.nego in
    let Some (|g,  _|) = mode.Nego.n_server_share in
    trace ("staged parsing of share: "^(hex_of_bytes cke));
    let open Parsers.ClientKeyExchange in
    match convert_kex (Nego.kexAlg mode) with
    | Error z -> InError z
    | Correct kex ->
    match clientKeyExchange_parser32 kex cke with
    | None -> InError (fatalAlert Decode_error, "failed parsing of untagged CKE")
    | Some (Cke_ecdhe gyb, l)
    | Some (Cke_dhe gyb, l) ->
    trace ("Inner format: "^(hex_of_bytes gyb));
    match len cke = l, CommonDH.parse g gyb with
    | _, None
    | false, _ -> InError(fatalAlert Decode_error,
        perror __SOURCE_FILE__ __LINE__
          "Cannot parse client share in CKE")
    | true, Some gy ->
      let app_keys = KS.ks_server12_cke_dh hs.ks (| g, gy |) digestCCS1 in
      register hs app_keys;
      Epochs.incr_reader hs.epochs;
      // use the new reader; will use the new writer only after sending CCS
      hs.state := S_wait_Finished1 digestCCS1; // keep digest to verify the Client Finished
      InAck true false  // Server 1.2 ATK

let server_ClientFinished hs cvd digestCCS digestClientFinished =
  trace "Process Client Finished";
  let fink = KS.ks12_finished_key hs.ks in
  let mode = Nego.getMode hs.nego in
  let cfg = Nego.local_config hs.nego in
  let pv = mode.Nego.n_protocol_version in
  let cs = mode.Nego.n_cipher_suite in
  let alpha = (mode.Nego.n_protocol_version, mode.Nego.n_cipher_suite) in
  let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
  let expected_cvd = TLSPRF.finished12 ha fink Client digestCCS in
  //let expected_cvd = TLSPRF.verifyData alpha fink Client digestCCS in
  if cvd = expected_cvd
  then
    //let svd = TLSPRF.verifyData alpha fink Server digestClientFinished in
    let digestTicket =
      if Nego.sendticket_12 mode then
         let (msId, ms) = KS.ks12_ms hs.ks in
         let ticket = Ticket.Ticket12 pv cs (Nego.emsFlag mode) msId ms in
         let ticket = Parsers.NewSessionTicket12.({
           lifetime_hint = 3600ul;
           ticket = Ticket.create_ticket false ticket;
         }) in
         HSL.send_tag #ha hs.log (HSL.Msg12 (HSM.M12_new_session_ticket ticket))
      else digestClientFinished in
    let svd = TLSPRF.finished12 ha fink Server digestTicket in
    let unused_digest = HSL.send_CCS_tag #ha hs.log (HSL.Msg12 (HSM.M12_finished svd)) true in
    hs.state := S_Complete;
    InAck false false // Server 1.2 ATK; will switch write key and signal completion after sending
  else
    InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)

let server_ClientFinished2 hs cvd digestSF digestCF =
  trace "Process Client Finished";
  let fink = KS.ks12_finished_key hs.ks in
  let mode = Nego.getMode hs.nego in
  let pv = mode.Nego.n_protocol_version in
  let cs = mode.Nego.n_cipher_suite in
  let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
  let expected_cvd = TLSPRF.finished12 ha fink Client digestSF in
  if cvd = expected_cvd then
    (hs.state := S_Complete; InAck false false)
  else
    InError (fatalAlert Decode_error, "Client Finished MAC did not verify: expected digest "^print_bytes digestSF)

(*** TLS 1.3 ***)

let server_ServerFinished_13 hs =
    trace "prepare Server Finished";
    let mode = Nego.getMode hs.nego in
    let cfg = Nego.local_config hs.nego in
    let kex = Nego.kexAlg mode in
    let pv = mode.Nego.n_protocol_version in
    let cs = mode.Nego.n_cipher_suite in
    let exts = mode.Nego.n_server_extensions in
    let eexts = match mode.Nego.n_encrypted_extensions with | None -> [] | Some ee -> ee in
    let sh_alg = sessionHashAlg pv cs in
    let halg = verifyDataHashAlg_of_ciphersuite cs in
    
    let digestFinished =
      match kex with
      | Kex_ECDHE -> // [Certificate; CertificateVerify]
        HSL.send hs.log (HSL.Msg13 (HSM.M13_encrypted_extensions eexts));
        let Some (chain, sa) = mode.Nego.n_server_cert in
        let c = Parsers.Certificate13.({
          certificate_request_context = empty_bytes;
          certificate_list = chain}) in
        let digestSig = HSL.send_tag #halg hs.log (HSL.Msg13 (HSM.M13_certificate c)) in
        let tbs = Nego.to_be_signed pv Server None digestSig in
        (match Nego.sign hs.nego tbs with
        | Error z -> Error z
        | Correct signature ->
	  Correct (HSL.send_tag #halg hs.log (HSL.Msg13 (HSM.M13_certificate_verify signature))))
      | _ -> // PSK
        Correct (HSL.send_tag #halg hs.log (HSL.Msg13 (HSM.M13_encrypted_extensions eexts)))
      in

    match digestFinished with
    | Correct digestFinished ->
      let (| sfinId, sfin_key |) = KS.ks_server13_server_finished hs.ks in
      let svd = HMAC.mac sfin_key digestFinished in
      let digestServerFinished = HSL.send_tag #halg hs.log (HSL.Msg13 (HSM.M13_finished svd)) in
      let app_keys, ems = KS.ks_server13_sf hs.ks digestServerFinished in
      export hs ems;
      register hs app_keys;
      HSL.send_signals hs.log (Some (true,false)) false;

      hs.state := (
        if Nego.zeroRTT mode && not cfg.is_quic then
          S13_wait_EOED // EOED sent with 0-RTT: dont increment reader
        else
          (Epochs.incr_reader hs.epochs; // Turn on HS key
          S13_wait_Finished2 digestServerFinished)
      );
      Correct()
    | Error z -> Error z

let server_EOED hs digestEOED =
  trace "Process EOED (increment reader to HS key)";
  Epochs.incr_reader hs.epochs;
  hs.state := S13_wait_Finished2 digestEOED;
  InAck false false

let server_Ticket13 hs app_data =
  let (| li, rmsid, rms |) = KS.ks_server13_rms hs.ks in
  let cfg = Nego.local_config hs.nego in
  let mode = Nego.getMode hs.nego in
  let cs = mode.Nego.n_cipher_suite in
  let age_add = Random.sample32 4ul in
  let age_add = Parse.uint32_of_bytes age_add in

  let now = UInt32.uint_to_t (FStar.Date.secondsFromDawn()) in
  let ticket = Ticket.Ticket13 cs li rmsid rms empty_bytes now age_add app_data in

  let tb = Ticket.create_ticket false ticket in
  trace ("Sending ticket: "^(print_bytes tb));
  trace ("Application data in ticket: "^(print_bytes app_data));
  let ticket_ext =
    let open Parsers.NewSessionTicketExtension in
    match cfg.max_early_data with
    | Some max_ed -> [NSTE_early_data max_ed]
    | None -> [] in
  let tnonce, _ = split_ tb 12 in

  HSL.send hs.log (HSL.Msg13 (HSM.M13_new_session_ticket
  Parsers.NewSessionTicket13.({
    ticket_lifetime = 3600ul;
    ticket_age_add = age_add;
    ticket_nonce = tnonce;
    ticket = tb;
    extensions = ticket_ext;
  })))

let server_ClientFinished_13 hs f digestBeforeClientFinished digestClientFinished clientAuth =
   trace "Process Client Finished";
   match clientAuth with
   | Some (c,cv,digest) ->
      InError(fatalAlert Internal_error,
        perror __SOURCE_FILE__ __LINE__ "Client CertificateVerify validation not implemented")
   | None ->
       let (| i, cfin_key |) = KS.ks_server13_client_finished hs.ks in
       let mode = Nego.getMode hs.nego in
       if HMAC.verify cfin_key digestBeforeClientFinished f
       then
        begin
         KS.ks_server13_cf hs.ks digestClientFinished;
         hs.state := S_Complete;
         let cfg = Nego.local_config hs.nego in
         (match Nego.find_psk_key_exchange_modes mode.Nego.n_offer with
         | [] -> trace ("Not sending a ticket: no PSK key exchange mode advertised")
         | psk_kex ->
           if Some? cfg.send_ticket then server_Ticket13 hs (Some?.v cfg.send_ticket));
         Epochs.incr_reader hs.epochs; // finally start reading with AKTs
         InAck true true  // Server 1.3 ATK
        end
       else InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)


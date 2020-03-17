module TLS.Handshake.Server

open Mem
open TLSConstants
open TLSInfo
open TLSError

open FStar.HyperStack.ST
open TLS.Handshake.Machine
open TLS.Handshake.Messaging

(* FStar libraries *)
module HS = FStar.HyperStack
module B = FStar.Bytes
module LB = LowStar.Buffer
module M = LowStar.Modifies

(* Internal dependencies *)
module E = Extensions
module HSM = HandshakeMessages
module HMAC = Old.HMAC.UFCMA
module KS = Old.KeySchedule
module Nego = Negotiation
module Transcript = TLS.Handshake.Transcript
module Send = TLS.Handshake.Send
module Recv = TLS.Handshake.Receive
module Epochs = Old.Epochs

(* Hashing *)
module H = Hashing.Spec
module HD = Spec.Hash.Definitions
module HI = EverCrypt.Hash.Incremental

(* Parsers (for easy access to conflicting field names *)
module PF = TLS.Handshake.ParseFlights
module CH = Parsers.ClientHello
module SH = Parsers.ServerHello
module SHK = Parsers.SHKind
module HRRK = Parsers.HRRKind

#set-options "--admit_smt_queries true"

(* See common functions in TLS.Handshake.Machine
private let rec verify_binder (bkey:list Nego.bkey13) (tags: list binders)
//  (tag:HMAC.tag (HMAC.HMAC_Binder (dfst bkey))) tlen
  : ST bool
    (requires fun h0 -> binders_for bkey tags)
    (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  let (| bid, bk |) = bkey in
  let digest_CH0 = HSL.hash_tag_truncated #(binderId_hash bid) hs.log tlen in
  HMAC.verify bk digest_CH0 tag
*)

private let consistent_truncation (x:option E.offeredPsks) =
  match x with
  | None -> true
  | Some psk -> List.length psk.E.identities = List.length psk.E.binders

private let keyShareEntry_of_share ((| g, gx |):Nego.share)
  : Parsers.ServerHelloExtension.serverHelloExtension_SHE_key_share = 
  let r = CommonDH.format #g gx in
  //19-06-17 push to CommonDH? 
  assume(Parsers.KeyShareEntry.keyShareEntry_bytesize r <= 65535);
  r

(*** TLS 1.2 functions **)

(*
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
*)

(*
// Bramch after selecting TLS 1.3
private let server_ClientHello_13 (ch:HSM.ch) (sh:HSM.sh) (ks:s_init)
  (#r:rgn) (m:msg_state r ParseFlights.F_s_Idle (HSM.sh_random sh))
  (gx:option Nego.share) (use_psk:option Nego.bkey13) (cert:Nego.certNego)
  : St Receive.incoming
  =
  let cs = HSM.sh_cipher_suite sh in
  let cr = ch.CH.random in
  let opskid = match use_psk with Some (id,_) -> Some id | None -> None in
  let ks', ogy, obk = KS.ks_server13_init ks cr cs opskid gx in
  let sh' = Nego.server_KeyShare sh ogy in // Write server share extension
  match extend m.sending m.digest (HSM.M_server_hello sh) [MSH.M_client_hello ch] with
  | Error z -> Error z
  | Correct tx' ->
    let digest_sh = transcript_extract m.digest tx' in
    let ks'', hs_keys = KS.ks_server13_sh ks' digest_sh in
    register m.epochs hs_keys;
    Correct ks''
*)

  (*
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
         register hs zero_keys
//         Epochs.incr_reader hs.epochs // Be ready to read 0-RTT data
      );
      // signal key change after writing ServerHello
      HSL.send_signals hs.log (Some (false, zeroing)) false;
      trace "derive handshake keys";
      let hs_keys = KS.ks_server13_sh hs.ks digestServerHello in
      register hs hs_keys;
      hs.state := S13_sent_ServerHello;
      InAck zeroing false
  *)

// Only if we are sure this is the 1st CH
let server_ClientHello1 st offer
  : St Receive.incoming =
  trace ("server_ClientHello "^(B.hex_of_bytes (HSM.clientHello_serializer32 offer)));
  let Server region config r = st in
  let S_wait_ClientHello random recv = !r in
  let soffer = {retry = None; s_ch = offer} in

  match Nego.server_ClientHello config offer with
  | Error z -> Recv.InError z
  | Correct (Nego.ServerRetry hrr) -> admit()
  | Correct (Nego.ServerAccept13 cert cs13 opsk) ->
    let cs, opski, g_gx =
      match cs13 with
      | Nego.PSK_EDH j g_gx cs -> cs, (Some j), g_gx
      | Nego.JUST_EDH g_gx cs -> cs, None, (Some g_gx)
      in
    let CipherSuite13 ae ha = cs in
    let di = transcript_start region ha None offer false in
    let tag0 = transcript_extract di in
    trace ("ClientHello/Binder digest: "^(B.hex_of_bytes tag0));
    let (ks, ogy, obk) = KS.ks_server13_init random (offer.CH.random) cs config.is_quic opsk g_gx in
    let ogyb = match ogy with None -> None | Some gy -> Some (keyShareEntry_of_share gy) in
    let accept_0rtt =  Some? config.max_early_data &&
      Some 0us = opski && Nego.find_early_data offer in

    // Verify selected binder, update tag, di, tx
    let binder_ok = match obk with
      | None -> Correct tag0
      | Some bk ->
        let open Parsers.OfferedPsks in
        let open Parsers.OfferedPsks_binders in
        let Some opsk = Nego.find_clientPske offer in
        let Some binder = List.Tot.nth opsk.binders (UInt16.v (Some?.v opski)) in

        // Complete the TCH hash (wasteful, should be fixed when interface is repr_pos)
        let (| _, chr |) = get_handshake_repr (HSM.M_client_hello offer) in
	let lbl = Transcript.LR_CompleteTCH chr in
	Transcript.extend di lbl;

        if HMAC.verify (dsnd bk) tag0 binder then
          Correct (transcript_extract di)
        else Error (fatalAlert Bad_record_mac, "Failed to verify selected binder")
      in

    match binder_ok with
    | Error z -> Recv.InError z
    | Correct tag1 ->
      let pfs = if accept_0rtt then PF.F_s13_wait_EOED else PF.F_s13_wait_Finished2 in
      let ms0 : msg_state region pfs random ha =
        create_msg_state region pfs random ha (Some di) (Some recv) in
      if accept_0rtt then (
        let ees, ets = KS.ks_server13_0rtt_key ks tag1 in
         export ms0.epochs ees;
         register ms0.epochs ets
//         Epochs.incr_reader ms0.epochs
      );
      let she = Nego.server_clientExtensions TLS_1p3 config cs None opski ogyb false offer.CH.extensions in
      let ee = Nego.encrypted_clientExtensions TLS_1p3 config cs None opski ogyb false offer.CH.extensions in
      let sh = SH.({
        version = TLS_1p2;
	is_hrr = Parsers.ServerHello_is_hrr.(
	  ServerHello_is_hrr_false ({
	  tag = random;
	  value = SHK.({
            session_id = offer.CH.session_id;
	    cipher_suite = name_of_cipherSuite cs;
	    compression_method = Parsers.CompressionMethod.NullCompression;
	    extensions = she
          });
	}));
      }) in
      let tag_SH = LB.alloca 0z (H.hash_len ha) in
      let sd = Send.signals ms0.sending (Some (false, accept_0rtt)) false in
      trace("ServerHello bytes: "^(Bytes.hex_of_bytes (HSM.serverHello_serializer32 sh)));
      match Send.send_tag_sh di sd (HSM.M_server_hello sh) tag_SH with
      | Error z -> Recv.InError z
      | Correct sd ->
        let digest_SH = B.of_buffer (H.hash_len ha) tag_SH in
        let ks', hsk = KS.ks_server13_sh ks digest_SH in
	trace ("Transcript ServerHello: "^(Bytes.hex_of_bytes digest_SH));
        register ms0.epochs hsk;
	let ms1 : msg_state region pfs random ha = {ms0 with sending=sd} in
        r := S13_sent_ServerHello soffer sh ee accept_0rtt ms1 cert ks';
        Recv.InAck false false

(*
    // Create a cookie, for stateless retry
    let ha = TLS.Cookie.hrr_ha hrr in 
    let digest = HandshakeLog.hash_tag #ha hs.log in 
    let hrr = TLS.Cookie.append digest empty_bytes hrr in
    let m = HSM.M_server_hello (HSM.serverHello_of_hrr hrr) in
    HSL.send hs.log (HSL.Msg m);
    hs.state := S13_wait_CH2 offer hrr;
    InAck false false
  | Correct (Nego.ServerAccept13 sh ee psk dhg cert) ->
    (match server_ClientHello_13 with
    | Correct ks' ->
      r := S13_sent_ServerHello ch sh ee m cert ks'';
      InAck true false
    | Error z -> InError z)
    if Nego.resume_12 mode then
       server_ClientHello_resume12 hs offer mode app_exts
    else if mode.Nego.n_protocol_version = TLS_1p3 then
      server_ClientHello_13 hs offer mode app_exts
    else
      server_ClientHello_12 hs offer mode app_exts
*)

let server_ClientHello2 hs ch1 hrr ch2 app_cookie =
  admit()

(*
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
*)

let server_ClientHello = server_ClientHello1

(*** TLS 1.2 ***)

let server_ClientCCS1 st = admit()

let server_ClientFinished hs cvd digestCCF digestCF = admit()

let server_ClientFinished2 hs cvd digestSF digestCF = admit()

(*
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
//      Epochs.incr_reader hs.epochs;
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
*)

(*** TLS 1.3 ***)

let server_ServerFinished_13 hs =
  trace ("server_ServerFinished_13");
  let Server region config r = hs in
  let S13_sent_ServerHello soffer sh ee accept_0rtt ms cert ks = !r in
  let ha = Nego.selected_ha sh in
  let eem = HSM.M13_encrypted_extensions ee in
  let tag_F = LB.alloca 0z (H.hash_len ha) in
  match Send.send13 #ha ms.digest ms.sending eem with
  | Error z -> Error z
  | Correct send ->
    let send_cert =
      match cert with
      | None ->
        Transcript.extract_hash ms.digest tag_F;
        Correct (send, NoServerCert)
      | Some (cert_ptr, sa) ->
        let tag_C = LB.alloca 0z (H.hash_len ha) in
        let chain12 = TLS.Callbacks.cert_format_cb config.cert_callbacks cert_ptr in
	let chain = Parsers.Certificate13.({
	  certificate_request_context = Bytes.empty_bytes;
	  certificate_list = Cert.chain_up chain12;
	  }) in
	match Send.send_tag13 ms.digest send (HSM.M13_certificate chain) tag_C with
	| Error z -> Error z
	| Correct send ->
	  let digest_C = Bytes.of_buffer (H.hash_len ha) tag_C in
          trace ("Hash up to Cert: "^(Bytes.hex_of_bytes digest_C));
	  let tbs = Nego.to_be_signed TLS_1p3 TLSConstants.Server None digest_C in
	  match TLS.Callbacks.cert_sign_cb config.cert_callbacks cert_ptr sa tbs with
	  | None -> fatal Bad_certificate
	    (perror __SOURCE_FILE__ __LINE__ "Failed to sign with selected certificate.")
          | Some sigv ->
            let cv = HSM.(({algorithm = sa; signature = sigv})) in
	    match Send.send_tag13 ms.digest send (HSM.M13_certificate_verify cv) tag_F with
	    | Error z -> Error z
	    | Correct send ->
	      Correct (send, ServerCert cert_ptr chain cv)
     in
    match send_cert with
    | Error z -> Error z
    | Correct (send, cert_ctx) ->
      let (| sfinId, sfin_key |) = KS.ks_server13_get_sfk ks in
      let digest_F = Bytes.of_buffer (H.hash_len ha) tag_F in
      trace ("Hash for Finished: "^(Bytes.hex_of_bytes digest_F));
      let svd = HMAC.mac sfin_key digest_F in
      let fin = HSM.(M13_finished svd) in
      match Send.send_tag13 ms.digest send fin tag_F with
      | Error z -> Error z
      | Correct send ->
        let digest_SF = Bytes.of_buffer (H.hash_len ha) tag_F in
        trace ("Hash up to SF: "^(Bytes.hex_of_bytes digest_SF));
        let ks, app_keys, ems = KS.ks_server13_sf ks digest_SF in 
	export ms.epochs ems;
        register ms.epochs app_keys;
        let send = Send.signals send (Some (true,false)) false in
	let mode = S13_mode soffer sh ee cert_ctx in
	let eoed_done = not (Nego.zeroRTT sh) || config.is_quic in
	let pf = if eoed_done then ParseFlights.F_s13_wait_Finished2
	         else ParseFlights.F_s13_wait_EOED in
	let ms : msg_state region pf _ ha = {ms with sending = send} in
        r := S13_wait_Finished2 mode (Ghost.hide svd) eoed_done ms ks;
        Correct()

let server_EOED hs digestEOED = admit()

let server_Ticket13 hs app_data =
  let Server region cfg r = hs in
  let S13_complete mode cvd svd ms ks = !r in
  let (| li, rmsid, rms |) = KS.ks_server13_rms ks in
  
  let sh = S13_mode?.sh mode in
  let cs = Nego.selected_cipher_suite sh in
  let age_add = Random.sample32 4ul in
  let age_add = Parse.uint32_of_bytes age_add in

  let now = UInt32.uint_to_t (FStar.Date.secondsFromDawn()) in
  let ticket = Ticket.Ticket13 cs li rmsid rms Bytes.empty_bytes now age_add app_data in

  let tb = Ticket.create_ticket false ticket in
  trace ("Sending ticket: "^(Bytes.print_bytes tb));
  trace ("Application data in ticket: "^(Bytes.print_bytes app_data));
  let ticket_ext =
    let open Parsers.NewSessionTicketExtension in
    match cfg.max_early_data with
    | Some max_ed -> [NSTE_early_data max_ed]
    | None -> [] in
  let tnonce, _ = Bytes.split_ tb 12 in

  let nst = Parsers.NewSessionTicket13.({
    ticket_lifetime = 3600ul;
    ticket_age_add = age_add;
    ticket_nonce = tnonce;
    ticket = tb;
    extensions = ticket_ext;
  }) in

  match Send.send13 ms.digest ms.sending (HSM.M13_new_session_ticket nst) with
  | Correct snd' ->
    let ms1 = {ms with sending = snd'} in
    r := S13_complete mode cvd svd ms1 ks;
    true
  | Error z -> false

(*
  let (| _, chr |) = get_handshake_repr (HSM.M_client_hello offer) in
  let lbl = Transcript.LR_CompleteTCH chr in
  Transcript.extend di lbl;
  let ks', hsk = KS.ks_server13_sh ks digest_SH in
  trace ("Transcript ServerHello: "^(Bytes.hex_of_bytes digest_SH));
  register ms0.epochs hsk;
  let ms1 : msg_state region pfs random ha = {ms0 with sending=sd} in
  r := S13_sent_ServerHello soffer sh ee accept_0rtt ms1 cert ks';
*)

let server_ClientFinished_13 hs cvd client_cert =
  trace "Process Client Finished";
  let Server region config r = hs in
  let S13_wait_Finished2 mode svd eoed_done ms ks = !r in
  
  let ha = Nego.selected_ha (S13_mode?.sh mode) in
  let tag = LB.alloca 0z (H.hash_len ha) in
  Transcript.extract_hash ms.digest tag;
  let digest_CF = B.of_buffer (H.hash_len ha) tag in

  // Add CF to transcript, get final tag
  let (| _, cfr |) = get_handshake13_repr (HSM.M13_finished cvd) in
  let lbl = Transcript.LR_HSM13 cfr in
  Transcript.extend ms.digest lbl;
  Transcript.extract_hash ms.digest tag;
  let digest_F = B.of_buffer (H.hash_len ha) tag in

   match client_cert with
   | Some _ -> // (c,cv,digest) ->
      Recv.InError(fatalAlert Internal_error,
        perror __SOURCE_FILE__ __LINE__ "Client CertificateVerify validation not implemented")
   | None ->
     let (| i, cfin_key |) = KS.ks_server13_get_cfk ks in
     if HMAC.verify cfin_key digest_CF cvd
     then
       begin
       let ks = KS.ks_server13_cf ks digest_F in
       let ms1 : msg_state region PF.F_s_Idle _ ha = ms in
       r := S13_complete mode (Ghost.hide cvd) svd ms1 ks;
       (match Nego.find_psk_key_exchange_modes (S13_mode?.offer mode).s_ch with
       | [] -> trace ("Not sending a ticket: no PSK key exchange mode advertised")
       | psk_kex ->
         if Some? config.send_ticket then
	   let _ = server_Ticket13 hs (Some?.v config.send_ticket)
	 in ());
       Recv.InAck true true  // Server 1.3 ATK
       end
     else Recv.InError (fatalAlert Bad_record_mac, "Finished MAC did not verify: expected digest "^Bytes.print_bytes cvd)

(*
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
          ( //Epochs.incr_reader hs.epochs; // Turn on HS key
          S13_wait_Finished2 digestServerFinished)
      );
      Correct()
    | Error z -> Error z

let server_EOED hs digestEOED =
  trace "Process EOED (increment reader to HS key)";
//  Epochs.incr_reader hs.epochs;
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
//         Epochs.incr_reader hs.epochs; // finally start reading with AKTs
         InAck true true  // Server 1.3 ATK
        end
       else InError (fatalAlert Decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)

*)

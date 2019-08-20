module TLS.Handshake

open FStar.String
open FStar.Heap
open FStar.HyperStack
open FStar.Seq
open FStar.Error
open FStar.Bytes

open TLSError
open TLSInfo
open TLS.Callbacks
open TLSConstants
open Range
open Old.Epochs

//open TLS.Handshake.Client
open TLS.Handshake.Server

module U32 = FStar.UInt32
module MS = FStar.Monotonic.Seq
module HS = FStar.HyperStack
module Nego = Negotiation
module HST = FStar.HyperStack.ST
module Epochs = Old.Epochs
module KS = Old.KeySchedule
module HMAC_UFCMA = Old.HMAC.UFCMA
module HSM = HandshakeMessages
module HSL = HandshakeLog
module CH = Parsers.ClientHello
module SH = Parsers.RealServerHello
module HRR = Parsers.HelloRetryRequest
module FSH = Parsers.ServerHello

// consider adding an optional (resume: option sid) on the client side
// for now this bit is not explicitly authenticated.

// Well-formed logs are all prefixes of (Epoch; Complete)*; Error
// This crucially assumes that TLS keeps track of OutCCS and InCCSAck
// so that it knows which reader & writer to use (not always the latest ones):
// - within InCCSAck..OutCCS, we still use the older writer
// - within OutCCS..InCCSAck, we still use the older reader
// - otherwise we use the latest readers and writers

// abstract invariant; depending only on the HS state (not the epochs state)
// no need for an epoch states invariant here: the HS never modifies them

#set-options "--admit_smt_queries true"

(* -------------------- Control Interface ---------------------- *)

let create (parent:rid) cfg role =
  let r = new_region parent in
  let log = HSL.create r None (* cfg.max_version (Nego.hashAlg nego) *) in
  //let nonce = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
  let ks, nonce = KS.create #r role cfg.is_quic in
  let nego = Nego.create r role cfg nonce in
  let epochs = Epochs.create r nonce in
  let state = ralloc r (if role = Client then C_init else S_Idle) in
  let x: hs = HS role nego log ks epochs state in //17-04-17 why needed?
  x

let rehandshake s c = FStar.Error.unexpected "rehandshake: not yet implemented"

let rekey s c = FStar.Error.unexpected "rekey: not yet implemented"

let send_ticket hs app_data =
  if is_post_handshake hs then
    let _ = server_Ticket13 hs app_data in true
  else false

let request s c = FStar.Error.unexpected "request: not yet implemented"

let invalidateSession hs = ()
// ADL: disabling this for top-level API testing purposes
// FStar.Error.unexpected "invalidateSession: not yet implemented"


(* ------------------ Outgoing -----------------------*)

let next_fragment_bounded (hs:hs) i (max:nat) =
    trace "next_fragment";
    let outgoing = HSL.write_at_most hs.log i max in
    match outgoing, !hs.state with
    // when the output buffer is empty, we send extra messages in two cases
    // we prepare the initial ClientHello; or
    // after sending ServerHello in plaintext, we continue with encrypted traffic
    // otherwise, we just returns buffered messages and signals
    | HSL.Outgoing None None false, C_init ->
      (match client_ClientHello hs with
      | Error z -> Error z
      | Correct () -> Correct(HSL.write_at_most hs.log i max))
    | HSL.Outgoing None None false, S13_sent_ServerHello ->
      (match server_ServerFinished_13 hs with
      | Error z -> Error z
      | Correct () -> Correct(HSL.write_at_most hs.log i max))
    | HSL.Outgoing None None false, C13_sent_EOED d ocr cfk ->
      client_ClientFinished_13 hs d ocr cfk;
      Correct(HSL.write_at_most hs.log i max)
    | _ -> Correct outgoing // nothing to do

let next_fragment (hs:hs) i =
  next_fragment_bounded hs i max_TLSPlaintext_fragment_length

let to_be_written (hs:hs) =
  HSL.to_be_written hs.log

(* ----------------------- Incoming ----------------------- *)

let rec recv_fragment (hs:hs) #i rg f =
  let open HandshakeLog in
  let open HandshakeMessages in
  let recv_again r =
    match r with
    // only case where the next incoming flight may already have been buffered.
    | InAck false false -> recv_fragment hs #i (0,0) empty_bytes
    | r -> r  in
  trace "recv_fragment";
  let h0 = HST.get() in
  let flight = receive hs.log f in
  match flight with
  | Error z -> InError z
  | Correct None -> InAck false false // nothing happened
  | Correct (Some (ms,ts)) ->
    match !hs.state, ms, ts with

    (* CLIENT *)

    | C_init, _, _ -> InError (fatalAlert Unexpected_message, "Client hasn't sent hello yet")
    | C_wait_ServerHello, [Msg (M_server_hello sh)], [] ->
      if HSM.is_hrr sh then
        client_HelloRetryRequest hs (HSM.get_hrr sh)
      else
        recv_again (client_ServerHello hs (HSM.get_sh sh))

    // 1.2 full: wrap these two into a single received flight with optional [cr]
    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_server_hello_done ())], [_] ->
      client_ServerHelloDone hs c ske None

    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_certificate_request cr); Msg12 (M12_server_hello_done ())], [_] ->
      client_ServerHelloDone hs c ske (Some cr)

    | C_wait_Finished2 digestClientFinished, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_ServerFinished hs f digestClientFinished

    | C_wait_NST resume, [Msg12 (M12_new_session_ticket st)], [digestNewSessionTicket] ->
      client_NewSessionTicket_12 hs resume digestNewSessionTicket st

    // 1.3; wrap these three into single flight with optional cr and optional (c;cv).
    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client_ServerFinished_13 hs ee None (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate_request cr); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client_ServerFinished_13 hs ee (Some cr) (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_finished f)],
                        [digestEE; digestServerFinished] ->
      client_ServerFinished_13 hs ee None None None f None digestEE digestServerFinished

    | C_Complete, [Msg13 (M13_new_session_ticket st13)], [_] ->
      client_NewSessionTicket_13 hs st13

    // 1.2 resumption
    | C_wait_R_Finished1 digestNewSessionTicket, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_R_ServerFinished hs f digestNewSessionTicket digestServerFinished

    (* SERVER *)
    | S_Idle, [Msg (M_client_hello ch)], []  -> server_ClientHello hs ch

    // 1.2 full
    | S_wait_Finished1 digest, [Msg12 (M12_finished f)], [digestClientFinish] ->
      server_ClientFinished hs f digest digestClientFinish

    // 1.2 resumption
    | S_wait_CF2 digest, [Msg12 (M12_finished f)], [digestClientFinished] -> // classic resumption
      server_ClientFinished2 hs f digest digestClientFinished

    // 1.3, similarly group cases with optional ((c,cv)?
    | S13_wait_EOED, [Msg13 (M13_end_of_early_data ())], [digestEOED] ->
      server_EOED hs digestEOED

    | S13_wait_Finished2 digestServerFinished,
      [Msg13 (M13_finished f)], [digestClientFinished] ->
      server_ClientFinished_13 hs f digestServerFinished digestClientFinished None

    | S13_wait_Finished2 digestServerFinished,
      [Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)], [digestSigned; digestCertVerify; digestClientFinished] ->
      server_ClientFinished_13 hs f digestCertVerify digestClientFinished (Some (c, cv, digestSigned))

    // are we missing the case with a Certificate but no CertificateVerify?
    | _,  _, _ ->
//      trace "DISCARD FLIGHT"; InAck false false
      InError(fatalAlert Unexpected_message, "unexpected flight")

// TODO check CCS once committed to TLS 1.3 yields an alert
let recv_ccs (hs:hs) =
  let open HandshakeLog in
  let open HandshakeMessages in
  trace "recv_ccs";
  // Draft 22 CCS during HRR
  // Because of stateless HRR, this may also happen as the very first message before CH (!!!)
  let is_hrr = Nego.is_hrr hs.nego in
  let is_idle = S_Idle? !hs.state in
  if is_hrr || is_idle then
    begin
    trace "IGNORING CCS (workaround for implementations that send CCS after HRR)";
    InAck false false
    end
  else
    // CCS triggers completion of the incoming flight of messages.
    let mode = Nego.getMode hs.nego in
    match receive_CCS #(Nego.hashAlg mode) hs.log with
    | Error z -> InError z
    | Correct (ms, digests, digestCCS) ->
      match !hs.state, ms, digests with
      // client full handshake
      | C_wait_CCS (resume, digest), [], [] ->
        Epochs.incr_reader hs.epochs;
        hs.state := (if resume then C_wait_R_Finished1 digest else C_wait_Finished2 digest);
        InAck true false

      | S_wait_CCS2 digestServerFinished, [], [] -> (
        Epochs.incr_reader hs.epochs;
        hs.state := S_wait_CF2 digestServerFinished;
        InAck true false)

      | S_wait_CCS1, [Msg12 (M12_client_key_exchange cke)], [digest_to_finish] ->
        // assert (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE))
        // getting two copies of the same digest?
        server_ClientCCS1 hs cke digestCCS

      | _, _, _ ->
        trace "WARNING: bad CCS";
        InError(fatalAlert Unexpected_message, "CCS received at wrong time")


let authorize s ch = FStar.Error.unexpected "authorize: not yet implemented"

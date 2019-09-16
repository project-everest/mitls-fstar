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
//open TLS.Handshake.Server

module U32 = FStar.UInt32
module MS = FStar.Monotonic.Seq
module HS = FStar.HyperStack
module Nego = Negotiation
module HST = FStar.HyperStack.ST
module Epochs = Old.Epochs
module KS = Old.KeySchedule
module HMAC_UFCMA = Old.HMAC.UFCMA
module HSM = HandshakeMessages

module Client = TLS.Handshake.Client
module Server = TLS.Handshake.Server
module Receive = TLS.Handshake.Receive 
module PF = TLS.Handshake.ParseFlights

module LP = LowParse.Low.Base

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

let is_0rtt_offered hs = admit()

let xkeys_of hs = 
  let n = Machine.nonce hs in 
  FStar.Monotonic.Seq.i_read (Machine.epochs hs n).Epochs.exporter

open TLS.Handshake.Machine 


/// now integrating Outline.fst; see also
/// https://github.com/project-everest/mitls-fstar/issues/231 and
/// https://github.com/project-everest/mitls-fstar/blob/afromher_dev/src/tls/Test.TLS.Send.fst

(* -------------------- Control Interface ---------------------- *)

//19-09-11 we'll need to split it between clients and servers, since their config differ. 

let create (parent:rid) cfg role =
  assert(role == TLSConstants.Client);
  let r = new_region parent in
  // let log = HSL.create r None (* cfg.max_version (Nego.hashAlg nego) *) in
  //let nonce = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
  let ks, nonce = KS.create #r role cfg.is_quic in
  // let nego = Nego.create r role cfg nonce in
  // let epochs = Epochs.create r nonce in
  let resume = None, [] in //TODO 19-09-13 cfg.use_tickets in 
  let config: client_config = cfg, resume in 
  let state = ralloc r (C_init nonce) in
  Machine.Client r config state

let rehandshake s c = FStar.Error.unexpected "rehandshake: not yet implemented"

let rekey s c = FStar.Error.unexpected "rekey: not yet implemented"

//19-09-13 TODO 
let send_ticket hs app_data =
//if is_post_handshake hs then
//  let _ = server_Ticket13 hs app_data in true
//else 
    false

let request s c = FStar.Error.unexpected "request: not yet implemented"

let invalidateSession hs = ()
// ADL: disabling this for top-level API testing purposes
// FStar.Error.unexpected "invalidateSession: not yet implemented"


(* ------------------ Outgoing -----------------------*)

// We send extra messages in three cases: we prepare the initial
// ClientHello; or the output buffer is empty, after sending
// ServerHello in plaintext, we continue with encrypted traffic.
// Otherwise, we just returns buffered messages and signals.

let rec next_fragment_bounded hs i max =
  trace "next_fragment";
  match hs with 
  | Client region config r -> (
    let st0 = !r in 
    if C_init? st0 then (
      match Client.client_ClientHello hs with
      | Error z -> Error z
      | Correct () -> next_fragment_bounded hs i max )
    else 
      let ms0 = Machine.client_ms st0 in 
      let sending, result = Send.write_at_most ms0.sending i max in
      let ms1 = { ms0 with sending = sending } in 
      let st1 = set_client_ms st0 ms1 in 
      // any simpler way to update substate? 
      r := st1; 
      match result, st1 with
      | Send.Outgoing None None false, 
        C13_complete offer sh ee server_id fin1 fin2 (Some _) ms ks -> (
        match Client.client13_Finished2 hs with
        | Error z -> Error z 
        | Correct _ -> next_fragment_bounded hs i max )

      | _ -> Correct result // nothing to do
    )
  | Server region config r -> ( 
    let st0 = !r in 
    let ms0 = Machine.server_ms st0 in 
    let sending, result = Send.write_at_most ms0.sending i max in
    let ms1 = { ms0 with sending = sending } in 
    let st1 = set_server_ms st0 ms1 in 
    r := st1; 
    match result, st1 with
    | Send.Outgoing None None false, 
      S13_sent_ServerHello _ _ _ -> (
      match Server.server_ServerFinished_13 hs with
      | Error z -> Error z 
      | Correct _ -> next_fragment_bounded hs i max )
    | _ -> Correct result // nothing to do
    )

let next_fragment hs i =
  next_fragment_bounded hs i max_TLSPlaintext_fragment_length

let to_be_written hs =
  let sto = 
    match hs with
    | Machine.Client region config r -> 
      let st = !r in (client_ms st).sending
    | Server region config r -> 
      let st = !r in (server_ms st).sending in 
  Send.to_be_written sto

(* ----------------------- Incoming ----------------------- *)

let buffer_received_fragment ms #i rg f = ms

// Some parsing functions translating between low-level representations
// obtained after receiving, and high-level values passed as arguments
// to the processing functions
// TODO: Implement this. This is likely a well-chosen call to Parsers.ServerHello.something
assume
val parse_wait_serverHello
  (#st:Receive.state)
  (res:PF.c_wait_ServerHello (Receive.cslice_of st) & UInt32.t) :
  ST Parsers.ServerHello.serverHello
    (requires fun h -> PF.valid_c_wait_ServerHello st.Receive.rcv_from (snd res) (fst res) h)
    // Maybe a bit too strong?
    (ensures fun h0 _ h1 -> h0 == h1)

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"
// #set-options "--admit_smt_queries true"
let rec recv_fragment hs #i rg f =
  let open HandshakeMessages in
  let recv_again r =
    match r with
    // only case where the next incoming flight may already have been buffered.
    | Receive.InAck false false -> recv_fragment hs #i (0,0) empty_bytes
    | r -> r  in
  // trace "recv_fragment";
  let h0 = HST.get() in
  match hs with 
  | Client region config r -> (
    match !r  with
    | C_init _ ->
      Receive.InError (
        fatalAlert Unexpected_message,
        "Client hasn't sent hello yet (to be statically excluded)")

    | C_wait_ServerHello offer0 ms0 ks0 -> (
      // AF: How do we ensure this statically? Should this be handled
      // by buffer_received_fragment, returning an Error if the
      // property does not hold? CF: yes; or realloc the buffer if
      // this is problematic.
      let rcv0 = ms0.receiving in 
      assume Receive.(UInt32.v rcv0.rcv_to + Bytes.length f <= UInt32.v rcv0.rcv_b.LP.len);
      let rcv1 = buffer_received_fragment rcv0 #i rg f in
      match Receive.receive_c_wait_ServerHello rcv1 with
      | Error z -> Receive.InError z
      | Correct (x, rcv2) ->
        let v = C_wait_ServerHello offer0 ({ms0 with receiving = rcv2}) ks0 in
        let h1 = HST.get() in
        r := v;
        let h2 = HST.get() in
        match x with
        | None -> Receive.InAck false false // nothing happened
        | Some sh_msg -> (
          let sh = parse_wait_serverHello sh_msg in
          let h3 = HST.get() in
          if HSM.is_hrr sh then
            // TODO adjust digest, here or in the transition call
            Client.client_HelloRetryRequest hs sh
          else
            // TODO extend digest[..sh]
            // transitioning to C12_wait_ServerHelloDone or C13_wait_Finished1;
            let r = Client.client_ServerHello hs sh in
            // TODO check that ms1.receiving is set for processing the next flight
            recv_again r )))
(*
  | C12_wait_ServerHelloDone ch sh ms0 ks -> (
    let rcv1 = buffer_received_fragment ms0.receiving f in
    match TLS.Handshake.Receive.receive_c12_wait_ServerHelloDone rcv1 with
    | Error z -> InError z
    | Correct (x, rcv2) ->
      hs.cstate := C12_wait_ServerHelloDone ch sh ({ms0 with receiving = rcv2}) ks;
      match x with
      | None -> InAck false false // nothing happened
      | Some x ->
      // TODO extend digest[..ServerHelloDone]
      // let c, ske, ocr = admit() in
      // client_ServerHelloDone hs c ske None
        admit()
      )

  | C13_wait_Finished1 offer sh ms0 ks -> (
    let rcv1 = buffer_received_fragment ms0.receiving f in
    match TLS.Handshake.Receive.receive_c13_wait_Finished1 rcv1
    with
    | Error z -> InError z
    | Correct (x, rcv2) ->
      hs.cstate := C13_wait_Finished1 offer sh ({ms0 with receiving = rcv2}) ks;
      match x with
      | None -> InAck false false // nothing happened
      | Some x ->
        // covering 3 cases (see old code for details)
        // we need to extract these high-level values from the flight:
        let ee, ocr, oc, ocv, fin1, otag0, tag1, tag_fin1 = admit() in
        client_ServerFinished13 hs offer sh ee ocr oc ocv fin1 otag0 tag1 tag_fin1
      )

  | C13_Complete _ _ _ _ _ _ _ ms0 _ ->
    let ms1 = buffer_received_fragment ms0 #i rg f in
    // TODO two sub-states: waiting for fin2 or for the post-handshake ticket.
    match HSL.Receive.receive_c_wait_ServerHello 12_wait_ServerHelloDone st b f_begin f_end with
    | Error z -> InError z
    | Correct None -> InAck false false // nothing happened
    | Correct (Some x) ->

  , [Msg13 (M13_new_session_ticket st13)], [_] ->
      client_NewSessionTicket_13 hs st13

  // 1.2 full: wrap these two into a single received flight with optional [cr]
    | C_wait_Finished2 digestClientFinished, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_ServerFinished hs f digestClientFinished

    | C_wait_NST resume, [Msg12 (M12_new_session_ticket st)], [digestNewSessionTicket] ->
      client_NewSessionTicket_12 hs resume digestNewSessionTicket st

    // 1.2 resumption
    | C_wait_R_Finished1 digestNewSessionTicket, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_R_ServerFinished hs f digestNewSessionTicket digestServerFinished
*)

  | _ ->
    Receive.InError (fatalAlert Unexpected_message, "TBC")



(* The old, but more complete version, to be merged: 

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
        client_HelloRetryRequest hs sh
      else
        recv_again (client_ServerHello hs sh)

    | C13_sent_CH2 ch1 hrr, [Msg (M_server_hello sh)], [] ->
      if HSM.is_hrr sh then 
        InError (fatalAlert Unexpected_message, "server sent a second retry request")
      else
        recv_again (client_ServerHello_HRR hs ch1 hrr sh)

    // 1.2 full: wrap these two into a single received flight with optional [cr]
    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_server_hello_done ())], [_] ->
      client12_ServerHelloDone hs c ske None

    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_certificate_request cr); Msg12 (M12_server_hello_done ())], [_] ->
      client12_ServerHelloDone hs c ske (Some cr)

    | C_wait_Finished2 digestClientFinished, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client12_ServerFinished hs f digestClientFinished

    | C_wait_NST resume, [Msg12 (M12_new_session_ticket st)], [digestNewSessionTicket] ->
      client12_NewSessionTicket hs resume digestNewSessionTicket st

    // 1.3; wrap these three into single flight with optional cr and optional (c;cv).
    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client13_Finished1 hs ee None (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate_request cr); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client13_Finished1 hs ee (Some cr) (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_finished f)],
                        [digestEE; digestServerFinished] ->
      client13_Finished1 hs ee None None None f None digestEE digestServerFinished

    | C_Complete, [Msg13 (M13_new_session_ticket st13)], [_] ->
      client13_NewSessionTicket hs st13

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

    // 1.3, retry (second CH)
    | S13_wait_CH2 ch1 hrr, [Msg (M_client_hello ch2)], [] ->
      server_ClientHello2 hs ch1 hrr ch2 empty_bytes

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
*)

// TODO check CCS once committed to TLS 1.3 yields an alert
let recv_ccs hs =
  admit()
  //19-09-13 TBC 
(*  
  trace "recv_ccs";
  // Draft 22 CCS during HRR
  // Because of stateless HRR, this may also happen as the very first message before CH (!!!)
  let is_hrr = C13_sent_CH2? !hs.state in
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
*)


let authorize s ch = FStar.Error.unexpected "authorize: not yet implemented"

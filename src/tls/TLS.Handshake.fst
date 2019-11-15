module TLS.Handshake

open FStar.Error
open FStar.Bytes
open FStar.HyperStack.ST

open TLSError
open TLSConstants
open TLSInfo
open TLS.Callbacks

open Range
open Old.Epochs

open TLS.Handshake.Machine
open TLS.Handshake.Messaging

module LB = LowStar.Buffer
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
module Send = TLS.Handshake.Send
module Recv = TLS.Handshake.Receive 
module PF = TLS.Handshake.ParseFlights
module LP = LowParse.Low.Base

#set-options "--admit_smt_queries true"
#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 20"

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

let is_0rtt_offered hs = false // FIXME

#push-options "--max_ifuel 0 --z3rlimit 32"
let xkeys_of hs = 
  let n = Machine.nonce hs in
  let es = Machine.epochs hs n in 
  //let h = Mem.get() in assert(modifies_none h h);
  FStar.Monotonic.Seq.i_read es.Epochs.exporter

/// now integrating Outline.fst; see also
/// https://github.com/project-everest/mitls-fstar/issues/231 and
/// https://github.com/project-everest/mitls-fstar/blob/afromher_dev/src/tls/Test.TLS.Send.fst

(* -------------------- Control Interface ---------------------- *)

//19-09-11 we'll need to split it between clients and servers, since their config differ. 
// FIXME(adl) keeping a single function for client and server to maintain current API
let create (parent:rid) cfg role =
  let r = new_region parent in
  let nonce = Nonce.mkHelloRandom role r in
  match role with
  | TLSConstants.Client ->
    // FIXME(adl) Nego.unseal_tickets cfg.use_tickets
    let resume = None, [] in
    let config: client_config = cfg, resume in 
    let state = ralloc r (C_init nonce) in
    Machine.Client r config state
  | TLSConstants.Server ->
    // We need to pre-allocate the receiving buffer
    // but we can't pre-allocate the full msg_state
    // because the hash is not known
    let in_buf_len = 16000ul in
    let b_in = LB.malloc r 0z in_buf_len in
    let ms0 = Recv.create (LP.make_slice b_in in_buf_len) in
    let state = ralloc r (S_wait_ClientHello nonce ms0) in
    Machine.Server r cfg state

let rehandshake s c = FStar.Error.unexpected "rehandshake: not yet implemented"

let rekey s c = FStar.Error.unexpected "rekey: not yet implemented"

let send_ticket hs app_data =
  match hs with
  | Machine.Client _ _ _ -> false
  | Machine.Server _ _ s ->
    match !s with
    | S13_complete _ _ _ _ ks ->
//  let _ = server_Ticket13 hs app_data in true
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

let rec next_fragment_bounded hs i (max32: UInt32.t) =
  trace ("next_fragment_bounded");
  match hs with 
  | Client region config r -> (
    let st0 = !r in 
    if C_init? st0 then (
      match Client.client_ClientHello hs with
      | Error z -> Error z
      | Correct () -> next_fragment_bounded hs i max32 )
    else 
      let ms0 = Machine.client_ms st0 in 
      let sending, result = Send.write_at_most ms0.sending i max32 in
      let ms1 = { ms0 with sending = sending } in 
      let st1 = set_client_ms st0 ms1 in 
      // any simpler way to update substate? 
      r := st1; 
      match result, st1 with
      | Send.Outgoing None None false, 
        C13_complete offer sh ee server_id fin1 ms (Finished_pending _ _ _) ->
	(match Client.client13_Finished2 hs with
        | Error z -> Error z 
        | Correct _ -> next_fragment_bounded hs i max32 )
      | _ -> Correct result // nothing to do
    )
  | Server region config r ->
    let st0 = !r in
    if S_wait_ClientHello? st0 then
      // Allocation of the messaging state must be delayed until
      // CH is received (to avoid re-allocation)
      Correct (Send.Outgoing None None false)
    else
      let ms0 = Machine.server_ms st0 in 
      let sending, result = Send.write_at_most ms0.sending i max32 in
      let ms1 = { ms0 with sending = sending } in 
      let st1 = set_server_ms st0 ms1 in 
      r := st1; 
      match result, st1 with
      | Send.Outgoing None None false, 
        S13_sent_ServerHello _ _ _ _ _ _ _ ->
        (match Server.server_ServerFinished_13 hs with
        | Error z -> Error z 
        | Correct _ -> next_fragment_bounded hs i max32)
      | _ -> Correct result

let next_fragment hs i =
  next_fragment_bounded hs i max_TLSPlaintext_fragment_length32

let to_be_written hs =
  if Machine.is_init hs then 0 else
  let sto = 
    match hs with
    | Machine.Client region config r -> 
      let st = !r in (client_ms st).sending
    | Server region config r -> 
      let st = !r in (server_ms st).sending in 
  Send.to_be_written sto

(* ----------------------- Incoming ----------------------- *)

module R = MITLS.Repr
module RH = MITLS.Repr.Handshake
module RH12 = MITLS.Repr.Handshake12
module RH13 = MITLS.Repr.Handshake13

inline_for_extraction noextract
let overflow () = Recv.InError (fatalAlert Internal_error, "Overflow in input buffer")

(* FIXME(adl): this should be automatic in wrap_pf_st! *)
let update_recv_pos hs pos =
 match hs with
 | Client region config r ->
   let st = !r in
   let ms0 = client_ms st in
   let ms1 = {ms0 with receiving = {ms0.receiving with Recv.rcv_from = pos}} in
   r := set_client_ms st ms1
 | Server region config r ->
   let st = !r in
   let ms0 = server_ms st in
   let ms1 = {ms0 with receiving = {ms0.receiving with Recv.rcv_from = pos}} in
   r := set_server_ms st ms1

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"
// #set-options "--admit_smt_queries true"
let rec recv_fragment hs #i rg f =
  trace ("recv_fragment: "^hex_of_bytes f);
  let open HandshakeMessages in
  // only case where the next incoming flight may already have been buffered.
  [@inline_let] let recv_again r =
    match r with
    | Recv.InAck false false -> recv_fragment hs #i (0,0) empty_bytes
    | r -> r  in
  let h0 = HST.get() in
  match hs with 
  | Client region config r ->
   begin // Client
    match !r  with
    | C_init _ ->
      trace "No CH sent (statically excluded)";
      Recv.InError (
      fatalAlert Unexpected_message,
      "Client hasn't sent hello yet (to be statically excluded)")

    | C_wait_ServerHello offer0 ms0 ks0 -> (
      match Recv.buffer_received_fragment ms0.receiving f with
      | None -> overflow ()
      | Some rcv1 ->
      trace "receive_c_wait_ServerHello";
      match Recv.receive_c_wait_ServerHello rcv1 with
      | Error z -> Recv.InError z
      | Correct (x, rcv2) ->
        r := C_wait_ServerHello offer0 ({ms0 with receiving = rcv2}) ks0;
        match x with
        | None -> Recv.InAck false false // nothing happened
        | Some (sh_msg,pos) ->
	  update_recv_pos hs pos; // FIXME should have been done in Recv_SH
          let shr = RH.serverHello (sh_msg.PF.sh_msg) in
	  let sh = shr.R.vv in
          let h3 = HST.get() in
          if HSM.is_hrr sh then
            Client.client_HelloRetryRequest hs sh
          else
            let r = Client.client_ServerHello hs sh in
            recv_again r)

    | C13_wait_Finished1 offer sh ms0 ks -> (
      match Recv.buffer_received_fragment ms0.receiving f with
      | None -> overflow ()
      | Some rcv1 ->
      trace "receive_c13_wait_Finished1";
      match TLS.Handshake.Receive.receive_c13_wait_Finished1 rcv1 with
      | Error z -> Recv.InError z
      | Correct (sflight, rcv2) ->
        r := C13_wait_Finished1 offer sh ({ms0 with receiving = rcv2}) ks;
        match sflight with
        | None -> Recv.InAck false false // nothing happened
        | Some sflight ->
	  let ee = RH13.get_ee_repr sflight.PF.ee_msg in
	  let fin = RH13.get_fin_repr (PF.Mkc13_wait_Finished1?.fin_msg sflight) in
	  let ocr = match PF.Mkc13_wait_Finished1?.cr_msg sflight with
	    | None -> None | Some cr -> let x = RH13.get_cr_repr cr in Some x.R.vv in
	  let oc_cv = match PF.Mkc13_wait_Finished1?.c_cv_msg sflight with
	    | None -> None | Some (c,cv) ->
	      let x = RH13.get_c_repr c in
	      let y = RH13.get_cv_repr cv in
	      Some (x.R.vv, y.R.vv) in
	  update_recv_pos hs (fin.R.end_pos); // FIXME(adl)!!
          Client.client13_Finished1 hs (ee.R.vv) ocr oc_cv (fin.R.vv))

    | C13_complete offer sh ee server_id fin1 ms0 (Finished_sent fin2 ks) ->
     begin
      match Recv.buffer_received_fragment ms0.receiving f with
      | None -> overflow ()
      | Some rcv1 ->
      trace "receive_c13_Complete";
      match TLS.Handshake.Receive.receive_c13_Complete rcv1 with
      | Error z -> Recv.InError z
      | Correct (nst, rcv2) ->
        r := C13_complete offer sh ee server_id fin1 ({ms0 with receiving = rcv2})
            (Finished_sent fin2 ks);
        match nst with
        | None -> Recv.InAck false false // nothing happened
        | Some nst ->
	  let nst = RH13.get_nst_repr (PF.Mkc13_Complete?.nst_msg nst) in
	  update_recv_pos hs (nst.R.end_pos); // FIXME(adl)!!
          Client.client13_NewSessionTicket hs (nst.R.vv)
     end
    | _ ->
      Recv.InError (fatalAlert Unexpected_message, "TBC")
   end // Client
  | Server region config r ->
   begin // Server
    match !r  with
    | S_wait_ClientHello n rcv0 ->
     begin
      match Recv.buffer_received_fragment rcv0 f with
      | None -> overflow ()
      | Some rcv1 ->
      match Recv.receive_s_Idle rcv1 with
      | Error z -> Recv.InError z
      | Correct (x, rcv2) ->
        match x with
        | None ->
	  // Still in PF.F_s_Idle
	  r := S_wait_ClientHello n rcv2;
	  Recv.InAck false false // nothing happened
        | Some ch ->
          let chr = RH.clientHello (ch.PF.ch_msg) in
	  let ch = chr.R.vv in
          let h3 = HST.get() in
          let r = Server.server_ClientHello hs ch in
	  update_recv_pos hs chr.R.end_pos; // FIXME(adl)!!
	  r
     end	  
    | _ ->
      Recv.InError (fatalAlert Unexpected_message,
        "Unexpected server state")
   end // Server

(*
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

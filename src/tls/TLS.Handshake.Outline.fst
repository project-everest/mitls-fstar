module TLS.Handshake.Outline

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

module Range = Range

include TLS.Handshake.Receive
include TLS.Handshake.Machine

/// Outlining our integration test (code adapted from TLS.Handshake).
/// See also https://github.com/project-everest/mitls-fstar/issues/231
/// and
/// https://github.com/project-everest/mitls-fstar/blob/afromher_dev/src/tls/Test.TLS.Send.fst

(* ----------------------- Incoming ----------------------- *)


(* OLD:
let recv_ensures (#region:rgn) (cfg:client_config) (cs:client_state region cfg) (h0:HS.mem) (result:incoming) (h1:HS.mem) =
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    w1 == w0 /\
    r1 == (if in_next_keys result then r0 + 1 else r0) /\
    (b2t (in_complete result) ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 (*/\ completed (eT s Reader h1)*) )
*)

val receive_fragment:
  // mutable client state
  #region:rgn -> hs: TLS.Handshake.Machine.t region ->
  // high-level calling convention for the incoming fragment
  #i:TLSInfo.id -> rg:Range.frange i -> f:Range.rbytes rg ->
  ST incoming
  (requires fun h0 ->
    h0 `HS.contains` hs.cstate /\
    // TODO statically exclude C_init
    True)
  (ensures fun h0 r h1 -> True)

let buffer_received_fragment ms #i rg f = ms

// TODO ms has a dependent type

// TODO copy f's contents into !hs.receiving.rcv_b between rcv_to and
// the end of the slice, probably returning indexes too, possibly
// reallocating a bigger buffer if the current one is too small
// (later?)


// the actual transitions; we should experiment with some precise pre/post
assume val client_HelloRetryRequest: #region:rgn -> hs: t region -> HSM.hrr -> St incoming
assume val client_ServerHello:       #region:rgn -> hs: t region -> HSM.sh -> St incoming
assume val client_ServerHelloDone:   #region:rgn -> hs: t region -> HSM.sh -> St incoming
assume val client_ServerFinished13:  #region:rgn -> hs: t region ->
  full_offer ->
  sh: serverHello ->
  ee: HSM.encryptedExtensions ->
  ocr: option HSM.certificateRequest13 ->
  oc: option HSM.certificate13 ->
  ocv: option HSM.certificateVerify13 ->
  svd: bytes ->
  digestCert: option Hashing.anyTag ->
  digestCertVerify: Hashing.anyTag ->
  digestServerFinished: Hashing.anyTag ->
  St incoming

open TLS.Handshake.Receive
open TLS.Handshake.Machine


#set-options "--admit_smt_queries true"
let rec receive_fragment #region hs #i rg f =
  let open HandshakeMessages in
  let recv_again r =
    match r with
    // only case where the next incoming flight may already have been buffered.
    | InAck false false -> receive_fragment hs #i (0,0) empty_bytes
    | r -> r  in
  // trace "recv_fragment";
  let h0 = HST.get() in
  match !hs.cstate with
  | C_init _ ->
    InError (
      fatalAlert Unexpected_message,
      "Client hasn't sent hello yet (to be statically excluded)")

  | C_wait_ServerHello offer0 ms0 ks0 -> (
    let rcv1 = buffer_received_fragment ms0.receiving f in
    match TLS.Handshake.Receive.receive_c_wait_ServerHello rcv1 with
    | Error z -> InError z
    | Correct (x, rcv2) ->
      hs.cstate := C_wait_ServerHello offer0 ({ms0 with receiving = rcv2}) ks0;
      match x with
      | None -> InAck false false // nothing happened
      | Some sh_msg -> (
        let sh = admit() in
        if HSM.is_hrr sh then
          // TODO adjust digest, here or in the transition call
          client_HelloRetryRequest hs (HSM.get_hrr sh)
        else
          // TODO extend digest[..sh]
          // transitioning to C12_wait_ServerHelloDone or C13_wait_Finished1;
          let r = client_ServerHello hs (HSM.get_sh sh) in
          // TODO check that ms1.receiving is set for processing the next flight
          recv_again r ))

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

  | _ ->
    InError (fatalAlert Unexpected_message, "TBC")

module Alert

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq

open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
open Range

//* moving to stateful private state
private type state = | State:
  #region: rid ->
  incoming: rref region (b:bytes { length b < 2 }) -> (* incomplete incoming alert *)
  outgoing: rref region (b:bytes { length b = 0 || length b = 2 }) -> (* empty if nothing to be sent *)
  state
// FIXME: Port to deltas and streams!

let init r0 =
  let r = new_region r0 in
  State (ralloc r empty_bytes) (ralloc r empty_bytes)

type nextReply =
    | EmptyALFrag
    | ALFrag:          rg:frange_any -> rbytes rg -> nextReply
    | LastALFrag:      rg:frange_any -> rbytes rg -> alertDescription -> nextReply
    | LastALCloseFrag: rg:frange_any -> rbytes rg -> nextReply

type recvReply =
    | ALAck
    | ALFatal of alertDescription
    | ALWarning of alertDescription
    | ALClose_notify

(* Conversions *)

let alertBytes ad =
  (* Severity (warning or fatal) is hardcoded, as specified in sec. 7.2.2 *)
  match ad with
    | AD_close_notify ->                       abyte2 (1uy,   0uy)
    | AD_unexpected_message ->                 abyte2 (2uy,  10uy)
    | AD_bad_record_mac ->                     abyte2 (2uy,  20uy)
    | AD_decryption_failed ->                  abyte2 (2uy,  21uy)
    | AD_record_overflow ->                    abyte2 (2uy,  22uy)
    | AD_decompression_failure ->              abyte2 (2uy,  30uy)
    | AD_handshake_failure ->                  abyte2 (2uy,  40uy)
    | AD_no_certificate ->                     abyte2 (1uy,  41uy)
    | AD_bad_certificate_warning ->            abyte2 (1uy,  42uy)
    | AD_bad_certificate_fatal ->              abyte2 (2uy,  42uy)
    | AD_unsupported_certificate_warning ->    abyte2 (1uy,  43uy)
    | AD_unsupported_certificate_fatal ->      abyte2 (2uy,  43uy)
    | AD_certificate_revoked_warning ->        abyte2 (1uy,  44uy)
    | AD_certificate_revoked_fatal ->          abyte2 (2uy,  44uy)
    | AD_certificate_expired_warning ->        abyte2 (1uy,  45uy)
    | AD_certificate_expired_fatal ->          abyte2 (2uy,  45uy)
    | AD_certificate_unknown_warning ->        abyte2 (1uy,  46uy)
    | AD_certificate_unknown_fatal ->          abyte2 (2uy,  46uy)
    | AD_illegal_parameter ->                  abyte2 (2uy,  47uy)
    | AD_unknown_ca ->                         abyte2 (2uy,  48uy)
    | AD_access_denied ->                      abyte2 (2uy,  49uy)
    | AD_decode_error ->                       abyte2 (2uy,  50uy)
    | AD_decrypt_error ->                      abyte2 (2uy,  51uy)
    | AD_export_restriction ->                 abyte2 (2uy,  60uy)
    | AD_protocol_version ->                   abyte2 (2uy,  70uy)
    | AD_insufficient_security ->              abyte2 (2uy,  71uy)
    | AD_internal_error ->                     abyte2 (2uy,  80uy)
    | AD_user_cancelled_warning ->             abyte2 (1uy,  90uy)
    | AD_user_cancelled_fatal ->               abyte2 (2uy,  90uy)
    | AD_no_renegotiation ->                   abyte2 (1uy, 100uy)
    | AD_unrecognized_name ->                  abyte2 (2uy, 112uy)
    | AD_unsupported_extension ->              abyte2 (2uy, 110uy)

val parseAlert: b:lbytes 2 -> Tot 
  (r: Result alertDescription { forall ad. (r = Correct ad ==> b = alertBytes ad) })
let parseAlert b =
    let b1,b2 = cbyte2 b in
    Seq.lemma_eq_intro b (abyte2 (b1,b2));
    match cbyte2 b with
    | (1uy,   0uy) -> Correct AD_close_notify
    | (2uy,  10uy) -> Correct AD_unexpected_message
    | (2uy,  20uy) -> Correct AD_bad_record_mac
    | (2uy,  21uy) -> Correct AD_decryption_failed
    | (2uy,  22uy) -> Correct AD_record_overflow
    | (2uy,  30uy) -> Correct AD_decompression_failure
    | (2uy,  40uy) -> Correct AD_handshake_failure
    | (1uy,  41uy) -> Correct AD_no_certificate
    | (1uy,  42uy) -> Correct AD_bad_certificate_warning
    | (2uy,  42uy) -> Correct AD_bad_certificate_fatal
    | (1uy,  43uy) -> Correct AD_unsupported_certificate_warning
    | (2uy,  43uy) -> Correct AD_unsupported_certificate_fatal
    | (1uy,  44uy) -> Correct AD_certificate_revoked_warning
    | (2uy,  44uy) -> Correct AD_certificate_revoked_fatal
    | (1uy,  45uy) -> Correct AD_certificate_expired_warning
    | (2uy,  45uy) -> Correct AD_certificate_expired_fatal
    | (1uy,  46uy) -> Correct AD_certificate_unknown_warning
    | (2uy,  46uy) -> Correct AD_certificate_unknown_fatal
    | (2uy,  47uy) -> Correct AD_illegal_parameter
    | (2uy,  48uy) -> Correct AD_unknown_ca
    | (2uy,  49uy) -> Correct AD_access_denied
    | (2uy,  50uy) -> Correct AD_decode_error
    | (2uy,  51uy) -> Correct AD_decrypt_error
    | (2uy,  60uy) -> Correct AD_export_restriction
    | (2uy,  70uy) -> Correct AD_protocol_version
    | (2uy,  71uy) -> Correct AD_insufficient_security
    | (2uy,  80uy) -> Correct AD_internal_error
    | (1uy,  90uy) -> Correct AD_user_cancelled_warning
    | (2uy,  90uy) -> Correct AD_user_cancelled_fatal
    | (1uy, 100uy) -> Correct AD_no_renegotiation
    | (2uy, 110uy) -> Correct AD_unsupported_extension
    | _            -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


// ---------------- outgoing alerts -------------------

let send_alert (* ci:ConnectionInfo *) s (ad:alertDescription{isFatal ad}) =
    (* FIXED? We should only send fatal alerts. Right now we'll interpret any sent alert
       as fatal, and so will close the connection afterwards. *)
    (* Note: we only support sending one (fatal) alert in the whole protocol execution
       (because we'll tell dispatch an alert has been sent when the buffer gets empty)
       So we only add an alert on an empty buffer (we don't enqueue more alerts) *)
    if length !(State.outgoing s) = 0
    then State.outgoing s := alertBytes ad
    (* We currently ignore subsequent requests *)

// We implement locally fragmentation, not hiding any length
let makeFragment i b =
    //let ki = mk_id e in
    if length b < fragmentLength then
      let r0 = (length b, length b) in
      //let f = HSFragment.fragmentPlain ki r0 b in
      ((r0,b),empty_bytes)
    else
      let (b0,rem) = Platform.Bytes.split b fragmentLength in
      let r0 : range = (length b0, length b0) in
      //let f = HSFragment.fragmentPlain ki r0 b0 in
      ((r0,b),rem)

assume val next_fragment: i:id -> s:state -> ST nextReply
  (requires (fun _ -> True))
  (ensures (fun h0 r h1 -> 
    modifies (Set.singleton(State.region s)) h0 h1))

(* TODO
let next_fragment i s =
    let f = !(State.outgoing s) in
    if length f = 0 then EmptyALFrag
    else
        let ((r0,df),f') = makeFragment i f in
        State.outgoing s := f';
        if length f' = 0 then
            // FIXME: This hack is not even working, because if we do one-byte fragmentation parseAlert fails!
            (match parseAlert f with
            | Error z    -> unexpected ("[next_fragment] This invocation of parseAlertDescription should never fail")
            | Correct ad ->
                match ad with
                | AD_close_notify -> LastALCloseFrag r0 df
                | _               -> LastALFrag r0 df ad)
        else ALFrag r0 df
*)

// ---------------- incoming alerts -------------------

let handle_alert s ad =
    match ad with
    | AD_close_notify -> (* we possibly send a close_notify back *)
        send_alert s AD_close_notify;
        ALClose_notify
    | _ ->
        if isFatal ad then ALFatal ad else ALWarning ad

let recv_fragment (ci:ConnectionInfo) s (r:range) (b1:bytes) =
    // FIXME: we should accept further alert data after a warning! (parsing sequences of messages in Handshake style)
    // but this requires changing the response protocol to dispatch
    let ki = mk_id ci.id_in in
    let b0 = !(State.incoming s) in
    //let b1 = HSFragment.fragmentRepr ki r f in
    match length b0, length b1 with
    | 0, 2 | 1, 1 -> (* process this alert *)
        if length b0 = 1 then State.incoming s := empty_bytes;
        (match parseAlert (b0 @| b1) with
        | Error z    -> Error z
        | Correct ad -> correct (handle_alert s ad) )

    | 0, 1 -> State.incoming s := b1; Correct ALAck (* Buffer this partial alert *)
    | _, 0 -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Empty alert fragments are invalid")
    | _, _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "No more data expected after an alert")

let is_incoming_empty (c:ConnectionInfo) s = length !s.incoming  = 0

let reset_incoming s = s.incoming := empty_bytes
let reset_outgoing s = s.outgoing := empty_bytes

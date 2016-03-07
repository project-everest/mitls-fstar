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

val parse: b:lbytes 2 -> Tot 
  (r: result alertDescription { forall ad. (r = Correct ad ==> b = alertBytes ad) })
let parse b =
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


(*** alert protocol ***)

// TLS 1.2 and earlier miTLS supported alert fragmentation;
// TLS 1.3 and miTLS* forbid it (a slight deviation from TLS 1.2): 
// each alert fragment carries exactly a 2-byte alert.

// outgoing buffer: either empty or a complete alert

type fragment = f:lbytes 2 { exists ad. f = alertBytes ad }

type buffer = option fragment

//* moving to stateful private state
private type state = | State:
  #region: rid ->
  outgoing: rref region buffer -> (* empty if nothing to be sent *)
  state

let init r0 =
  let r = new_region r0 in
  State (ralloc r None)

// ---------------- outgoing alerts -------------------

let send (State b) (ad:alertDescription{isFatal ad}) =
    if !b = None 
    then b := Some (alertBytes ad)
 
    (* alert generation is underspecified, so we just ignore subsequent requests *)
    (* FIXED? We should only send fatal alerts. Right now we'll interpret any sent alert
       as fatal, and so will close the connection afterwards. *)
    (* Note: we only support sending one (fatal) alert in the whole protocol execution
       (because we'll tell dispatch an alert has been sent when the buffer gets empty)
       So we only add an alert on an empty buffer (we don't enqueue more alerts) *)

val next_fragment: s:state -> ST (option alertDescription)
  (requires (fun _ -> True))
  (ensures (fun h0 r h1 -> modifies (Set.singleton(State.region s)) h0 h1))

let next_fragment (State b) =  
  match !b with 
  | None -> None 
  | Some f -> b:= None; 
             (match parse f with | Correct ad -> Some ad | Error _ -> None)

// ---------------- incoming alerts -------------------

let recv_fragment s (r:range) (f:bytes) : result (ad: alertDescription { f = alertBytes ad }) =
    if length f = 2 then 
    match parse f with 
    | Correct ad -> 
        if ad = AD_close_notify then send s ad; (* we possibly send a close_notify back *)
        Correct ad
    | Error z -> Error z
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "expected exactly 2 bytes of alert")

let reset s = s.outgoing := None   // we silently discard any unsent alert. 

module Alert

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq

open Platform.Error
open FStar.Bytes

open TLSError
open TLSConstants
open TLSInfo
open Range

//16-05-29 not much protocol left; consider merging with TLSError

(* Conversions *)

let alertBytes ad =
  (* Severity (warning or fatal) is hardcoded, as specified in sec. 7.2.2 *)
  match ad with
    | AD_close_notify ->                       abyte2 (1z,   0z)
    | AD_unexpected_message ->                 abyte2 (2z,  10z)
    | AD_bad_record_mac ->                     abyte2 (2z,  20z)
    | AD_decryption_failed ->                  abyte2 (2z,  21z)
    | AD_record_overflow ->                    abyte2 (2z,  22z)
    | AD_decompression_failure ->              abyte2 (2z,  30z)
    | AD_handshake_failure ->                  abyte2 (2z,  40z)
    | AD_no_certificate ->                     abyte2 (1z,  41z)
    | AD_bad_certificate_warning ->            abyte2 (1z,  42z)
    | AD_bad_certificate_fatal ->              abyte2 (2z,  42z)
    | AD_unsupported_certificate_warning ->    abyte2 (1z,  43z)
    | AD_unsupported_certificate_fatal ->      abyte2 (2z,  43z)
    | AD_certificate_revoked_warning ->        abyte2 (1z,  44z)
    | AD_certificate_revoked_fatal ->          abyte2 (2z,  44z)
    | AD_certificate_expired_warning ->        abyte2 (1z,  45z)
    | AD_certificate_expired_fatal ->          abyte2 (2z,  45z)
    | AD_certificate_unknown_warning ->        abyte2 (1z,  46z)
    | AD_certificate_unknown_fatal ->          abyte2 (2z,  46z)
    | AD_illegal_parameter ->                  abyte2 (2z,  47z)
    | AD_unknown_ca ->                         abyte2 (2z,  48z)
    | AD_access_denied ->                      abyte2 (2z,  49z)
    | AD_decode_error ->                       abyte2 (2z,  50z)
    | AD_decrypt_error ->                      abyte2 (2z,  51z)
    | AD_export_restriction ->                 abyte2 (2z,  60z)
    | AD_protocol_version ->                   abyte2 (2z,  70z)
    | AD_insufficient_security ->              abyte2 (2z,  71z)
    | AD_internal_error ->                     abyte2 (2z,  80z)
    | AD_user_cancelled_warning ->             abyte2 (1z,  90z)
    | AD_user_cancelled_fatal ->               abyte2 (2z,  90z)
    | AD_no_renegotiation ->                   abyte2 (1z, 100z)
    | AD_unrecognized_name ->                  abyte2 (2z, 112z)
    | AD_missing_extension ->                  abyte2 (2z, 109z)
    | AD_unsupported_extension ->              abyte2 (2z, 110z)
    | AD_no_application_protocol ->            abyte2 (2z, 120z)

#set-options "--z3rlimit 64"

val parse: b:lbytes 2 -> Tot
  (r: result alertDescription { forall ad. (r = Correct ad ==> b == alertBytes ad) })
let parse b =
    let b1,b2 = cbyte2 b in
    Seq.lemma_eq_intro b (abyte2 (b1,b2));
    match cbyte2 b with
    | (1z,   0z) -> Correct AD_close_notify
    | (2z,  10z) -> Correct AD_unexpected_message
    | (2z,  20z) -> Correct AD_bad_record_mac
    | (2z,  21z) -> Correct AD_decryption_failed
    | (2z,  22z) -> Correct AD_record_overflow
    | (2z,  30z) -> Correct AD_decompression_failure
    | (2z,  40z) -> Correct AD_handshake_failure
    | (1z,  41z) -> Correct AD_no_certificate
    | (1z,  42z) -> Correct AD_bad_certificate_warning
    | (2z,  42z) -> Correct AD_bad_certificate_fatal
    | (1z,  43z) -> Correct AD_unsupported_certificate_warning
    | (2z,  43z) -> Correct AD_unsupported_certificate_fatal
    | (1z,  44z) -> Correct AD_certificate_revoked_warning
    | (2z,  44z) -> Correct AD_certificate_revoked_fatal
    | (1z,  45z) -> Correct AD_certificate_expired_warning
    | (2z,  45z) -> Correct AD_certificate_expired_fatal
    | (1z,  46z) -> Correct AD_certificate_unknown_warning
    | (2z,  46z) -> Correct AD_certificate_unknown_fatal
    | (2z,  47z) -> Correct AD_illegal_parameter
    | (2z,  48z) -> Correct AD_unknown_ca
    | (2z,  49z) -> Correct AD_access_denied
    | (2z,  50z) -> Correct AD_decode_error
    | (2z,  51z) -> Correct AD_decrypt_error
    | (2z,  60z) -> Correct AD_export_restriction
    | (2z,  70z) -> Correct AD_protocol_version
    | (2z,  71z) -> Correct AD_insufficient_security
    | (2z,  80z) -> Correct AD_internal_error
    | (1z,  90z) -> Correct AD_user_cancelled_warning
    | (2z,  90z) -> Correct AD_user_cancelled_fatal
    | (1z, 100z) -> Correct AD_no_renegotiation
    | (2z, 109z) -> Correct AD_missing_extension
    | (2z, 110z) -> Correct AD_unsupported_extension
    | _            -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


(* 16-05-29 now integrated with the record layer, for simplicity

(*** alert protocol ***)

// TLS 1.2 and earlier miTLS supported alert fragmentation;
// TLS 1.3 and miTLS* forbid it (a slight deviation from TLS 1.2):
// each alert fragment carries exactly a 2-byte alert.

// outgoing buffer: either empty or a complete alert

type fragment = f:lbytes 2 { exists ad. f = alertBytes ad }

type buffer = option fragment

//* moving to stateful private state; NS: should it be abstract?
private type state = | State:
  #region: rid ->
  outgoing: rref region buffer -> (* empty if nothing to be sent *)
  state

let region s = s.region

val init: r0:rid -> ST state
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    extends (State?.region s) r0 /\
    fresh_region (State?.region s) h0 h1))

let init r0 =
  let r = new_region r0 in
  State (ralloc r None)

// ---------------- outgoing alerts -------------------
val send : s:state -> ad:alertDescription{isFatal ad} -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_one (region s) h0 h1))
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
  (ensures (fun h0 r h1 -> modifies_one (State?.region s) h0 h1))

let next_fragment (State b) =
  match !b with
  | None -> None
  | Some f -> b:= None;
             (match parse f with | Correct ad -> Some ad | Error _ -> None)

// ---------------- incoming alerts -------------------

// no more recv_fragment as alerts are now parsed by Content.

let reset s = s.outgoing := None   // we silently discard any unsent alert.

*)

module TLSError

(* TLS explicitly returns run-time errors: 
   results carry either values or error descriptions *)

type alertDescription =
    | AD_close_notify
    | AD_unexpected_message
    | AD_bad_record_mac
    | AD_decryption_failed
    | AD_record_overflow
    | AD_decompression_failure
    | AD_handshake_failure
    | AD_no_certificate
    | AD_bad_certificate_warning
    | AD_bad_certificate_fatal
    | AD_unsupported_certificate_warning
    | AD_unsupported_certificate_fatal
    | AD_certificate_revoked_warning
    | AD_certificate_revoked_fatal
    | AD_certificate_expired_warning
    | AD_certificate_expired_fatal
    | AD_certificate_unknown_warning
    | AD_certificate_unknown_fatal
    | AD_illegal_parameter
    | AD_unknown_ca
    | AD_access_denied
    | AD_decode_error
    | AD_decrypt_error
    | AD_export_restriction
    | AD_protocol_version
    | AD_insufficient_security
    | AD_internal_error
    | AD_user_cancelled_warning
    | AD_user_cancelled_fatal
    | AD_no_renegotiation
    | AD_unrecognized_name
    | AD_unsupported_extension

let isFatal ad =
    match ad with
    | AD_unexpected_message
    | AD_bad_record_mac
    | AD_decryption_failed
    | AD_record_overflow
    | AD_decompression_failure
    | AD_handshake_failure
    | AD_bad_certificate_fatal
    | AD_unsupported_certificate_fatal
    | AD_certificate_revoked_fatal
    | AD_certificate_expired_fatal
    | AD_certificate_unknown_fatal
    | AD_illegal_parameter
    | AD_unknown_ca
    | AD_access_denied
    | AD_decode_error
    | AD_decrypt_error
    | AD_export_restriction
    | AD_protocol_version
    | AD_insufficient_security
    | AD_internal_error
    | AD_user_cancelled_fatal
    | AD_unsupported_extension -> true
    | _ -> false

type error = alertDescription * string

type Result 'a = Platform.Error.optResult error 'a

open Platform.Error

val resT: r:Result 'a { Platform.Error.is_Correct r } -> Tot 'a
let resT (Platform.Error.Correct v) = v

val mapResult: ('a -> Tot 'b) -> Result 'a -> Tot (Result 'b)
let mapResult f r = 
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val bindResult: ('a -> Tot (Result 'b)) -> Result 'a -> Tot (Result 'b)
let bindResult f r = 
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

val resultMap: Result 'a -> ('a -> Tot 'b) -> Tot (Result 'b)
let resultMap r f = 
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val resultBind: Result 'a -> ('a -> Tot (Result 'b)) -> Tot (Result 'b)
let resultBind r f = 
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

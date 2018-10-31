module TLSError
open FStar.String
(* TLS explicitly returns run-time errors:
   results carry either values or error descriptions *)

include Parsers.AlertDescription
include Parsers.AlertLevel
include Parsers.Alert

let string_of_alertDescription (a:alertDescription) = "alertDescription"
let string_of_alertLevel (a:alertLevel) = "alertLevel"
let string_of_alert (a:alert) = 
  "level="^string_of_alertLevel a.level^
  "description="^string_of_alertDescription a.description

let fatalAlert ad = {level=Fatal; description=ad}

(* TODO functions checking consistency of levels and descriptions *)

// let isFatal ad =
//     match ad with
//     | AD_unexpected_message
//     | AD_bad_record_mac
//     | AD_decryption_failed
//     | AD_record_overflow
//     | AD_decompression_failure
//     | AD_handshake_failure
//     | AD_bad_certificate_fatal
//     | AD_unsupported_certificate_fatal
//     | AD_certificate_revoked_fatal
//     | AD_certificate_expired_fatal
//     | AD_certificate_unknown_fatal
//     | AD_illegal_parameter
//     | AD_unknown_ca
//     | AD_access_denied
//     | AD_decode_error
//     | AD_decrypt_error
//     | AD_export_restriction
//     | AD_protocol_version
//     | AD_insufficient_security
//     | AD_internal_error
//     | AD_user_cancelled_fatal
//     | AD_missing_extension
//     | AD_unsupported_extension
//     | AD_no_application_protocol -> true
//     | _ -> false

type error = alert * string
let string_of_error (a,s)= string_of_alertDescription a.description^" ("^s^")"

type result 'a = FStar.Error.optResult error 'a

open FStar.Error
let string_of_result f = function
  | Error z -> "Error: "^string_of_error z
  | Correct v -> f v

let fatal #t a s: result t = Error(fatalAlert a, s)

val resT: r:result 'a { FStar.Error.Correct? r } -> Tot 'a
let resT (FStar.Error.Correct v) = v

inline_for_extraction
val mapResult: ('a -> Tot 'b) -> result 'a -> Tot (result 'b)
inline_for_extraction
let mapResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val bindResult: ('a -> Tot (result 'b)) -> result 'a -> Tot (result 'b)
let bindResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

val resultMap: result 'a -> ('a -> Tot 'b) -> Tot (result 'b)
let resultMap r f =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

val resultBind: result 'a -> ('a -> Tot (result 'b)) -> Tot (result 'b)
let resultBind r f =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

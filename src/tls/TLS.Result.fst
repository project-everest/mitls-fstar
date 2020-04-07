module TLS.Result 

let string_of_alert (a:alert) = 
  "level="^Parsers.AlertLevel.string_of_alertLevel a.Parsers.Alert.level^
  ", description="^string_of_alertDescription a.Parsers.Alert.description

let fatalAlert ad = Parsers.Alert.({level=Parsers.AlertLevel.Fatal; description=ad})

// (* TODO functions checking consistency of levels and descriptions *)
//
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
//     | AD_decrypt_errorS.
//     | AD_export_restriction
//     | AD_protocol_version
//     | AD_insufficient_security
//     | AD_internal_error
//     | AD_user_cancelled_fatal
//     | AD_missing_extension
//     | AD_unsupported_extension
//     | AD_no_application_protocol -> true
//     | _ -> false

let string_of_error e = 
  FStar.Printf.sprintf "%s: %s" (string_of_alertDescription e.alert) e.cause

let string_of_result #a f = function
  | Error z -> "Error: "^string_of_error z
  | Correct v -> f v

let resT (Correct v) = v

inline_for_extraction
let mapResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

let bindResult f r =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

let resultMap r f =
   (match r with
    | Error z -> Error z
    | Correct c -> Correct (f c))

let resultBind r f =
   (match r with
    | Error z -> Error z
    | Correct c -> f c)

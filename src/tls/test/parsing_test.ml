(* Tests for parsing functions in miTLS *)
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open TLSError
open TLSConstants

(* State variables *)
let pv = ref TLS_1p2
let kex = ref Kex_DHE
       
(* Traces list *)
let traces = [
    "google-trace.bin";
    "akamai-trace.bin";
    "tls-unique-trace-1.bin";
    "client-auth-trace-1.bin";
    "client-auth-trace-2.bin";
    "tls-unique-trace-1.bin";
  ]

let print_error error =
  let error_type = match fst error with
  | AD_close_notify -> "Close notify error:"
  | AD_unexpected_message -> "Unexpected message error :"
  | AD_bad_record_mac -> "Bad record mac error:"
  | AD_decryption_failed -> "Decryption failed error:"
  | AD_record_overflow -> "Record overflow error:"
  | AD_decompression_failure -> "Decompression failure error:"
  | AD_handshake_failure -> "Handshake failure error:"
  | AD_no_certificate -> "No certificate error:"
  | AD_bad_certificate_warning -> "Bad certificate warning:"
  | AD_bad_certificate_fatal -> "Bad certificate error:"
  | AD_unsupported_certificate_warning -> "Unsupported certificate error:"
  | AD_unsupported_certificate_fatal -> "Unsupported certificate error:"
  | AD_certificate_revoked_fatal -> "Certificate revoked error:"
  | AD_certificate_expired_fatal -> "Certificate expired error:"
  | AD_certificate_unknown_fatal -> "Certificate unknown error:"
  | AD_certificate_revoked_warning -> "Certificate revoked error:"
  | AD_certificate_expired_warning -> "Certificate expired error:"
  | AD_certificate_unknown_warning -> "Certificate unknown error:"
  | AD_illegal_parameter -> "Illegal parameter error:"
  | AD_unknown_ca -> "Unknown CA error:"
  | AD_access_denied -> "Access denied error:"
  | AD_decode_error -> "Decoding error:"
  | AD_decrypt_error -> "Decrypting error:"
  | AD_export_restriction -> "Exporting restriction error:"
  | AD_protocol_version -> "Protocol version error:"
  | AD_insufficient_security -> "Insufficient security error:"
  | AD_internal_error -> "Internal error:"
  | AD_user_cancelled_fatal -> "User canceled error:"
  | AD_unsupported_extension -> "Unsupported extension error:"
  | AD_user_cancelled_warning -> "User canceled error:"
  | AD_no_renegotiation -> "No renegotiation error:"
  | AD_unrecognized_name -> "Unrecognized name error:" in
  (error_type ^ "\n" ^ snd error)
	       
let parse_handshake_message bytes =
  if length bytes >= 4 then
    let ht, len, msg = split2 bytes 1 3 in
    let len = int_of_bytes len in
    if length msg <> len then print_string "Error: message length did not match bytes length\n"
    else
      match cbyte ht with
      | '\x00' -> ()
      | '\x01' ->
	 print_string "Parsing client hello...\n";
	 (match parseClientHello msg with
	 | Correct(ch) -> print_string "ClientHello OK\n"
	 | Error(z) ->
	    print_string "Failed to parse client hello:\n";
	    print_string (print_error z ^ "\n"))
      | '\x02' -> 
	 print_string "Parsing server hello message...\n";
	 (match parseServerHello msg with
	 | Correct(ch) -> print_string "ServerHello OK\n"
	 | Error(z) -> print_string "Failed to parse server hello :\n";
	               print_string (snd z))
      | '\x04' -> 
	 print_string "Parsing session ticket message...\n";
	 (match parseSessionTicket msg with
	 | Correct(ch) -> print_string "SessionTicket OK\n"
	 | Error(z) ->
	    print_string "Failed to parse session ticket:\n";
	    print_string (snd z))
      | '\x06' -> 
	 print_string "Parsing hello retry request message...\n";
	 (match parseHelloRetryRequest msg with
	 | Correct(ch) -> print_string "HelloRetryRequest OK\n"
	 | Error(z) -> print_string "Failed to parse hello retry request\n")
      | '\x08' -> 
	 print_string "Parsing encrypted extensions message...\n";
	 (match parseEncryptedExtensions msg with
	 | Correct(ch) -> print_string "EncryptedExtensions OK\n"
	 | Error(z) -> print_string "Failed to parse encrypted extensions\n")
      | '\x0b' -> 
	 print_string "Parsing certificate message...\n";
	 (match parseCertificate msg with
	 | Correct(ch) -> print_string "Certificate OK\n"
	 | Error(z) -> print_string "Failed to parse certificate\n")
      | '\x0c' -> 
	 print_string "Parsing server key exchange message...\n";
	 (match parseServerKeyExchange !kex msg with 
	 | Correct(ch) -> print_string "ServerKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse server key exchange\n")
      | '\x0d' -> 
	 print_string "Parsing certificate request message...\n";
	 (match parseCertificateRequest !pv msg with
	 | Correct(ch) -> print_string "CertificateRequest OK\n"
	 | Error(z) -> print_string "Failed to parse certificate request\n")
      | '\x0e' ->
	 print_string "Parsing server hello done message...\n";
	 if length msg = 0 then print_string "ServerHelloDone OK\n"
	 else print_string "Failed to parse server hello done\n"
      | '\x0f' -> 
	 print_string "Parsing certificate verify message...\n";
	 (match parseCertificateVerify msg with
	 | Correct(ch) -> print_string "CertificateVerify OK\n"
	 | Error(z) -> print_string "Failed to parse certificate verify\n")
      | '\x10' -> 
	 print_string "Parsing client key exchange message...\n";
	 (match parseClientKeyExchange !pv !kex msg with
	 | Correct(ch) -> print_string "ClientKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse client key exchange\n")
      | '\x11' -> 
	 print_string "Parsing server configuration message...\n";
	 (match parseServerConfiguration msg with
	 | Correct(ch) -> print_string "ServerConfiguration OK\n"
	 | Error(z) -> print_string "Failed to parse server configuration\n")
      | '\x14' -> 
	 print_string "Parsing finished message...\n";
	 (match parseFinished msg with
	 | Correct(ch) -> print_string "FinishedMessage OK\n"
	 | Error(z) -> print_string "Failed to parse finished message\n")
      | '\x18' -> print_string "Error: ignored key update message\n"
      | _ -> print_string "Error: parsed an unknown handshake type\n"
  else print_string "Error: HS message too small to retrieve handshake type + length from it\n"

let rec parse_handshake bytes =
  if length bytes >= 4 then
    let ht, len, data = split2 bytes 1 3 in
    let len = int_of_bytes len in
    let (msg, bytes) = split bytes (4+len) in
    parse_handshake_message msg;
    parse_handshake bytes
  else if length bytes = 0 then print_string "Parsed all messages\n"
  else print_string "Error: parsing failed due to length not being appropriate"
		    
let parse_alert_message bytes =
  ()

let parse_application_data_message bytes =
  ()

let parse_ccs_message bytes =
  ()
    
let rec parse_message bytes =
  if length bytes >= 2 then
    let (pv, ct, bytes) = split2 bytes 2 1 in
    match vlsplit 2 bytes with
    | Correct (msg, bytes) ->
       let (len, msg) = split msg 2 in
       (match cbyte ct with
	| '\x14' -> parse_ccs_message msg
	| '\x15' -> parse_alert_message msg
	| '\x16' -> parse_handshake_message msg
	| '\x17' -> parse_application_data_message msg
        | _ -> print_string "Error: wrong content type\n" );
       parse_message bytes
    | Error(z) -> print_string "Error : Failed to parse bytes length of message \n"
  else if length bytes = 0 then ()
  else print_string "Error : Found some standalone bytes"

let parse_trace_file file =
  let bytes = Bytes.create 1000000 in
  let flag = input file bytes 0 65536 in
  if flag = 0 then print_string "Reached EOF\n"
  else print_string ("Read " ^ (string_of_int flag) ^ " characters\n");
  let bytes = Bytes.sub bytes 0 flag in
  let bytes = { bl = [bytes]; max = Bytes.length bytes; index = 0; length = Bytes.length bytes; } in
  parse_handshake bytes;  
  print_string "\n********************************************\n"
		    
let _ =
  let handshakes = List.map (fun x -> open_in_bin ("./traces/" ^ x)) traces in 
  List.iter parse_trace_file handshakes
  

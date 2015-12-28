(* Tests for parsing functions in miTLS *)
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open TLSError
open TLSConstants

(* State variables *)
let pv = ref TLS_1p2
let kex = ref Kex_ECDHE
       
(* Traces list *)
let ecdhe_traces = [
    "openssl-google.bin";
    "openssl-akamai.bin";
    "tls-unique-trace-4.bin";
  ]

let dhe_traces = [
    "tls-unique-trace-3.bin";
    "client-auth-trace-1.bin";
    "client-auth-trace-2.bin";
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
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) ->
	    print_string "...FAILED:\n";
	    print_string (print_error z ^ "\n"))
      | '\x02' -> 
	 print_string "Parsing server hello message...\n";
	 (match parseServerHello msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED:\n";
	               print_string (snd z))
      | '\x04' -> 
	 print_string "Parsing session ticket message...\n";
	 (match parseSessionTicket msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) ->
	    print_string "...FAILED:\n";
	    print_string (snd z))
      | '\x06' -> 
	 print_string "Parsing hello retry request message...\n";
	 (match parseHelloRetryRequest msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x08' -> 
	 print_string "Parsing encrypted extensions message...\n";
	 (match parseEncryptedExtensions msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x0b' -> 
	 print_string "Parsing certificate message...\n";
	 (match parseCertificate msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x0c' -> 
	 print_string "Parsing server key exchange message...\n";
	 (match parseServerKeyExchange !kex msg with 
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x0d' -> 
	 print_string "Parsing certificate request message...\n";
	 (match parseCertificateRequest !pv msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x0e' ->
	 print_string "Parsing server hello done message...\n";
	 if length msg = 0 then print_string "...OK\n"
	 else print_string "...FAILED\n"
      | '\x0f' -> 
	 print_string "Parsing certificate verify message...\n";
	 (match parseCertificateVerify msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x10' -> 
	 print_string "Parsing client key exchange message...\n";
	 (match parseClientKeyExchange !pv !kex msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x11' -> 
	 print_string "Parsing server configuration message...\n";
	 (match parseServerConfiguration msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x14' -> 
	 print_string "Parsing finished message...\n";
	 (match parseFinished msg with
	 | Correct(ch) -> print_string "...OK\n"
	 | Error(z) -> print_string "...FAILED\n")
      | '\x18' -> print_string "Error: ignored key update message\n"
      | '\x43' ->
	 print_string "Parsing next protocol message...\n";
         (match parseNextProtocol msg with
	  | Correct(_) -> print_string "...OK\n"
	  | Error(_) -> print_string "...FAILED\n")
      | _ -> print_string ("Error: parsed an unknown handshake type: " ^ (Platform.Bytes.print_bytes bytes) ^ "\n")
  else print_string "Error: HS message too small to retrieve handshake type + length from it\n"

let rec parse_handshake bytes =
  if length bytes >= 4 then
    let ht, len, data = split2 bytes 1 3 in
    let len = int_of_bytes len in
    let (msg, bytes) = split bytes (4+len) in
    parse_handshake_message msg;
    parse_handshake bytes
  else if length bytes = 0 then print_string "Parsed all messages\n"
  else print_string ("Error: parsing failed due to length not being appropriate:\n"
		       ^ (Platform.Bytes.print_bytes bytes))
		    
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
  let fbytes = Bytes.create 1000000 in
  let flag = input file fbytes 0 65536 in
  if flag = 0 then print_string "Reached EOF\n"
  else print_string ("Read " ^ (string_of_int flag) ^ " characters\n");
  let bytes = Bytes.sub fbytes 0 flag in
  let hs = { bl = [bytes]; max = flag; index = 0; length = flag; } in
  parse_handshake hs;  
  print_string "\n********************************************\n"
		    
let _ =
  let ecdhe_handshakes = List.map (fun x -> open_in_bin ("./traces/" ^ x)) ecdhe_traces in
  let dhe_handshakes = List.map (fun x -> open_in_bin ("./traces/" ^ x)) dhe_traces in
  kex := Kex_ECDHE;
  List.iter parse_trace_file ecdhe_handshakes;
  kex := Kex_DHE;
  List.iter parse_trace_file dhe_handshakes
  
  

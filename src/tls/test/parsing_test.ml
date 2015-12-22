(* Tests for parsing functions in miTLS *)
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open TLSConstants

(* State variables *)
let pv = ref TLS_1p2
let kex = ref Kex_DHE
       
(* Traces list *)
let traces = [
    "tls-unique-trace-2.bin";
    "client-auth-trace-1.bin";
    "client-auth-trace-2.bin";
    "openssl-google.hex";
    "tls-unique-trace-1.bin";
  ]
    
let parse_handshake_message bytes =
  if length bytes >= 4 then
    let ht, len, msg = split2 bytes 1 3 in
    let len = int_of_bytes len in
    if length msg <> len then print_string "Error: message length did not match bytes length\n"
    else
      match cbyte ht with
      | '\x00' -> ()
      | '\x01' ->
	 (match parseClientHello msg with
	 | Correct(ch) -> print_string "ClientHello OK\n"
	 | Error(z) -> print_string "Failed to parse client hello\n")
      | '\x02' -> 
	 (match parseServerHello msg with
	 | Correct(ch) -> print_string "ServerHello OK\n"
	 | Error(z) -> print_string "Failed to parse server hello :\n";
	               print_string (snd z))
      | '\x04' -> 
	 (match parseSessionTicket msg with
	 | Correct(ch) -> print_string "SessionTicket OK\n"
	 | Error(z) -> print_string "Failed to parse session ticket\n")
      | '\x06' -> 
	 (match parseHelloRetryRequest msg with
	 | Correct(ch) -> print_string "HelloRetryRequest OK\n"
	 | Error(z) -> print_string "Failed to parse hello retry request\n")
      | '\x08' -> 
	 (match parseEncryptedExtensions msg with
	 | Correct(ch) -> print_string "EncryptedExtensions OK\n"
	 | Error(z) -> print_string "Failed to parse encrypted extensions\n")
      | '\x0b' -> 
	 (match parseCertificate msg with
	 | Correct(ch) -> print_string "Certificate OK\n"
	 | Error(z) -> print_string "Failed to parse certificate\n")
      | '\x0c' -> 
	 (match parseServerKeyExchange !kex msg with 
	 | Correct(ch) -> print_string "ServerKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse server key exchange\n")
      | '\x0d' -> 
	 (match parseCertificateRequest !pv msg with
	 | Correct(ch) -> print_string "CertificateRequest OK\n"
	 | Error(z) -> print_string "Failed to parse certificate request\n")
      | '\x0e' ->
	 if length msg = 0 then print_string "ServerHelloDone OK\n"
	 else print_string "Failed to parse server hello done\n"
      | '\x0f' -> 
	 (match parseCertificateVerify msg with
	 | Correct(ch) -> print_string "CertificateVerify OK\n"
	 | Error(z) -> print_string "Failed to parse certificate verify\n")
      | '\x10' -> 
	 (match parseClientKeyExchange !pv !kex msg with
	 | Correct(ch) -> print_string "ClientKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse client key exchange\n")
      | '\x11' -> 
	 (match parseServerConfiguration msg with
	 | Correct(ch) -> print_string "ServerConfiguration OK\n"
	 | Error(z) -> print_string "Failed to parse server configuration\n")
      | '\x14' -> 
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
  let bytes = Bytes.create 65536 in
  let flag = input file bytes 0 65536 in
  if flag = 0 then print_string "Reached EOF\n"
  else print_string ("Read " ^ (string_of_int flag) ^ " characters\n");
  let bytes = { bl = [bytes]; max = Bytes.length bytes; index = 0; length = Bytes.length bytes; } in
  parse_handshake bytes;
  print_string "\n"
		    
let _ =
  let handshakes = List.map (fun x -> open_in ("./traces/" ^ x)) traces in 
  List.iter parse_trace_file handshakes
  

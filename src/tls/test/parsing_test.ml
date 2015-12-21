(* Tests for parsing functions in miTLS *)
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open TLSConstants

(* State variables *)
let pv = ref TLS_1p2
let kex = ref Kex_DHE
       
let log_bytes =
  { bl = ["abcde"];
    max = 65536;
    index = 0;
    length = 5; }

let rec parse_handshake_message bytes =
  if length bytes >= 4 then
    let ht, len, msg = split2 bytes 1 3 in
    if length msg <> len then print_string "Error: message length did not match bytes length\n"
    else
      match ht with
      | 0 -> ()
      | 1 ->
	 (match parseClientHello msg with
	 | Correct(ch) -> print_string "ClientHello OK\n"
	 | Error(z) -> print_string "Failed to parse client hello\n")
      | 2 -> 
	 (match parseServerHello msg with
	 | Correct(ch) -> print_string "ServerHello OK\n"
	 | Error(z) -> print_string "Failed to parse server hello\n")
      | 4 -> 
	 (match parseSessionTicket msg with
	 | Correct(ch) -> print_string "SessionTicket OK\n"
	 | Error(z) -> print_string "Failed to parse session ticket\n")
      | 6 -> 
	 (match parseHelloRetryRequest msg with
	 | Correct(ch) -> print_string "HelloRetryRequest OK\n"
	 | Error(z) -> print_string "Failed to parse hello retry request\n")
      | 8 -> 
	 (match parseEncryptedExtensions msg with
	 | Correct(ch) -> print_string "EncryptedExtensions OK\n"
	 | Error(z) -> print_string "Failed to parse encrypted extensions\n")
      | 11 -> 
	 (match parseCertificate msg with
	 | Correct(ch) -> print_string "Certificate OK\n"
	 | Error(z) -> print_string "Failed to parse certificate\n")
      | 12 -> 
	 (match parseServerKeyExchange !kex msg with 
	 | Correct(ch) -> print_string "ServerKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse server key exchange\n")
      | 13 -> 
	 (match parseCertificateRequest !pv msg with
	 | Correct(ch) -> print_string "CertificateRequest OK\n"
	 | Error(z) -> print_string "Failed to parse certificate request\n")
      | 14 ->
	 if length msg = 0 then print_string "ServerHelloDone OK\n"
	 else print_string "Failed to parse server hello done\n"
      | 15 -> 
	 (match parseCertificateVerify msg with
	 | Correct(ch) -> print_string "CertificateVerify OK\n"
	 | Error(z) -> print_string "Failed to parse certificate verify\n")
      | 16 -> 
	 (match parseClientKeyExchange !pv !kex msg with
	 | Correct(ch) -> print_string "ClientKeyExchange OK\n"
	 | Error(z) -> print_string "Failed to parse client key exchange\n")
      | 17 -> 
	 (match parseServerConfiguration msg with
	 | Correct(ch) -> print_string "ServerConfiguration OK\n"
	 | Error(z) -> print_string "Failed to parse server configuration\n")
      | 20 -> 
	 (match parseFinished msg with
	 | Correct(ch) -> print_string "FinishedMessage OK\n"
	 | Error(z) -> print_string "Failed to parse finished message\n")
      | 24 -> print_string "Error: ignored key update message"
      | _ -> print_string "Error: parsed an unknown handshake type"
  else print_string "Error: HS message too small to retrieve handshake type + length from it\n"

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
       (match ct with
	| 20 -> parse_ccs_message msg
	| 21 -> parse_alert_message msg
	| 22 -> parse_handshake_message msg
	| 23 -> parse_application_data_message msg
        | _ -> print_string "Error: wrong content type\n" );
       parse_message bytes
    | Error(z) -> print_string "Failed to parse bytes length \n"
  else if length bytes = 0 then ()
  else print_string "Error : Found some standalone bytes"

let _ =
  parse_message log_bytes
  

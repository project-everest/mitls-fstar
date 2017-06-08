(* Main driver for interop tests *)
open TLSConstants
open TLSInfo

let args = ref []
let role = ref Client
let ffi  = ref false
let reconnect = ref false
let config = ref {defaultConfig with
  minVer = TLS_1p2;
  maxVer = TLS_1p3;
  check_peer_certificate = false;
  cert_chain_file = "../../data/test_chain.pem";
  private_key_file = "../../data/server.key";
  ca_file = "../../data/CAFile.pem";
  safe_resumption = true;
  ciphersuites = cipherSuites_of_nameList
    [ TLS_AES_128_GCM_SHA256;
      TLS_AES_256_GCM_SHA384;
      TLS_CHACHA20_POLY1305_SHA256;
      TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256;
      TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256;
      TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    ];
}

let s2pv = function
  | "1.2" -> TLS_1p2
  | "1.3" -> TLS_1p3
  | "1.1" -> TLS_1p1
  | "1.0" -> TLS_1p0
  | s -> failwith ("Invalid protocol version specified: "^s)

let css = [
  ("TLS_AES_128_GCM_SHA256", TLS_AES_128_GCM_SHA256);
  ("TLS_AES_256_GCM_SHA384", TLS_AES_256_GCM_SHA384);
  ("TLS_CHACHA20_POLY1305_SHA256", TLS_CHACHA20_POLY1305_SHA256);
  ("TLS_AES_128_CCM_SHA256", TLS_AES_128_CCM_SHA256);
  ("TLS_AES_128_CCM_8_SHA256", TLS_AES_128_CCM_8_SHA256);
  ("ECDHE-RSA-AES256-GCM-SHA384", TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384);
  ("ECDHE-RSA-AES128-GCM-SHA256", TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256);
  ("ECDHE-RSA-CHACHA20-POLY1305-SHA256", TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256);
  ("ECDHE-ECDSA-AES256-GCM-SHA384", TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384);
  ("ECDHE-ECDSA-AES128-GCM-SHA256", TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256);
  ("ECDHE-ECDSA-CHACHA20-POLY1305-SHA256", TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256);
  ("DHE-RSA-AES256-GCM-SHA384", TLS_DHE_RSA_WITH_AES_256_GCM_SHA384);
  ("DHE-RSA-AES128-GCM-SHA256", TLS_DHE_RSA_WITH_AES_128_GCM_SHA256);
  ("DHE-RSA-CHACHA20-POLY1305-SHA256", TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256);
  ("ECDHE-RSA-AES256-SHA", TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA);
  ("DHE-RSA-AES256-SHA", TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA);
  ("ECDHE-RSA-AES128-SHA", TLS_DHE_RSA_WITH_AES_256_CBC_SHA);
  ("DHE-RSA-AES128-SHA", TLS_DHE_RSA_WITH_AES_128_CBC_SHA);
]

let sas = [
  ("RSA+SHA512",   RSA_PKCS1_SHA512);
  ("RSA+SHA384",   RSA_PKCS1_SHA384);
  ("RSA+SHA256",   RSA_PKCS1_SHA256);
  ("RSA+SHA1",     RSA_PKCS1_SHA1);
  ("ECDSA+SHA512", ECDSA_SECP521R1_SHA512);
  ("ECDSA+SHA384", ECDSA_SECP384R1_SHA384);
  ("ECDSA+SHA256", ECDSA_SECP256R1_SHA256);
  ("ECDSA+SHA1",   ECDSA_SHA1);
]

let ngs = [
  ("P-521", Parse.SEC CoreCrypto.ECC_P521);
  ("P-384", Parse.SEC CoreCrypto.ECC_P384);
  ("P-256", Parse.SEC CoreCrypto.ECC_P256);
  ("X25519", Parse.SEC CoreCrypto.ECC_X25519);
  ("X448",  Parse.SEC CoreCrypto.ECC_X448);
  ("FFDHE4096", Parse.FFDHE Parse.FFDHE4096);
  ("FFDHE3072", Parse.FFDHE Parse.FFDHE3072);
  ("FFDHE2048", Parse.FFDHE Parse.FFDHE2048);
]

let prn s (k, _) = s ^ k ^ ", "

let setcs x =
  let csl = BatString.nsplit x ":" in
  let csl = List.map (fun x->try List.assoc x css with Not_found -> failwith ("Unknown cipher suite "^x^" requested; check --help for list")) csl in
  config := {!config with ciphersuites = cipherSuites_of_nameList csl}

let setsa x =
  let sal = BatString.nsplit x ":" in
  let sal = List.map (fun x->try List.assoc x sas with Not_found -> failwith ("Unknown signature algorithm "^x^"; check --help for list")) sal in
  config := {!config with signatureAlgorithms = sal}

let setng x =
  let ngl = BatString.nsplit x ":" in
  let ngl = List.map (fun x->try List.assoc x ngs with Not_found -> failwith ("Unknown named group "^x^"; check --help for list")) ngl in
  config := {!config with namedGroups = ngl}

let offered_psk = ref []
let loaded_psk : (string list) ref = ref []

let load_psk is_ticket x =
  let id, key = BatString.split x ":" in
  if List.mem id !loaded_psk then failwith ("Cannot load more than one PSK with label "^id);
  loaded_psk := id :: !loaded_psk;
  let id = Platform.Bytes.utf8 id in
  let key = Platform.Bytes.bytes_of_hex key in
  let cipher = List.hd ((!config).ciphersuites) in
  let (ae, h) = match cipher with
    | CipherSuite13(ae,h) -> ae, h
    | _ -> failwith "the first ciphersuite must be 1.3 to load with PSK" in
  let pskInfo = {
    PSK.is_ticket = is_ticket;
    PSK.time_created = Prims.parse_int "0";
    PSK.allow_early_data = true;
    PSK.allow_dhe_resumption = true;
    PSK.allow_psk_resumption = true;
    PSK.early_ae = ae;
    PSK.early_hash = h;
    PSK.identities = Platform.Bytes.empty_bytes, Platform.Bytes.empty_bytes;
   } in
  PSK.coerce_psk id pskInfo key

let offer_psk x =
  let ids = BatString.nsplit x ":" in
  let add_psk y =
    if List.mem y !loaded_psk then
      offered_psk := (Platform.Bytes.utf8 y) :: !offered_psk
    else
      failwith ("Cannot offer PSK with label "^y^" without loading it first")
    in
  List.iter add_psk ids

let help = "A TLS test client.\n\n"
 ^ "Cipher suite names for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" css) ^ "\n"
 ^ "Signature algorithm names for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" sas) ^ "\n"
 ^ "Named groups for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" ngs) ^ "\n"

let _ =
  Arg.parse [
    ("-v", Arg.String (fun s -> let v = s2pv s in config := {!config with maxVer = v;}), " sets maximum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.3)");
    ("-mv", Arg.String (fun s -> let v = s2pv s in config := {!config with minVer = v;}), " sets minimum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.2)");
    ("-s", Arg.Unit (fun () -> role := Server), "run as server instead of client");
    ("-0rtt", Arg.Unit (fun () -> config := {!config with enable_early_data = true;}), "enable early data (server support and client offer)");
    ("-psk", Arg.String (fun s -> load_psk false s), " L:K add an entry in the PSK database at label L with key K (in hex), associated with the fist current -cipher");
    ("-ticket", Arg.String (fun s -> load_psk true s), " T:K add ticket T in the PSK database with RMS K (in hex), associated with the fist current -cipher");
    ("-offerpsk", Arg.String (fun s -> offer_psk s), "offer the given PSK identifier(s) (must be loaded first with -psk or -ticket, client only)");
    ("-tlsapi", Arg.Unit (fun () -> ()), "run through the TLS API (legacy, always on)");
    ("-verify", Arg.Unit (fun () -> config := {!config with check_peer_certificate = true;}), "enforce peer certificate validation");
    ("-ffi", Arg.Unit (fun () -> ffi := true), "test FFI instead of API");
    ("-noems", Arg.Unit (fun () -> config := {!config with safe_resumption = false;}), "disable extended master secret in TLS <= 1.2 (client only)");
    ("-ciphers", Arg.String setcs, "colon-separated list of cipher suites; see above for valid values");
    ("-sigalgs", Arg.String setsa, "colon-separated list of signature algorithms; see above for valid values");
    ("-reconnect", Arg.Unit (fun () -> reconnect := true), "reconnect at the end of the session, using received ticket (client only)");
    ("-groups", Arg.String setng, "colon-separated list of named groups; see above for valid values");
    ("-cert", Arg.String (fun s -> config := {!config with cert_chain_file = s}), "PEM file containing certificate chain to send");
    ("-key", Arg.String (fun s -> config := {!config with private_key_file = s}), "PEM file containing private key of endpoint certificate in chain");
    ("-CAFile", Arg.String (fun s -> config := {!config with ca_file = s}), "set openssl root cert file to <path>")
  ] (fun s->args:=s::!args) help;;

  let (host, port) = match List.rev !args with
    | host :: port :: _ ->
       if !role = Client then config := {!config with peer_name = Some host;};
       (host, int_of_string port)
    | host :: _ ->
       if !role = Client then config := {!config with peer_name = Some host;};
       (host, 443)
    | _ ->
       (if !role = Client then "127.0.0.1" else "0.0.0.0"), 443
    in

  match !role, !config.maxVer with
  | Client, _ when !ffi    -> TestFFI.client !config host (Z.of_int port)
  | Server, _ when !ffi    -> TestFFI.server !config host (Z.of_int port)
  | Client, _ ->
    (let _ = TestAPI.client !config host (Z.of_int port) (!offered_psk) in
    match !reconnect, !config.peer_name with
    | true, Some h ->
      let t = match Ticket.lookup h with None -> [] | Some t -> [t] in
      TestAPI.client !config host (Z.of_int port) t
    | _ -> ())
  | Server, _ -> TestAPI.server !config host (Z.of_int port)

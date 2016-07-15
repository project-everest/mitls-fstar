(* Main driver for interop tests *)
open TLSConstants
open TLSInfo

let tlsapi = ref false
let args = ref []
let role = ref Client
let config = ref {defaultConfig with
  minVer = TLS_1p3;
  maxVer = TLS_1p3;
  check_peer_certificate = false;
  cert_chain_file = "../../data/server.crt";
  private_key_file = "../../data/server.key";
  ca_file = "../../data/ca.crt";
  safe_resumption = true;
  ciphersuites = cipherSuites_of_nameList [TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256];
}

let s2pv = function
  | "1.2" -> TLS_1p2
  | "1.3" -> TLS_1p3
  | "1.1" -> TLS_1p1
  | "1.0" -> TLS_1p0
  | s -> failwith ("Invalid protocol version specified: "^s)

let css = [
  ("ECDHE-RSA-AES256-GCM-SHA384", TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384);
  ("ECDHE-RSA-AES128-GCM-SHA256", TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256);
  ("DHE-RSA-AES256-GCM-SHA384", TLS_DHE_RSA_WITH_AES_256_GCM_SHA384);
  ("DHE-RSA-AES128-GCM-SHA256", TLS_DHE_RSA_WITH_AES_128_GCM_SHA256);
]

let sas = [
  ("RSA+SHA512", (CoreCrypto.RSASIG, Hash CoreCrypto.SHA512));
  ("RSA+SHA384", (CoreCrypto.RSASIG, Hash CoreCrypto.SHA384));
  ("RSA+SHA256", (CoreCrypto.RSASIG, Hash CoreCrypto.SHA256));
  ("RSA+SHA1", (CoreCrypto.RSASIG, Hash CoreCrypto.SHA1));
  ("ECDSA+SHA512", (CoreCrypto.ECDSA, Hash CoreCrypto.SHA512));
  ("ECDSA+SHA384", (CoreCrypto.ECDSA, Hash CoreCrypto.SHA384));
  ("ECDSA+SHA256", (CoreCrypto.ECDSA, Hash CoreCrypto.SHA256));
  ("ECDSA+SHA1", (CoreCrypto.ECDSA, Hash CoreCrypto.SHA1));
]

let ngs = [
  ("P-521", SEC CoreCrypto.ECC_P521);
  ("P-384", SEC CoreCrypto.ECC_P384);
  ("P-256", SEC CoreCrypto.ECC_P256);
  ("FFDHE4096", FFDHE FFDHE4096);
  ("FFDHE3072", FFDHE FFDHE3072);
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

let help = "A TLS test client.\n\n"
 ^ "Cipher suite names for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" css) ^ "\n"
 ^ "Signature algorithm names for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" sas) ^ "\n"
 ^ "Named groups for colon-separated priority string:\n    "
 ^ (List.fold_left prn "" ngs) ^ "\n"

let _ =
  Arg.parse [
          ("-v", Arg.String (fun s -> let v = s2pv s in config := {!config with minVer = v; maxVer = v;}), " sets minimum and maximum protocol version to <1.0 | 1.1 | 1.2 | 1.3>");
    ("-s", Arg.Unit (fun () -> role := Server), "run as server instead of client");
    ("-tlsapi", Arg.Unit (fun () -> tlsapi := true), "run through TLS API instead of scripted test file");
    ("-verify", Arg.Unit (fun () -> config := {!config with check_peer_certificate = true;}), "enforce peer certificate validation");
    ("-noems", Arg.Unit (fun () -> config := {!config with safe_resumption = false;}), "disable extended master secret in TLS <= 1.2");
    ("-ciphers", Arg.String setcs, "colon-separated list of cipher suites; see above for valid values");
    ("-sigalgs", Arg.String setsa, "colon-separated list of signature algorithms; see above for valid values");
    ("-groups", Arg.String setng, "colon-separated list of named groups; see above for valid values");
    ("-cert", Arg.String (fun s -> config := {!config with cert_chain_file = s}), "PEM file containing certificate chain to send");
    ("-key", Arg.String (fun s -> config := {!config with private_key_file = s}), "PEM file containing private key of endpoint certificate in chain");
    ("-CAFile", Arg.String (fun s -> config := {!config with ca_file = s}), "set openssl root cert file to <path>")
  ] (fun s->args:=s::!args) help;;

  let (host, port) = match List.rev !args with
    | host :: port :: _ ->
       config := {!config with peer_name = Some host;};
       host, int_of_string port
    | host :: _ -> host, 443
    | _ -> (if !role = Client then "127.0.0.1" else "0.0.0.0"), 443 in

  match !role, !config.maxVer with
  | Client, TLS_1p3 ->
     if !tlsapi then TestAPI.client !config host port
     else TestHandshake.client_13 !config host port
  | Client, _ -> TestHandshake.client_12 !config host port
  | Server, TLS_1p3 ->
     if !tlsapi then TestAPI.server !config host port
     else TestHandshake.server_13 !config host port
  | Server, _ -> TestHandshake.server_12 !config host port

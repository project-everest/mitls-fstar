open TLSConstants
open TLSInfo

let config = ref {defaultConfig with
  minVer = TLS_1p3;
  maxVer = TLS_1p3;
  check_peer_certificate = false;
  cert_chain_file = "c:\\Repos\\mitls-fstar\\data\\test_chain.pem";
  private_key_file = "c:\\Repos\\mitls-fstar\\data\\server.key";
  ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
  safe_resumption = true;
  ciphersuites = cipherSuites_of_nameList [TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256];
}

let s2pv = function
  | "1.2" -> TLS_1p2
  | "1.3" -> TLS_1p3
  | "1.1" -> TLS_1p1
  | "1.0" -> TLS_1p0
  | s -> failwith ("Invalid protocol version specified: "^s)

let ffiConfig s =
  let v = s2pv s in 
  config := {!config with minVer = v; maxVer = v;}



let _ = Callback.register "MITLS_FFI_Config" ffiConfig;
        Callback.register "MITLS_FFI_Connect" TestAPI.ffiConnect;

(* Main driver for interop tests *)
open TLSConstants
open TLSInfo

let config pv =
  if pv = "1.3" then
    let sigPref = [CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA256] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
     {TLSInfo.defaultConfig with
         minVer = TLS_1p3;
         maxVer = TLS_1p3;
         ciphersuites = csn;
         signatureAlgorithms = sigAlgPrefs;
         ca_file = "";
         cert_chain_file = "../../data/test_chain.pem";
         private_key_file = "../../data/test_chain.key";
         }
  else
    let sigPref = [CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA256] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
     {TLSInfo.defaultConfig with
         minVer = TLS_1p2;
         maxVer = TLS_1p2;
         ciphersuites = csn;
         signatureAlgorithms = sigAlgPrefs;
         ca_file = "";
         cert_chain_file = "../../data/test_chain.pem";
         private_key_file = "../../data/test_chain.key";
         }


let _ =
  if (Array.length Sys.argv <> 4) then
     print_string "Usage: ./server.out <1.2|1.3> <binding> <port>\n"
  else 
     if (Sys.argv.(1) = "1.3") then
       TestServer13.main (config "1.3") Sys.argv.(2) (int_of_string Sys.argv.(3))
     else
       TestServer.main (config "1.2") Sys.argv.(2) (int_of_string Sys.argv.(3))

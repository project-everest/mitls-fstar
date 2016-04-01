module TestClient

open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSConstants
open TLSInfo

let id = {
    msId = noMsId;
    kdfAlg = PRF_SSL3_nested;
    pv = TLS_1p2;
    aeAlg = (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256);
    csrConn = bytes_of_hex "";
    ext = {
      ne_extended_ms = false;
      ne_extended_padding = false;
      ne_secure_renegotiation = RI_Unsupported;
      ne_supported_curves = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
    };
    writer = Client
  }

let main () =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect "ht.vc" 443 in
  let m0 = new_region root in
  let p0 = new_region root in
  let c = TLS.connect m0 p0 tcp Client TLSInfo.defaultConfig in
  match TLS.test_send c id with
  | _ -> ()


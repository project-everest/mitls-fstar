module Test

open Platform.Bytes

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS

let fragment_1 i (b:bytes { length b <= max_TLSPlaintext_fragment_length }) : fragment i (point (length b)) = 
  let rg : frange i = point(length b) in 
  appFragment i rg b 

// move to Bytes
let sub (buffer:bytes) (first:nat) (len:nat { first + len <= length buffer }) = 
  let before, now = split buffer first in 
  let now, after = split buffer len in 
  now 

val write_all': c:Connection.connection -> i:id -> buffer:bytes -> sent:nat {sent <= length buffer} -> St ioresult_w 
let rec write_all' c i buffer sent =  
  if sent = length buffer then Written 
  else 
  let size = min (length buffer - sent) max_TLSPlaintext_fragment_length in
  let payload = sub buffer sent size in
  let rg : frange i = point(length payload) in
  let f : fragment i rg = fragment_1 i payload in
  match assume false; write c f with
  | Written -> write_all' c i buffer (sent+size)
  | r       -> r 

let write_all c i b = write_all' c i b 0

// This sample code is currently full of partial pattern matching
// aka we don't handle any unexpected result or error. 

#set-options "--lax" 
 
let client (here:Connection.c_rgn) tcp config_1 (request:bytes) =
  let c = connect here tcp config_1 in
  let i_0 = currentId c Reader in 
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match read c i_0 with
  //    ClientHello
  //      + KeyShare             -------->
  //                                                  ServerHello
  //                                                   + KeyShare
  //                                         {EncryptedExtensions}
  //                                         {CertificateRequest*}
  //                                        {ServerConfiguration*}
  //                                                {Certificate*}
  //                                          {CertificateVerify*}
  //                             <--------              {Finished}
  //   {Certificate*}
  //   {CertificateVerify*}
  //   {Finished}                -------->
  | Complete ->
  let i = currentId c Writer in
  let f0 = fragment_1 i request  in 
  match write c f0 with 
  //   [Request]                 -------->
  | Written ->
  match read c i with 
  //                             <--------      [Application Data]
  | Read (Data g0) -> 
  let _ = writeCloseNotify c in
  //   [CloseNotify]             -------->
  match read c i with 
  //                             <--------           [CloseNotify] 
  | Read Close -> appBytes g0 
  // At this point, if authId i, I know that 
  // (1) my peer's writer view is exactly ( Data g0 ; Close ), 
  // (2) my peer's reader view is exactly ( Data f0 ; Close ).

  // it seems convenient to have complete return i.
  // the client need not be aware of the handshake epoch.
  // should connect read to completion?

  // we have exactly the same code for 1.2 and 1.3 1RTT 
  // (even with falseStart)

let server (here:Connection.c_rgn) tcp config_1 (respond: (bytes -> bytes)) =
  let c = accept here tcp config_1 in
  let i_0 = currentId c Reader in (
  match read c i_0 with
  | Complete ->
  let i = currentId c Reader in 
  match read c i with 
  | Read (Data f0) ->
  let data = respond (appBytes f0) in
  let response = fragment_1 i data in
  match write c response with
  | Written  -> 
  match read c i with 
  | Read Close -> ())
  // At this point, if authId i, I know that 
  // (1) my peer's writer view is exactly ( Data f0 ; Close )
  // but not what my peer has read, unless the app semantics says so.


let mkConfig cs pvs = // from test_client.ml and test_server.ml
  let l = [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
  let pv = match pvs with 
    | "1.3" -> TLS_1p3 
    | _     -> TLS_1p2 in
  let sigAlgPrefs = [ RSA_PKCS1_SHA256 ] in
  let cfg = ({TLSInfo.defaultConfig with
        minVer = pv;
        maxVer = pv;
        ciphersuites =   cipherSuites_of_nameList l; }) in 

  match cs, pv with
  | Client, TLS_1p3 -> { cfg with 
        namedGroups = [SEC CoreCrypto.ECC_P256; SEC CoreCrypto.ECC_P384];
        check_peer_certificate = false;
        ca_file = "../../data/CAFile.pem";
        }
  | Client, TLS_1p2 -> { cfg with 
         safe_resumption = true;
         signatureAlgorithms = [(CoreCrypto.RSASIG, Hash CoreCrypto.SHA512); 
                                (CoreCrypto.RSASIG, Hash CoreCrypto.SHA384);
                                (CoreCrypto.RSASIG, Hash CoreCrypto.SHA256)];
         check_peer_certificate = false;
         ca_file = "../../data/CAFile.pem";
        }
  | Server, _ -> { cfg with
         signatureAlgorithms = sigAlgPrefs;
         ca_file = "";
         cert_chain_file = "../../data/test_chain.pem";
         private_key_file = "../../data/test_chain.key";
         }


let main cs pv host port = 
  let config = mkConfig cs pv in 
  match cs with 
  | Client -> ( 
    IO.print_string "===============================================\n Starting test TLS client...\n";
    let tcp = Platform.Tcp.connect host port in
    let here = new_region root in 
    client here tcp config

  | Server -> (
    IO.print_string "===============================================\n Starting test TLS server...\n";
    let tcp = Platform.Tcp.connect host port in
    let here = new_region root in 
    client here tcp config pv)
  
  let _ =
    if (Array.length Sys.argv <> 4) then
      print_string "Usage: ./client.out <1.2|1.3> <host> <port>\n"
      else
      if (Sys.argv.(1) = "1.3") then
         TestClient13.main (config "1.3") Sys.argv.(2) (int_of_string Sys.argv.(3))
         else
         TestClient.main () () () () () () (config "1.2") Sys.argv.(2) (int_of_string Sys.argv.(3))
  

(* Notes towards a second example: RPC *)

let N = 100000

type request = rbytes (0,N-1)


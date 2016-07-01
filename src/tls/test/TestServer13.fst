module TestServer13

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open Handshake
open TLSError
open TLSInfo
open TLSConstants
open TLSInfo
open StreamAE
open CoreCrypto
open HandshakeLog

(* FlexRecord *)

//CF 16-04-30 it may be better to pass in a "Content.fragment i"

val encryptRecord_TLS13_AES_GCM_128_SHA256: #id:id -> writer id -> Content.contentType -> bytes -> bytes
let encryptRecord_TLS13_AES_GCM_128_SHA256 #id w ct plain = 
  let text = plain in
  let len = length text in
  let rg: Range.frange id = 0, len in
  let f = Content.mk_fragment id ct rg plain in 
  StreamAE.encrypt w (len+1) f // the extra byte is for CT with no padding

val decryptRecord_TLS13_AES_GCM_128_SHA256: #id:id -> reader id -> Content.contentType -> bytes -> bytes
let decryptRecord_TLS13_AES_GCM_128_SHA256 #id rd ct cipher = 
//  IO.print_string ("cipher:"^(Platform.Bytes.print_bytes cipher)^"\n");
  let (Some d) = StreamAE.decrypt #id rd (length cipher - (StreamAE.ltag id)) cipher in
  Content.repr id d

let sendRecord tcp pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  let Correct _ = Platform.Tcp.send tcp r in
  IO.print_string ("Sending "^Content.ctToString ct^"Data("^str^")\n")

val really_read_rec: bytes -> Platform.Tcp.networkStream -> nat -> optResult string bytes
let rec really_read_rec prev tcp len = 
    if (len <= 0) 
    then Correct(prev)
    else 
      match Platform.Tcp.recv tcp len with
      | Correct b -> 
            let lb = length b in
      	    if (lb >= len) then Correct(prev @| b)
      	    else really_read_rec (prev @| b) tcp (len - lb)
      | e -> e
      
let really_read = really_read_rec empty_bytes

let recvRecord tcp pv = 
  match really_read tcp 5 with 
  | Correct header ->
      match Record.parseHeader header with  
      | Correct (ct,pv,len)  ->
         match really_read tcp len  with
         | Correct payload -> (ct,pv,payload)

let makeHSRecord pv hs_msg =
  let hs = HandshakeMessages.handshakeMessageBytes (Some pv) hs_msg in
  (string_of_handshakeMessage hs_msg,hs)

let sendHSRecord tcp pv hs_msg = 
  let (str,hs) = makeHSRecord pv hs_msg in
  sendRecord tcp pv Content.Handshake hs str

let sendEncHSRecord tcp pv hs_msg wr =
  let (str,hs) = makeHSRecord pv hs_msg in
  let er = encryptRecord_TLS13_AES_GCM_128_SHA256 wr Content.Handshake hs in
  sendRecord tcp pv Content.Application_data er str

let recvHSRecord tcp pv kex = 
  let (Content.Handshake,rpv,pl) = recvRecord tcp pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^") INJECTIVE="^(if equalBytes to_log (HandshakeMessages.handshakeMessageBytes None hs_msg) then "YES" else "NO")^"\n");
	     (hs_msg,to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"

let recvCCSRecord tcp pv = 
  let (Content.Change_cipher_spec,_,ccs) = recvRecord tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, to_log

let recvEncAppDataRecord tcp pv rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

let rec aux config sock =
  let tcp = Platform.Tcp.accept sock in
  let rid = new_region root in
  let lg = HandshakeLog.create #rid in
  let ks, sr = KeySchedule.create #rid Server lg in

  let kex = TLSConstants.Kex_ECDHE in
  let pv = TLS_1p3 in
  let h = CoreCrypto.SHA256 in
  let sa = CoreCrypto.RSASIG in
  let cs = CipherSuite kex (Some sa) (AEAD AES_128_GCM h) in

  let ClientHello(ch), chb = recvHSRecord tcp pv kex in

  let (cr, sid, csl, ext) = (match ch with
    | {ch_protocol_version = TLS_1p3;
       ch_client_random = cr;
       ch_sessionID = sid;
       ch_cipher_suites = csl;
       ch_extensions = Some ext} -> (cr, sid, csl, ext)
    | _ -> failwith "Bad client hello (probably not 1.3)") in

  let (nego, Some keys, (ServerHello sh, shb)) =
  (match Handshake.prepareServerHello config ks lg None (ClientHello ch, chb) with
     | Correct z -> z 
     | Error (x,z) -> failwith z) in

  sendHSRecord tcp pv (ServerHello sh);
  let KeySchedule.StAEInstance rd wr = keys in

  let Correct chain = Cert.lookup_chain config.cert_chain_file in
  let crt = {crt_chain = chain} in
  sendEncHSRecord tcp pv (EncryptedExtensions ({ee_extensions=[]})) wr;
  sendEncHSRecord tcp pv (Certificate crt) wr;

  let _ = lg @@ (EncryptedExtensions ({ee_extensions=[]})) in
  let _ = lg @@ (Certificate crt) in

  let tbs = Handshake.to_be_signed pv Server None (HandshakeLog.getHash lg h) in
  let ha = Hash CoreCrypto.SHA256 in
  let hab, sab = hashAlgBytes ha, sigAlgBytes sa in
  let a = Signature.Use (fun _ -> True) sa [ha] false false in
  let Some csk = Signature.lookup_key #a config.private_key_file in
  let sigv = Signature.sign ha csk tbs in
  let signature = (hab @| sab @| (vlbytes 2 sigv)) in
  sendEncHSRecord tcp pv (CertificateVerify ({cv_sig = signature})) wr;
  let _ = lg @@ (CertificateVerify ({cv_sig = signature})) in

  let svd = KeySchedule.ks_server_13_server_finished ks in
  sendEncHSRecord tcp pv (Finished ({fin_vd = svd})) wr;
  let _ = lg @@ (Finished ({fin_vd = svd})) in
  let KeySchedule.StAEInstance drd dwr = KeySchedule.ks_server_13_sf ks in

  let cvd = KeySchedule.ks_server_13_client_finished ks in
  let Finished({fin_vd = cfin}), _ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ (Finished ({fin_vd = cfin})) in

  (if equalBytes cfin cvd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");

  let req = recvEncAppDataRecord tcp pv drd in
  let text = "You are connected to miTLS* 1.3!\r\nThis is the request you sent:\r\n\r\n" ^ (iutf8 req) in
  let payload = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:" ^ (string_of_int (length (abytes text))) ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text in

  let res = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data res "HTTPResponse";

  Platform.Tcp.close tcp;
  IO.print_string "Closing connection...\n";

  aux config sock

let main config host port =
 IO.print_string "===============================================\n Starting test TLS 1.3 server...\n";
 let sock = Platform.Tcp.listen host port in
 aux config sock


module TestClient13

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

(* FlexRecord *)

val encryptRecord_TLS13_AES_GCM_128_SHA256: #id:id -> writer id -> Content.contentType -> bytes -> bytes
let encryptRecord_TLS13_AES_GCM_128_SHA256 #id w ct plain = 
  // let pv = TLS_1p3 in
  let text = plain in
  // Range.frange -> Range.range
  let len = length text in
  let rg: Range.frange id = 0, len in

  let f = Content.mk_fragment id ct rg plain in 
  StreamAE.encrypt w (len+1) f // the extra byte is for CT with no padding

val decryptRecord_TLS13_AES_GCM_128_SHA256: #id:id -> reader id -> Content.contentType -> bytes -> bytes
let decryptRecord_TLS13_AES_GCM_128_SHA256 #id rd ct cipher = 
//  IO.print_string ("cipher:"^(Platform.Bytes.print_bytes cipher)^"\n");
  let (Some d) = StreamAE.decrypt #id rd (length cipher - (StreamAE.ltag id)) cipher in
  Content.repr id d

// ADL 05/05: tried the top-level but still fails
let sendRecord tcp pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  let Correct _ = Platform.Tcp.send tcp r in
  IO.print_string ("Sending "^Content.ctToString ct^"Data("^str^")\n")


let makeHSRecord pv hs_msg log =
  let hs = HandshakeMessages.handshakeMessageBytes (Some pv) hs_msg in
  (string_of_handshakeMessage hs_msg,hs,log@|hs)

let sendHSRecord tcp pv hs_msg log = 
  let (str,hs,log) = makeHSRecord pv hs_msg log in
  sendRecord tcp pv Content.Handshake hs str;
  log

let recvHSRecord tcp pv kex log = 
  let Correct(Content.Handshake,rpv,pl) = Record.read tcp pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg,log @| to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"

let recvCCSRecord tcp pv = 
  let Correct(Content.Change_cipher_spec,_,ccs) = Record.read tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex log rd = 
  let Correct(Content.Application_data,_,cipher) = Record.read tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, log @| to_log	      

let recvEncAppDataRecord tcp pv rd = 
  let Correct(Content.Application_data,_,cipher) = Record.read tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

// Workaround until KeySchedule is merged in Handshake
let replace_keyshare ksl e =
  match e with
  | TLSExtensions.E_keyShare _ -> TLSExtensions.E_keyShare (ClientKeyShare ksl)
  | x -> x 

let main config host port =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect host port in
  let log = empty_bytes in
  let rid = new_region root in
  let ks, cr = KeySchedule.create #rid Client in
  let lg = HandshakeLog.create #rid in

  // This will call KS.ks_client_13_init_1rtt
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let hash x = CoreCrypto.hash CoreCrypto.SHA256 x in
  let kex = TLSConstants.Kex_ECDHE in
  let log = sendHSRecord tcp pv (ClientHello ch) log in

  let ServerHello(sh),log = recvHSRecord tcp pv kex log in
  let Correct (n,Some k) = Handshake.processServerHello config ks lg None ch (ServerHello sh,log) in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let KeySchedule.StAEInstance rd wr = k in

  let sal = n.n_extensions.ne_signature_algorithms in
  let EncryptedExtensions(ee),log = recvEncHSRecord tcp pv kex log rd in
  let Certificate(sc),log = recvEncHSRecord tcp pv kex log rd in
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain sa (Some host) "../../data/CAFile.pem" then
      "OK" else "FAIL")^"\n");
  let cv_log = hash log in

  let CertificateVerify(cv),log = recvEncHSRecord tcp pv kex log rd in
  IO.print_string ("Signature validation status = " ^
    (if Cert.verify_signature sc.crt_chain pv Server None (Some.v sa) sal cv_log cv.cv_sig then "OK" else "FAIL") ^ "\n");

  let svd = KeySchedule.ks_client_13_1rtt_server_finished ks (hash log) in
  let Finished({fin_vd = sfin}),log = recvEncHSRecord tcp pv kex log rd in

  (if equalBytes sfin svd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");

  let cvd, (KeySchedule.StAEInstance drd dwr) = KeySchedule.ks_client_13_1rtt_client_finished ks (hash log) in
  let cfin = {fin_vd = cvd} in
  let (str,cfinb,log) = makeHSRecord pv (Finished cfin) log in
  IO.print_string "before encrypt \n";
  let efinb = encryptRecord_TLS13_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  sendRecord tcp pv Content.Application_data efinb str;

  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data get "GET /";
  let ad = recvEncAppDataRecord tcp pv drd in
  ()


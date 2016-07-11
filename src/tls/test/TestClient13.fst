module TestClient13

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open HandshakeLog
open Negotiation
open Handshake
open TLSError
open TLSInfo
open TLSConstants
open TLSInfo
open StreamAE
open CoreCrypto
open KeySchedule
open FFICallbacks

(* FlexRecord *)

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
  IO.print_string ("Sending "^Content.ctToString ct^"Data("^str^")\n");
  IO.print_string (print_bytes r)

let makeHSRecord pv hs_msg =
  let hs = HandshakeMessages.handshakeMessageBytes (Some pv) hs_msg in
  (string_of_handshakeMessage hs_msg, hs)

let sendHSRecord tcp pv hs_msg = 
  let (str,hs) = makeHSRecord pv hs_msg in
  sendRecord tcp pv Content.Handshake hs str

let recvHSRecord tcp pv kex = 
  let Correct(Content.Handshake,rpv,pl) = Record.read tcp pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg, to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"

let recvCCSRecord tcp pv = 
  let Correct(Content.Change_cipher_spec,_,ccs) = Record.read tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex rd = 
  let Correct(Content.Application_data,_,cipher) = Record.read tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, to_log

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

  
(*****************************************************************************************)
let newconfig pv peername =
  if pv = "1.3" then
    let sigPref = [CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA256] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
     ({TLSInfo.defaultConfig with
         minVer = TLS_1p3;
         maxVer = TLS_1p3;
         ciphersuites = csn;
         peer_name = Some peername;
         namedGroups = [SEC CoreCrypto.ECC_P256; SEC CoreCrypto.ECC_P384];
         check_peer_certificate = false;
         ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
         })
  else
    let l = [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
    ({TLSInfo.defaultConfig with
         minVer = TLS_1p2;
         maxVer = TLS_1p2;
         ciphersuites = csn;
         peer_name = Some peername;
         safe_resumption = true;
         signatureAlgorithms = [(CoreCrypto.RSASIG, Hash CoreCrypto.SHA512); (CoreCrypto.RSASIG, Hash CoreCrypto.SHA384);(CoreCrypto.RSASIG, Hash CoreCrypto.SHA256)];
         check_peer_certificate = false;
         ca_file = "c:\\Repos\\mitls-fstar\\data\\CAFile.pem";
         })

val ffiConfig: string -> string -> config  
let ffiConfig tlsversion hostname =
  let config = newconfig tlsversion hostname in
  config

    
(*****************************************************************************************)

type callbacks = FFICallbacks.callbacks

val sendTcpPacket: callbacks:callbacks -> buf:bytes -> (result (bytes))
let sendTcpPacket callbacks buf = 
  let result = FFICallbacks.ocaml_send_tcp callbacks (get_cbytes buf) in
  if result < 0 then
    Error (AD_internal_error, "socket send failure")
  else
    Correct buf

val recvTcpPacket: callbacks:callbacks -> maxlen:Prims.int -> (result (bytes))    
let recvTcpPacket callbacks maxlen =
  let str = String.make maxlen 0z in
  let recvlen = FFICallbacks.ocaml_recv_tcp callbacks str  in
  if recvlen < 0 then
    Error (AD_internal_error, "socket receive failure")
  else
    let b = String.substring str 0 recvlen in
    let ab = abytes b in
    Correct ab
  
private val really_read_rec: b:bytes -> callbacks -> l:nat -> (result (lbytes (l+length b)))

let rec really_read_rec prev callbacks len = 
    if len = 0 
    then Correct prev
    else 
      match recvTcpPacket callbacks len with
      | Correct b -> 
            let lb = length b in
      	    if lb = len then Correct(prev @| b)
      	    else really_read_rec (prev @| b) callbacks (len - lb)
      | Error e -> Error e

private let really_read = really_read_rec empty_bytes

val recvRecordCallback: callbacks -> protocolVersion -> 
  (result (Content.contentType * protocolVersion * b:bytes { length b <= max_TLSCiphertext_fragment_length}))
let recvRecordCallback callbacks pv =
  match really_read callbacks 5 with 
  | Correct header -> (
      match Record.parseHeader header with  
      | Correct (ct,pv,len) -> (
         match really_read callbacks len with
         | Correct payload  -> Correct (ct,pv,payload)
         | Error e          -> Error e )
      | Error e             -> Error e )
  | Error e                 -> Error e

let hsbuf = alloc ([] <: list (hs_msg * bytes))

let recvHSRecordCallback callbacks pv kex =
  let Correct(Content.Handshake,rpv,pl) = recvRecordCallback callbacks pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg, to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  
 let recvEncHSRecordCallback callbacks pv kex rd = 
  let Correct(Content.Application_data,_,cipher) = recvRecordCallback callbacks pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, to_log	      
  
let sendRecordCallback callbacks pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  let Correct _ = sendTcpPacket callbacks r in
  IO.print_string ("Sending "^Content.ctToString ct^"Data("^str^")\n")

let sendHSRecordCallback callbacks pv hs_msg = 
  let (str,hs) = makeHSRecord pv hs_msg in
  sendRecordCallback callbacks pv Content.Handshake hs str
    
let makePacket pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  (*let _ = (match ct with
  | Content.Application_data ->   IO.print_string ("Sending Data("^str^")\n")
  | Content.Handshake ->   IO.print_string ("Sending HS("^str^")\n")
  | Content.Change_cipher_spec ->   IO.print_string ("Sending CCS\n")
  | Content.Alert ->   IO.print_string ("Sending Alert("^str^")\n")) in  *)
  r
  
let rec really_check buf len = 
    let lb = length buf in
    if len = 0 then Correct buf
    else if len = lb then Correct buf
    else Error(AD_illegal_parameter,  "Unexpected buffer length")
  
let check_read header record pv =
  match really_check header 5 with 
  | Correct header -> (
      match Record.parseHeader header with  (* contenType protocolVersion length *)
      | Correct (ct,pv,len) -> (
         match really_check record len with
         | Correct payload  -> Correct (ct,pv,payload)
         | Error e          -> Error e )
      | Error e             -> Error e )
  | Error e                 -> Error e

  
  
(*****************************************************************************************)

let ffiConnect13 config callbacks =
  let rid = new_region root in
  let lg = HandshakeLog.create #rid in
  let ks, cr = KeySchedule.create #rid Client lg in

  // This will call KS.ks_client_13_init_1rtt
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let hash x = CoreCrypto.hash CoreCrypto.SHA256 x in
  let kex = TLSConstants.Kex_ECDHE in
  sendHSRecordCallback callbacks pv (ClientHello ch);

  let ServerHello(sh), shb = recvHSRecordCallback callbacks pv kex in
  
  let Correct (n,Some k) = Handshake.processServerHello config ks lg None ch (ServerHello sh, shb) in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex sa (AEAD ae h) = cs in
  let KeySchedule.StAEInstance rd wr = k in
  let sal = n.n_extensions.ne_signature_algorithms in
  
  let EncryptedExtensions(ee),_ = recvEncHSRecordCallback callbacks pv kex rd in
  let _ = lg @@ (EncryptedExtensions (ee)) in
  
  let Certificate(sc),log = recvEncHSRecordCallback callbacks pv kex rd in
  let _ = lg @@ Certificate(sc) in
  
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true (config.peer_name) config.ca_file then
      "OK" else "FAIL")^"\n");
  let cv_log = HandshakeLog.getHash lg h in

  let CertificateVerify(cv),log = recvEncHSRecordCallback callbacks pv kex rd in
  let _ = lg @@ CertificateVerify(cv) in  

  //let _ = IO.debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n") in
  let Some ((sa,h), sigv) = Handshake.sigHashAlg_of_ske cv.cv_sig in
  let a = Signature.Use (fun _ -> True) sa [h] false false in
  let tbs = Handshake.to_be_signed pv Server None cv_log in
  let Some pk = Signature.get_chain_public_key #a sc.crt_chain in

  IO.print_string ("Signature validation status = " ^
    (if Signature.verify h pk tbs sigv then "OK" else "FAIL") ^ "\n");

  let svd = KeySchedule.ks_client_13_server_finished ks in
  let Finished({fin_vd = sfin}),_= recvEncHSRecordCallback callbacks pv kex rd in
  let _ = lg @@ Finished({fin_vd = sfin}) in

  (if equalBytes sfin svd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");
  (* let KeySchedule.StAEInstance drd dwr = KeySchedule.ks_client_13_sf ks in *)
  let bb = KeySchedule.ks_client_13_sf ks in
  let KeySchedule.StAEInstance drd dwr = bb in

  let cvd = KeySchedule.ks_client_13_client_finished ks in
  let cfin = {fin_vd = cvd} in
  let (str,cfinb) = makeHSRecord pv (Finished cfin) in
  let _ = lg @@ (Finished cfin) in
  
  IO.print_string "before encrypt \n";
  let efinb = encryptRecord_TLS13_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  sendRecordCallback callbacks pv Content.Application_data efinb str;

  (* create a closure which is callable as follows:
      sendrecv(0, packet, _)    <- prepare a packet to send, return is encrypted packet ready to send.
      sendrecv(1, header, record) <- decrypt a received packet, return is plaintext 
  *)      
  let sendrecv what v1 v2 = (
  IO.print_string ("sendrecv " ^ string_of_int what ^ "\n");
  match what with
  | 0 -> (
    let payload = v1 in
    let msg = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
    let r = makePacket pv Content.Application_data msg "Send" in
    get_cbytes r)
  | 1 -> (
    let aheader = abytes v1 in
    let arecord = abytes v2 in
    let Correct(Content.Application_data,_,cipher) = check_read aheader arecord pv in
    let p = decryptRecord_TLS13_AES_GCM_128_SHA256 drd Content.Application_data cipher in
    get_cbytes p)
  ) in
  sendrecv

  
let main config host port =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Platform.Tcp.connect host port in
  let rid = new_region root in
  let lg = HandshakeLog.create #rid in
  let ks, cr = KeySchedule.create #rid Client lg in

  // This will call KS.ks_client_13_init_1rtt
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let kex = TLSConstants.Kex_ECDHE in
  sendHSRecord tcp pv (ClientHello ch);

  let ServerHello(sh), shb = recvHSRecord tcp pv kex in

  let Correct (n, Some k) = Handshake.processServerHello config ks lg None ch (ServerHello sh, shb) in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex sa (AEAD ae h) = cs in
  let KeySchedule.StAEInstance rd wr = k in
  let sal = n.n_extensions.ne_signature_algorithms in

  let EncryptedExtensions(ee),_ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ (EncryptedExtensions (ee)) in

  let Certificate(sc),_ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ Certificate(sc) in

  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true (Some host) config.ca_file then
      "OK" else "FAIL")^"\n");
  let cv_log = HandshakeLog.getHash lg h in

  let CertificateVerify(cv),_ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ CertificateVerify(cv) in

  //let _ = IO.debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n") in
  let Some ((sa,h), sigv) = Handshake.sigHashAlg_of_ske cv.cv_sig in
  let a = Signature.Use (fun _ -> True) sa [h] false false in
  let tbs = Handshake.to_be_signed pv Server None cv_log in
  let Some pk = Signature.get_chain_public_key #a sc.crt_chain in

  IO.print_string ("Signature validation status = " ^
    (if Signature.verify h pk tbs sigv then "OK" else "FAIL") ^ "\n");

  let svd = KeySchedule.ks_client_13_server_finished ks in
  let Finished({fin_vd = sfin}),_ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ Finished({fin_vd = sfin}) in

  (if equalBytes sfin svd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");
  let KeySchedule.StAEInstance drd dwr = KeySchedule.ks_client_13_sf ks in

  let cvd = KeySchedule.ks_client_13_client_finished ks in
  let cfin = {fin_vd = cvd} in
  let (str,cfinb) = makeHSRecord pv (Finished cfin) in
  let _ = lg @@ (Finished cfin) in

  IO.print_string "before encrypt \n";
  let efinb = encryptRecord_TLS13_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  sendRecord tcp pv Content.Application_data efinb str;

  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data get "GET /";
  let ad = recvEncAppDataRecord tcp pv drd in
  ()

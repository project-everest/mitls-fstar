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

<<<<<<< HEAD
// Workaround until KeySchedule is merged in Handshake
let replace_keyshare ksl e =
  match e with
  | TLSExtensions.E_keyShare _ -> TLSExtensions.E_keyShare (ClientKeyShare ksl)
  | x -> x 

  
(*****************************************************************************************)
type ffiStateConfigured = {
    cscf_guard: string;
    cscf_config: config;
    }

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
         })
  else
    let l = [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
    ({TLSInfo.defaultConfig with
         minVer = TLS_1p2;
         maxVer = TLS_1p2;
         ciphersuites = csn;
         safe_resumption = true;
         signatureAlgorithms = [(CoreCrypto.RSASIG, Hash CoreCrypto.SHA512); (CoreCrypto.RSASIG, Hash CoreCrypto.SHA384);(CoreCrypto.RSASIG, Hash CoreCrypto.SHA256)];
         check_peer_certificate = false;
         ca_file = "/cygdrive/c/Repos/mitls/data/CAFile.pem";
         peer_name = Some peername;
         })
         
val ffiConfig: string -> string -> ffiStateConfigured  
let ffiConfig tlsversion hostname =
  let config = newconfig tlsversion hostname in
  let state:ffiStateConfigured =
  {
    cscf_guard = "CSCF";
    cscf_config = config;
  } in
  state

    
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

let recvHSRecordCallback12 callbacks pv kex log = 
  let (hs_msg, to_log) = match !hsbuf with
    | [] -> 
      let Correct(ct,rpv,pl) = recvRecordCallback callbacks pv in
      let hsml = match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
      	         | Correct(_,hsml) -> hsml | Error (y,z) -> IO.print_string(z); failwith "parseHSM failed" in
      let (hs_msg, to_log)::r = hsml in
      hsbuf := r; (hs_msg, to_log)
    | h::t -> hsbuf := t; h in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  (hs_msg,to_log)
  
let recvHSRecordCallback callbacks pv kex log = 
  let Correct(Content.Handshake,rpv,pl) = recvRecordCallback callbacks pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg,log @| to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  
 let recvEncHSRecordCallback callbacks pv kex log rd = 
  let Correct(Content.Application_data,_,cipher) = recvRecordCallback callbacks pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, log @| to_log	      
  
let recvEncHSRecordCallback12 callbacks pv kex log rd = 
  let Correct(Content.Handshake,_,cipher) = recvRecordCallback callbacks pv in
  let payload = TestClient.decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  hs_msg,to_log  

let sendRecordCallback callbacks pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  let Correct _ = sendTcpPacket callbacks r in
  IO.print_string ("Sending "^Content.ctToString ct^"Data("^str^")\n")

let sendHSRecordCallback12 callbacks pv (m,b) = 
  let str = string_of_handshakeMessage m in
  sendRecordCallback callbacks pv Content.Handshake b str

let sendHSRecordCallback callbacks pv hs_msg log = 
  let (str,hs,log) = makeHSRecord pv hs_msg log in
  sendRecordCallback callbacks pv Content.Handshake hs str;
  log
    
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

type ffiStateClient12 = {
    cscc_guard: string;
    cscc_pv: protocolVersion;
    cscc_wr: (StatefulLHAE.writer TestClient.id);
    cscc_rd: (StatefulLHAE.reader TestClient.id);
}

let recvCCSRecordCallback callbacks pv = 
  let Correct(Content.Change_cipher_spec,_,ccs) = recvRecordCallback callbacks pv in
  IO.print_string "Received CCS\n";
  ccs

val ffiConnect12: ffiState:ffiStateConfigured -> callbacks:callbacks -> ffiStateClient12
let ffiConnect12 ffiState callbacks =
  let _ = (if not (ffiState.cscf_guard = "CSCF") then IO.print_string ("Incorrect cscf_guard "^ffiState.cscf_guard^"\n")) in
  let config = ffiState.cscf_config in
  let rid = new_region root in
  let log = HandshakeLog.create #rid in

  let ks, cr = KeySchedule.create #rid Client in
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks log None None in
  let pv = ch.ch_protocol_version in 
  let kex = TLSConstants.Kex_ECDHE in

  sendHSRecordCallback12 callbacks pv (ClientHello ch,chb);

  let (ServerHello(sh),shb) = recvHSRecordCallback12 callbacks pv kex log in
  
  let Correct (n,None) = Handshake.processServerHello config ks log None ch (ServerHello(sh),shb) in

  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let ems = n.n_extensions.ne_extended_ms in
  let sal = n.n_extensions.ne_signature_algorithms in

  let (Certificate(sc),scb) = recvHSRecordCallback12 callbacks pv kex log in
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true config.peer_name config.ca_file then
      "OK" else "FAIL")^"\n");

  let (ServerKeyExchange(ske),skeb) = recvHSRecordCallback12 callbacks pv kex log in
  let (ServerHelloDone,shdb) = recvHSRecordCallback12 callbacks pv kex log in

  let tbs = kex_s_to_bytes ske.ske_kex_s in
  let sigv = ske.ske_sig in
  let cr = ch.ch_client_random in
  let sr = sh.sh_server_random in
  let (ClientKeyExchange cke,ckeb) = 
     match
       Handshake.processServerHelloDone config n ks log
      	[(Certificate sc,scb);(ServerKeyExchange ske, skeb);(ServerHelloDone,shdb)]
	[] with
     | Correct [x] -> x 
     | Error (y,z) -> failwith (z ^ "\n") in

  sendHSRecordCallback12 callbacks pv (ClientKeyExchange cke,ckeb);

  let lb = HandshakeLog.getBytes log in
  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
//  IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n");
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n");
  let wr = TestClient.encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = TestClient.decryptor_TLS12_AES_GCM_128_SHA256 sk siv in

  let (Finished cfin, cfinb) = Handshake.prepareClientFinished ks log in
  let str = string_of_handshakeMessage (Finished cfin) in 
  let efinb = TestClient.encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake cfinb in

  sendRecordCallback callbacks pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Client";
  sendRecordCallback callbacks pv Content.Handshake efinb str;

  let _ = recvCCSRecordCallback callbacks pv in
  let (Finished(sfin),sfinb) = recvEncHSRecordCallback12 callbacks pv kex log rd in
  let Correct svd = Handshake.processServerFinished ks log (Finished sfin, sfinb) in


  IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n";
  let newstate:ffiStateClient12 = {
    cscc_guard="CSCC";
    cscc_pv=pv;
    cscc_wr = wr;
    cscc_rd = rd;
  } in
  newstate

  
val ffiPrepareSend12:  ffiState:ffiStateClient12 -> cbytes -> cbytes
let ffiPrepareSend12 ffiState payload =
  let _ = (if not (ffiState.cscc_guard = "CSHS") then IO.print_string ("Incorrect cscc_guard "^ffiState.cscc_guard^"\n")) in
  let _ = (if not (ffiState.cscc_pv = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let pv = ffiState.cscc_pv in
  let wr = ffiState.cscc_wr in
  let msg = TestClient.encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in
  let r = makePacket pv Content.Application_data msg "Send" in
  get_cbytes r
   
val ffiHandleReceiveWorker12: ffiState:ffiStateClient12 -> header:bytes -> record:bytes -> (result (bytes))
let ffiHandleReceiveWorker12 ffiState header record =
  let _ = (if not (ffiState.cscc_guard = "CSCC") then IO.print_string ("Incorrect cscc_guard "^ffiState.cscc_guard^"\n")) in
  let _ = (if not (ffiState.cscc_pv = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let pv = ffiState.cscc_pv in
  let rd = ffiState.cscc_rd in
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); Error (x,z)
  | Correct(Content.Application_data,_,cipher) -> 
      let cleartext = TestClient.decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
      Correct (cleartext)
      
  
val ffiHandleReceive12:  ffiState:ffiStateClient12 -> header:cbytes -> record:cbytes -> cbytes
let ffiHandleReceive12 ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleReceiveWorker12 ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> get_cbytes x 
  
(*****************************************************************************************)

type ffiStateClient13 = {
    cscl_guard: string;
    cscl_pv: protocolVersion;
    cscl_dwr: (StreamAE.writer TestClient.id);
    cscl_drd: (StreamAE.reader TestClient.id);
}
  
val ffiConnect13: ffiState:ffiStateConfigured -> callbacks:callbacks -> ffiStateClient13
let ffiConnect13 ffiState callbacks =
  let _ = (if not (ffiState.cscf_guard = "CSCF") then IO.print_string ("Incorrect cscf_guard "^ffiState.cscf_guard^"\n")) in
  let config = ffiState.cscf_config in
  let log = empty_bytes in
  let rid = new_region root in
  let ks, cr = KeySchedule.create #rid Client in
  let lg = HandshakeLog.create #rid in

  // This will call KS.ks_client_13_init_1rtt
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let hash x = CoreCrypto.hash CoreCrypto.SHA256 x in
  let kex = TLSConstants.Kex_ECDHE in
  let log = sendHSRecordCallback callbacks pv (ClientHello ch) log in

  let ServerHello(sh),log = recvHSRecordCallback callbacks pv kex log in
  let Correct (n,Some k) = Handshake.processServerHello config ks lg None ch (ServerHello sh,log) in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let KeySchedule.StAEInstance rd wr = k in

  let sal = n.n_extensions.ne_signature_algorithms in
  let EncryptedExtensions(ee),log = recvEncHSRecordCallback callbacks pv kex log rd in
  let Certificate(sc),log = recvEncHSRecordCallback callbacks pv kex log rd in
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true (config.peer_name) config.ca_file then
      "OK" else "FAIL")^"\n");
  let cv_log = hash log in

  let CertificateVerify(cv),log = recvEncHSRecordCallback callbacks pv kex log rd in

  //let _ = IO.debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n") in
  let Some ((sa,h), sigv) = Handshake.sigHashAlg_of_ske cv.cv_sig in
  let a = Signature.Use (fun _ -> True) sa [h] false false in
  let tbs = Handshake.to_be_signed pv Server None cv_log in
  let Some pk = Signature.get_chain_public_key #a sc.crt_chain in

  IO.print_string ("Signature validation status = " ^
    (if Signature.verify h pk tbs sigv then "OK" else "FAIL") ^ "\n");

  let svd = KeySchedule.ks_client_13_1rtt_server_finished ks (hash log) in
  let Finished({fin_vd = sfin}),log = recvEncHSRecordCallback callbacks pv kex log rd in

  (if equalBytes sfin svd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");

  let cvd, (KeySchedule.StAEInstance drd dwr) = KeySchedule.ks_client_13_1rtt_client_finished ks (hash log) in
  let cfin = {fin_vd = cvd} in
  let (str,cfinb,log) = makeHSRecord pv (Finished cfin) log in
  IO.print_string "before encrypt \n";
  let efinb = encryptRecord_TLS13_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  sendRecordCallback callbacks pv Content.Application_data efinb str;
  let newstate:ffiStateClient13 = {
    cscl_guard="CSCL";
    cscl_pv=pv;
    cscl_dwr = dwr;
    cscl_drd = drd;
  } in
  newstate


val ffiPrepareSend13:  ffiState:ffiStateClient13 -> cbytes -> cbytes
let ffiPrepareSend13 ffiState payload =
  let _ = (if not (ffiState.cscl_guard = "CSCL") then IO.print_string ("Incorrect cscl_guard "^ffiState.cscl_guard^"\n")) in
  let _ = (if not (ffiState.cscl_pv = TLS_1p3) then IO.print_string ("This call is for TLS 1.3 only\n")) in
  let pv = ffiState.cscl_pv in
  let dwr = ffiState.cscl_dwr in
  let msg = encryptRecord_TLS13_AES_GCM_128_SHA256 dwr Content.Application_data (utf8 payload) in
  let r = makePacket pv Content.Application_data msg "Send" in
  get_cbytes r

  
val ffiHandleReceiveWorker13: ffiState:ffiStateClient13 -> header:bytes -> record:bytes -> (result (bytes))
let ffiHandleReceiveWorker13 ffiState header record =
  let _ = (if not (ffiState.cscl_guard = "CSCL") then IO.print_string ("Incorrect cscl_guard "^ffiState.cscl_guard^"\n")) in
  let _ = (if not (ffiState.cscl_pv = TLS_1p3) then IO.print_string ("This call is for TLS 1.3 only\n")) in
  let pv = ffiState.cscl_pv in
  let drd = ffiState.cscl_drd in
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); Error (x,z)
  | Correct(Content.Application_data,_,cipher) -> 
      let cleartext = decryptRecord_TLS13_AES_GCM_128_SHA256 drd Content.Application_data cipher in
      Correct (cleartext)
  
val ffiHandleReceive13:  ffiState:ffiStateClient13 -> header:cbytes -> record:cbytes -> cbytes
let ffiHandleReceive13 ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleReceiveWorker13 ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> get_cbytes x 
  

  
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

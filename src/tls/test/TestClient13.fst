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
open KeySchedule

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

  
(*****************************************************************************************)
type ffiStateClientHello = {
    csch_guard: string;
    csch_config: config;
    csch_ks: ks;
    csch_log: bytes;
    csch_lg: HandshakeLog.log;
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
         
val ffiConfig: string -> string -> ffiStateClientHello  
let ffiConfig tlsversion hostname =
  let config = newconfig tlsversion hostname in
  let rid=new_region root in
  let ks, cr = KeySchedule.create #rid Client in
  let lg = HandshakeLog.create #rid in
  let log = empty_bytes in
  let state:ffiStateClientHello =
  {
    csch_guard = "CSCH";
    csch_config = config;
    csch_ks = ks;
    csch_log = log;
    csch_lg = lg;
  } in
  state

(*****************************************************************************************)
type ffiStateServerHello = {
    cssh_guard: string;
    cssh_config: config;
    cssh_ks: ks;
    cssh_log: bytes;
    cssh_lg: HandshakeLog.log;
    cssh_ch: HandshakeMessages.ch;
    }
        
val ffiPrepareClientHello: ffiState:ffiStateClientHello -> (cbytes * ffiStateServerHello)
let ffiPrepareClientHello ffiState =
  let _ = (if not (ffiState.csch_guard = "CSCH") then IO.print_string ("Incorrect csch_guard "^ffiState.csch_guard^"\n")) in
  let config = ffiState.csch_config in
  let ks = ffiState.csch_ks in
  let lg = ffiState.csch_lg in
  let log = ffiState.csch_log in
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let kex = TLSConstants.Kex_ECDHE in
  let (str,hs,log) = makeHSRecord pv (ClientHello ch) log in
  let r = Record.makePacket Content.Handshake pv hs in 
  let newstate:ffiStateServerHello = {
        cssh_guard = "CSSH";
        cssh_config = config;
        cssh_ks = ks;
        cssh_log = log;
        cssh_lg = lg;
        cssh_ch = ch;
    } in
  (get_cbytes r, newstate)
  
(*****************************************************************************************)
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
  
let handleHSRecord header record pv kex log = 
match check_read header record pv with
  | Error z -> Error z
  | Correct(Content.Handshake,rpv,pl) -> Handshake.parseHandshakeMessages (Some pv) (Some kex) pl
    
type ffiStateCertificateVerify = {
    cscv_guard: string;
    cscv_config: config;
    cscv_ks: ks;
    cscv_log: bytes;
    cscv_lg: HandshakeLog.log;
    cscv_ch: HandshakeMessages.ch;
    cscv_n:nego;
    cscv_k: option KeySchedule.recordInstance;
    cscv_sh:HandshakeMessages.sh;
    }

 let recvHSRecord2 header record pv kex log = 
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct(Content.Handshake,rpv,pl) -> (
    match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
    | Correct (rem,[(hs_msg,to_log)]) -> 
     	      (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	       (hs_msg,log @| to_log))
    | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
    )
  
 let recvCCRecord2 header record pv kex log = 
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct(Content.Change_cipher_spec,rpv,pl) -> (
    match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
    | Correct (rem,[(hs_msg,to_log)]) -> 
     	      (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	       (hs_msg,log @| to_log))
    | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
    )
  
val ffiHandleServerHelloWorker: ffiState:ffiStateServerHello -> header:cbytes -> record:cbytes -> (result (ffiStateCertificateVerify))
let ffiHandleServerHelloWorker ffiState cheader crecord =
  let _ = (if not (ffiState.cssh_guard = "CSSH") then IO.print_string ("Incorrect cssh_guard "^ffiState.cssh_guard^"\n")) in
  let header = abytes cheader in
  let record = abytes crecord in
  let config = ffiState.cssh_config in
  let log = ffiState.cssh_log in
  let ch = ffiState.cssh_ch in
  let lg = ffiState.cssh_lg in
  let ks = ffiState.cssh_ks in
  let kex = TLSConstants.Kex_ECDHE in
  let pv = config.maxVer in
  let ServerHello(sh),log = recvHSRecord2 header record pv kex log in
  let Correct (n,k) = Handshake.processServerHello config ks lg None ch (ServerHello sh,log) in
    match k with
    | None -> let newstate:ffiStateCertificateVerify = {
        cscv_guard = "CSCV";
        cscv_config=config;
        cscv_ch=ch;
        cscv_ks=ks;
        cscv_log=log;
        cscv_lg=lg;
        cscv_n=n;
        cscv_k=None;
        cscv_sh=sh;
        } in Correct(newstate)
    | Some kk -> let newstate:ffiStateCertificateVerify = {
        cscv_guard = "CSCV";
        cscv_config=config;
        cscv_ch=ch;
        cscv_ks=ks;
        cscv_log=log;
        cscv_lg=lg;
        cscv_n=n;
        cscv_k=Some kk;
        cscv_sh=sh;
        } in Correct(newstate)
  
  val ffiHandleServerHello: ffiState:ffiStateServerHello -> header:cbytes -> record:cbytes -> ffiStateCertificateVerify
  let ffiHandleServerHello ffiState cheader crecord =
    match ffiHandleServerHelloWorker ffiState cheader crecord with
    | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
    | Correct (x) -> x
  
(*****************************************************************************************)
let handleEncHSRecord header record pv kex log rd = 
match check_read header record pv with
  | Error z -> Error z
  | Correct(Content.Application_data,_,cipher) -> 
      let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
                    Handshake.parseHandshakeMessages (Some pv) (Some kex) payload

val ffiHandleEncryptedExtensionsWorker: ffiState:ffiStateCertificateVerify -> header:bytes -> record:bytes -> (result (ffiStateCertificateVerify))
let ffiHandleEncryptedExtensionsWorker ffiState header record =
  let _ = (if not (ffiState.cscv_guard = "CSCV") then IO.print_string ("Incorrect cssh_guard "^ffiState.cscv_guard^"\n")) in
  let config = ffiState.cscv_config in
  let log = ffiState.cscv_log in
  let lg = ffiState.cscv_lg in
  let ks = ffiState.cscv_ks in
  let kex = TLSConstants.Kex_ECDHE in
  let sh = ffiState.cscv_sh in
  let pv = sh.sh_protocol_version in
  match ffiState.cscv_k with
  | k -> Error(AD_illegal_parameter,  "k must be not None here")
  | Some k -> let KeySchedule.StAEInstance rd wr = k in
      (match handleEncHSRecord header record pv kex log rd with
        | Error z -> Error z
        | Correct (rem,[(hs_msg,to_log)]) -> Correct(ffiState) (* bugbug: confirm this is an EncryptedExtensions(ee),log *)
        | Correct (rem, hsm) -> Error (AD_illegal_parameter,  "Unexpected handleEncHSRecord rem hsm"))

val ffiHandleEncryptedExtensions:  ffiState:ffiStateCertificateVerify -> header:cbytes -> record:cbytes -> ffiStateCertificateVerify
let ffiHandleEncryptedExtensions ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleEncryptedExtensionsWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
type ffiStateKeyExchange = {
    cske_guard: string;
    cske_config: config;
    cske_ks: ks;
    cske_log: bytes;
    cske_lg: HandshakeLog.log;
    cske_ch: HandshakeMessages.ch;
    cske_n:nego;
    cske_sc:HandshakeMessages.crt;
    cske_sh:HandshakeMessages.sh;
    cske_scb:bytes;
    }

val ffiHandleCertificateVerifyWorker12: ffiState:ffiStateCertificateVerify -> header:bytes -> record:bytes -> (result (ffiStateKeyExchange))
let ffiHandleCertificateVerifyWorker12 ffiState header record =
  let _ = (if not (ffiState.cscv_guard = "CSCV") then IO.print_string ("Incorrect cssh_guard "^ffiState.cscv_guard^"\n")) in
  let config = ffiState.cscv_config in
  let log = ffiState.cscv_log in
  let sh = ffiState.cscv_sh in
  let n = ffiState.cscv_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  match pv with
    | TLS_1p2 -> (let (Certificate(sc),scb) = recvHSRecord2 header record pv kex log in
                     IO.print_string ("Certificate validation status = " ^
                       (if Cert.validate_chain sc.crt_chain true config.peer_name config.ca_file then
                       "OK" else "FAIL")^"\n");
                   let newstate:ffiStateKeyExchange = {
                    cske_guard = "CSKE";
                    cske_config = config;
                    cske_ks = ffiState.cscv_ks;
                    cske_log = log;
                    cske_lg = ffiState.cscv_lg;
                    cske_ch = ffiState.cscv_ch;
                    cske_n = n;
                    cske_sc = sc;
                    cske_sh = sh;
                    cske_scb = scb;
                   } in
                   Correct(newstate))
    | _ -> Error(AD_illegal_parameter,  "Unsupported sh_protocol_version")
  
  
val ffiHandleCertificateVerify12:  ffiState:ffiStateCertificateVerify -> header:cbytes -> record:cbytes -> ffiStateKeyExchange
let ffiHandleCertificateVerify12 ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleCertificateVerifyWorker12 ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
val ffiHandleCertificateVerifyWorker13: ffiState:ffiStateCertificateVerify -> header:bytes -> record:bytes -> (result (ffiStateCertificateVerify))
let ffiHandleCertificateVerifyWorker13 ffiState header record =
  let _ = (if not (ffiState.cscv_guard = "CSCV") then IO.print_string ("Incorrect cssh_guard "^ffiState.cscv_guard^"\n")) in
  let config = ffiState.cscv_config in
  let log = ffiState.cscv_log in
  let sh = ffiState.cscv_sh in
  let n = ffiState.cscv_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  match pv with
    | TLS_1p3 -> (match ffiState.cscv_k with
                       | k -> Error(AD_illegal_parameter,  "k must be not None here")
                       | Some k -> let KeySchedule.StAEInstance rd wr = k in
                                   (match handleEncHSRecord header record pv kex log rd with
                                          | Error z -> Error z
                                          | Correct (rem,[(hs_msg,to_log)]) -> Correct(ffiState) (* bugbug: confirm this is a Certificate(sc),log *)
                                          | Correct (rem, hsm) -> Error (AD_illegal_parameter,  "Unexpected handleEncHSRecord rem hsm")))
    | _ -> Error(AD_illegal_parameter,  "Unsupported sh_protocol_version")
  
  
val ffiHandleCertificateVerify13:  ffiState:ffiStateCertificateVerify -> header:cbytes -> record:cbytes -> ffiStateCertificateVerify
let ffiHandleCertificateVerify13 ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleCertificateVerifyWorker13 ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
type ffiStateServerHelloDone = {
    cssd_guard: string;
    cssd_config: config;
    cssd_ks: ks;
    cssd_log: bytes;
    cssd_lg: HandshakeLog.log;
    cssd_ch: HandshakeMessages.ch;
    cssd_n:nego;
    cssd_sc:HandshakeMessages.crt;
    cssd_scb: bytes;
    cssd_sh:HandshakeMessages.sh;
    cssd_ske:HandshakeMessages.ske;
    cssd_skeb:bytes;
    }
    
val ffiHandleServerKeyExchangeWorker: ffiState:ffiStateKeyExchange -> header:bytes -> record:bytes -> (result (ffiStateServerHelloDone))
let ffiHandleServerKeyExchangeWorker ffiState header record =
  let _ = (if not (ffiState.cske_guard = "CSKE") then IO.print_string ("Incorrect cske_guard "^ffiState.cske_guard^"\n")) in
  let _ = (if not (ffiState.cske_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let config = ffiState.cske_config in
  let log = ffiState.cske_log in
  let sh = ffiState.cske_sh in
  let n = ffiState.cske_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let (ServerKeyExchange(ske),skeb) = recvHSRecord2 header record pv kex log in
  let newstate:ffiStateServerHelloDone = {
        cssd_guard = "CSSD";
        cssd_config = config;
        cssd_ks = ffiState.cske_ks;
        cssd_log = log;
        cssd_lg = ffiState.cske_lg;
        cssd_ch = ffiState.cske_ch;
        cssd_n = n;
        cssd_sc = ffiState.cske_sc;
        cssd_sh = ffiState.cske_sh;
        cssd_scb = ffiState.cske_scb;
        cssd_sh = sh;
        cssd_ske = ske;
        cssd_skeb = skeb;
        } in
    Correct(newstate)
  
val ffiHandleServerKeyExchange:  ffiState:ffiStateKeyExchange -> header:cbytes -> record:cbytes -> ffiStateServerHelloDone
let ffiHandleServerKeyExchange ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleServerKeyExchangeWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
type ffiStateClientKeyExchange = {
    csck_guard: string;
    csck_config: config;
    csck_log: bytes;
    csck_lg: HandshakeLog.log;
    csck_n:nego;
    csck_ks: ks;
    csck_cke: HandshakeMessages.cke;
    csck_ckeb: bytes;
}

val ffiHandleServerHelloDoneWorker: ffiState:ffiStateServerHelloDone -> header:bytes -> record:bytes -> (result (ffiStateClientKeyExchange))
let ffiHandleServerHelloDoneWorker ffiState header record =
  let _ = (if not (ffiState.cssd_guard = "CSSD") then IO.print_string ("Incorrect cssd_guard "^ffiState.cssd_guard^"\n")) in
  let _ = (if not (ffiState.cssd_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let config = ffiState.cssd_config in
  let log = ffiState.cssd_log in
  let lg = ffiState.cssd_lg in
  let n = ffiState.cssd_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let (ServerHelloDone,shdb) = recvHSRecord2 header record pv kex log in

  let ske = ffiState.cssd_ske in
  let skeb = ffiState.cssd_skeb in
  let tbs = kex_s_to_bytes ske.ske_kex_s in
  let sigv = ske.ske_sig in
  let ch = ffiState.cssd_ch in
  let cr = ch.ch_client_random in
  let sh = ffiState.cssd_sh in
  let sr = sh.sh_server_random in
  let scb = ffiState.cssd_scb in
  let ks = ffiState.cssd_ks in
  let sc = ffiState.cssd_sc in
  let (ClientKeyExchange cke,ckeb) = 
     match
       Handshake.processServerHelloDone config n ks lg
      	[(Certificate sc,scb);(ServerKeyExchange ske, skeb);(ServerHelloDone,shdb)]
	[] with
     | Correct [x] -> x 
     | Error (y,z) -> failwith (z ^ "\n") in
   let newstate:ffiStateClientKeyExchange = {
    csck_guard = "CSCK";
    csck_config = config;
    csck_log = log;
    csck_lg = lg;
    csck_n = n;
    csck_ks = ffiState.cssd_ks;
    csck_cke = cke;
    csck_ckeb = ckeb;
   } in
   Correct(newstate)

val ffiHandleServerHelloDone:  ffiState:ffiStateServerHelloDone -> header:cbytes -> record:cbytes -> ffiStateClientKeyExchange
let ffiHandleServerHelloDone ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleServerHelloDoneWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> (x)
    
(*****************************************************************************************)
let sendRecord2 pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  (*let _ = (match ct with
  | Content.Application_data ->   IO.print_string ("Sending Data("^str^")\n")
  | Content.Handshake ->   IO.print_string ("Sending HS("^str^")\n")
  | Content.Change_cipher_spec ->   IO.print_string ("Sending CCS\n")
  | Content.Alert ->   IO.print_string ("Sending Alert("^str^")\n")) in  *)
  r
 
let sendHSRecord2 pv (m,b) = 
  let str = string_of_handshakeMessage m in
  sendRecord2 pv Content.Handshake b str

val ffiPrepareClientKeyExchange:  ffiState:ffiStateClientKeyExchange -> (cbytes * ffiStateClientKeyExchange)
let ffiPrepareClientKeyExchange ffiState =
  let _ = (if not (ffiState.csck_guard = "CSCK") then IO.print_string ("Incorrect csck_guard "^ffiState.csck_guard^"\n")) in
  let _ = (if not (ffiState.csck_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let n = ffiState.csck_n in
  let pv = n.n_protocol_version in
  let cke = ffiState.csck_cke in
  let ckeb = ffiState.csck_ckeb in
  let r = Record.makePacket Content.Handshake pv ckeb in
  (get_cbytes r, ffiState)

(*****************************************************************************************)
type ffiStateHandshake = {
    cshs_guard: string;
    cshs_config: config;
    cshs_log: bytes;
    cshs_lg: HandshakeLog.log;
    cshs_ks: ks;
    cshs_n:nego;
    cshs_wr: (StatefulLHAE.writer TestClient.id);
    cshs_rd: (StatefulLHAE.reader TestClient.id);
    cshs_efinb: bytes;
    cshs_str: string;
}


val ffiPrepareChangeCipherSpec:  ffiState:ffiStateClientKeyExchange -> (cbytes * ffiStateHandshake)
let ffiPrepareChangeCipherSpec ffiState =
  let _ = (if not (ffiState.csck_guard = "CSCK") then IO.print_string ("Incorrect csck_guard "^ffiState.csck_guard^"\n")) in
  let _ = (if not (ffiState.csck_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let log = ffiState.csck_lg in
  let n = ffiState.csck_n in
  let pv = n.n_protocol_version in
  let ks = ffiState.csck_ks in
  let ems = n.n_extensions.ne_extended_ms in
  let sal = n.n_extensions.ne_signature_algorithms in
  
  let lb = HandshakeLog.getBytes log in
  (* if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
//  IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n"); *)
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  (*IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n"); *)
  let wr = TestClient.encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = TestClient.decryptor_TLS12_AES_GCM_128_SHA256 sk siv in

  let (Finished cfin, cfinb) = Handshake.prepareClientFinished ks log in
  let str = string_of_handshakeMessage (Finished cfin) in 
  let efinb = TestClient.encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  let r = sendRecord2 pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Client" in
  let newstate:ffiStateHandshake = {
    cshs_guard="CSHS";
    cshs_config=ffiState.csck_config;
    cshs_log=ffiState.csck_log;
    cshs_lg=log;
    cshs_ks=ffiState.csck_ks;
    cshs_n=ffiState.csck_n;
    cshs_wr = wr;
    cshs_rd = rd;
    cshs_efinb = efinb;
    cshs_str = str;
  } in
  (get_cbytes r, newstate)
  
val ffiPrepareHandshake:  ffiState:ffiStateHandshake -> (cbytes * ffiStateHandshake)
let ffiPrepareHandshake ffiState =
  let _ = (if not (ffiState.cshs_guard = "CSHS") then IO.print_string ("Incorrect cshs_guard "^ffiState.cshs_guard^"\n")) in
  let _ = (if not (ffiState.cshs_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let n = ffiState.cshs_n in
  let pv = n.n_protocol_version in
  let r = sendRecord2 pv Content.Handshake ffiState.cshs_efinb ffiState.cshs_str in
  (get_cbytes r, ffiState)

(*****************************************************************************************)
val ffiHandleChangeCipherSpecWorker: ffiState:ffiStateHandshake -> header:bytes -> record:bytes -> (result (ffiStateHandshake))
let ffiHandleChangeCipherSpecWorker ffiState header record =
  let _ = (if not (ffiState.cshs_guard = "CSHS") then IO.print_string ("Incorrect cske_guard "^ffiState.cshs_guard^"\n")) in
  let _ = (if not (ffiState.cshs_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let config = ffiState.cshs_config in
  let log = ffiState.cshs_log in
  let n = ffiState.cshs_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); Error (x,z)
  | Correct(Content.Change_cipher_spec,rpv,pl) -> Correct(ffiState)
  
val ffiHandleChangeCipherSpec:  ffiState:ffiStateHandshake -> header:cbytes -> record:cbytes -> ffiStateHandshake
let ffiHandleChangeCipherSpec ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleChangeCipherSpecWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
let recvEncHSRecord2 header record pv kex log rd = 
  let Correct(Content.Handshake,_,cipher) = check_read header record pv in
  let payload = TestClient.decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  hs_msg,to_log

val ffiHandleServerFinishedWorker: ffiState:ffiStateHandshake -> header:bytes -> record:bytes -> (result (ffiStateHandshake))
let ffiHandleServerFinishedWorker ffiState header record =
  let _ = (if not (ffiState.cshs_guard = "CSHS") then IO.print_string ("Incorrect cske_guard "^ffiState.cshs_guard^"\n")) in
  let _ = (if not (ffiState.cshs_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let config = ffiState.cshs_config in
  let log = ffiState.cshs_log in
  let n = ffiState.cshs_n in
  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let rd = ffiState.cshs_rd in
  let ks = ffiState.cshs_ks in
  let lg = ffiState.cshs_lg in
  let (Finished(sfin),sfinb) = recvEncHSRecord2 header record pv kex lg rd in
  let Correct svd = Handshake.processServerFinished ks lg (Finished sfin, sfinb) in
  (*IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n"; *)
  Correct(ffiState)
  
val ffiHandleServerFinished:  ffiState:ffiStateHandshake -> header:cbytes -> record:cbytes -> ffiStateHandshake
let ffiHandleServerFinished ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleServerFinishedWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> x
    
(*****************************************************************************************)
val ffiPrepareSend:  ffiState:ffiStateHandshake -> cbytes -> cbytes
let ffiPrepareSend ffiState payload =
  let _ = (if not (ffiState.cshs_guard = "CSHS") then IO.print_string ("Incorrect cshs_guard "^ffiState.cshs_guard^"\n")) in
  let _ = (if not (ffiState.cshs_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let n = ffiState.cshs_n in
  let pv = n.n_protocol_version in
  let wr = ffiState.cshs_wr in
  let msg = TestClient.encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in
  let r = sendRecord2 pv Content.Application_data msg "Send" in
  get_cbytes r
(*****************************************************************************************)
   
val ffiHandleReceiveWorker: ffiState:ffiStateHandshake -> header:bytes -> record:bytes -> (result (bytes))
let ffiHandleReceiveWorker ffiState header record =
  let _ = (if not (ffiState.cshs_guard = "CSHS") then IO.print_string ("Incorrect cske_guard "^ffiState.cshs_guard^"\n")) in
  let _ = (if not (ffiState.cshs_n.n_protocol_version = TLS_1p2) then IO.print_string ("This call is for TLS 1.2 only\n")) in
  let config = ffiState.cshs_config in
  let n = ffiState.cshs_n in
  let pv = n.n_protocol_version in
  let rd = ffiState.cshs_rd in
  let c = check_read header record pv in
  match c with
  | Error (x,z) -> IO.print_string (z^"\n"); Error (x,z)
  | Correct(Content.Application_data,_,cipher) -> 
      let cleartext = TestClient.decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
      Correct (cleartext)
      
  
val ffiHandleReceive:  ffiState:ffiStateHandshake -> header:cbytes -> record:cbytes -> cbytes
let ffiHandleReceive ffiState header record =
  let h = abytes header in
  let r = abytes record in
  match ffiHandleReceiveWorker ffiState h r with
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  | Correct (x) -> get_cbytes x 
  
(*****************************************************************************************)
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
    (if Cert.validate_chain sc.crt_chain true (Some host) config.ca_file then
      "OK" else "FAIL")^"\n");
  let cv_log = hash log in

  let CertificateVerify(cv),log = recvEncHSRecord tcp pv kex log rd in

  //let _ = IO.debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n") in
  let Some ((sa,h), sigv) = Handshake.sigHashAlg_of_ske cv.cv_sig in
  let a = Signature.Use (fun _ -> True) sa [h] false false in
  let tbs = Handshake.to_be_signed pv Server None cv_log in
  let Some pk = Signature.get_chain_public_key #a sc.crt_chain in

  IO.print_string ("Signature validation status = " ^
    (if Signature.verify h pk tbs sigv then "OK" else "FAIL") ^ "\n");

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

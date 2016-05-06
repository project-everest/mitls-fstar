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

let config =
    let sigPref = [CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA256] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    let csn = cipherSuites_of_nameList l in
     {TLSInfo.defaultConfig with
         minVer = TLS_1p3;
    	 maxVer = TLS_1p3;
	 ciphersuites = csn;
	 }

//CF 16-04-30 it may be better to pass in a "Content.fragment i"

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

let makeHSRecord pv hs_msg log =
  let hs = HandshakeMessages.handshakeMessageBytes pv hs_msg in
  (string_of_handshakeMessage hs_msg,hs,log@|hs)

let sendHSRecord tcp pv hs_msg log = 
  let (str,hs,log) = makeHSRecord pv hs_msg log in
  sendRecord tcp pv Content.Handshake hs str;
  log

let recvHSRecord tcp pv kex log = 
  let (Content.Handshake,rpv,pl) = recvRecord tcp pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg,log @| to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"

let recvCCSRecord tcp pv = 
  let (Content.Change_cipher_spec,_,ccs) = recvRecord tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex log rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, log @| to_log	      

let recvEncAppDataRecord tcp pv rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

// Workaround until KeySchedule is merged in Handshake
let replace_keyshare gn gx e =
  match e with
  | TLSExtensions.E_keyShare _ -> TLSExtensions.E_keyShare (ClientKeyShare [gn, CommonDH.serialize gx])
  | x -> x 

let main host port =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect host port in
  let log = empty_bytes in
  let rid = new_region root in
  let ks = KeySchedule.create #rid config Client in
  
  let (Some gx,ch,chb) = Handshake.prepareClientHello config None None in
  let cr, [(gn, gx)] = KeySchedule.ks_client_13_init_1rtt ks [SEC CoreCrypto.ECC_P256] in

  let pv = ch.ch_protocol_version in
  let hash x = CoreCrypto.hash CoreCrypto.SHA256 x in
  let kex = TLSConstants.Kex_ECDHE in
  let ch = {ch with
    ch_client_random = cr;
    ch_extensions = (match ch.ch_extensions with
      | None -> None
      | Some l -> Some (List.Tot.map (replace_keyshare gn gx) l));} in

  let log = sendHSRecord tcp pv (ClientHello ch) log in

  let ServerHello(sh),log = recvHSRecord tcp pv kex log in
  let Correct (n,ake) = Handshake.processServerHello config None [] ch sh in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in

  let Some (SEC ec,gyb) = n.n_extensions.ne_keyShare in
  let Correct gyb = vlparse 1 gyb in 
  IO.print_string ("server gy:"^(Platform.Bytes.print_bytes gyb)^"\n");
  let Some gy = CommonDH.parse (CommonDH.key_params gx) gyb in
  let KeySchedule.StAEInstance rd wr = KeySchedule.ks_client_13_1rtt ks cs (gn, gy) (hash log) in

  let EncryptedExtensions(ee),log = recvEncHSRecord tcp pv kex log rd in
  let Certificate(sc),log = recvEncHSRecord tcp pv kex log rd in
  let CertificateVerify(cv),log = recvEncHSRecord tcp pv kex log rd in
//  let (ms,cfk,sfk,ts0) = derive_finished_keys xES xES log in
  let svd = KeySchedule.ks_client_13_1rtt_server_finished ks (hash log) in
  let Finished(sfin),log = recvEncHSRecord tcp pv kex log rd in
  // TODO check server finished

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


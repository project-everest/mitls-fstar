module TestClient

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open HandshakeMessages
open TLSError
open TLSInfo
open TLSConstants
open TLSInfo
open StatefulLHAE

let config =
    let sigPref = [CoreCrypto.RSASIG] in
    let hashPref = [Hash CoreCrypto.SHA256] in
    let sigAlgPrefs = sigAlgPref sigPref hashPref in
    let l =         [ TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 ] in
    cut (List.Tot.length l == 7);//this requires 8 unfoldings
    let csn = cipherSuites_of_nameList l in
     {TLSInfo.defaultConfig with
         minVer = TLS_1p2;
    	 maxVer = TLS_1p2;
	 ciphersuites = csn;
	 }

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

let encryptor_TLS12_AES_GCM_128_SHA256 key iv = 
  let r = HyperHeap.root in
  let w: writer id =
    let log: st_log_t r id = ralloc r Seq.createEmpty in
    let seqn: HyperHeap.rref r seqn_t = ralloc r 0 in
    let key: AEAD_GCM.state id Writer =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      AEAD_GCM.State r key iv log counter
    in
    State r log seqn key
  in
  // StatefulLHAE.writer -> StatefulLHAE.state
  w

let decryptor_TLS12_AES_GCM_128_SHA256 key iv = 
  let r = HyperHeap.root in
  let r: reader id =
    let log: st_log_t r id = ralloc r Seq.createEmpty in
    let seqn: HyperHeap.rref r seqn_t = ralloc r 0 in
    let key: AEAD_GCM.state id Reader =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      AEAD_GCM.State r key iv log counter
    in
    State r log seqn key
  in
  // StatefulLHAE.reader -> StatefulLHAE.state
  r

let encryptRecord_TLS12_AES_GCM_128_SHA256 w ct plain = 
  let pv = TLS_1p2 in
  let text = plain in
  // StatefulPlain.adata id -> bytes
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id ct in
  // Range.frange -> Range.range
  let rg: Range.frange id = 0, length text in
  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text |> unsafe_coerce in
  // LHAEPlain.plain -> StatefulPlain.plain -> Content.fragment
  //NS: Not sure about the unsafe_coerce: but, it's presence clearly means that #id cannot be inferred
  let f: LHAEPlain.plain id ad rg = Content.CT_Data #id rg f |> unsafe_coerce in
  // StatefulLHAE.cipher -> StatefulPlain.cipher -> bytes
  // FIXME: without the three additional #-arguments below, extraction crashes
  StatefulLHAE.encrypt #id #ad #rg w f


let decryptRecord_TLS12_AES_GCM_128_SHA256 rd ct cipher = 
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id ct in
  let (Some d) = StatefulLHAE.decrypt #id #ad rd cipher in
  Content.repr id d


let sendHSRecord tcp pv log hs_msg = 
  let r = Record.makePacket Content.Handshake pv hs_msg in
  let Correct _ = Platform.Tcp.send tcp r in
  log @| hs_msg

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

val recvHSRecordRec: bytes -> Platform.Tcp.networkStream -> protocolVersion -> kexAlg -> bytes -> (hs_msg * bytes)
let rec recvHSRecordRec prev tcp pv kex log = 
//  IO.print_string (Platform.Bytes.print_bytes prev);
//  IO.print_string ((string_of_int (length prev))^" left from before\n");
  match really_read tcp 5 with 
  | Correct header ->
      match Record.parseHeader header with  
      | Correct (Content.Handshake,pv,len)  ->
         IO.print_string ((string_of_int len)^" bytes expected\n");
         match really_read tcp len  with
         | Correct payload -> 
	      let buf = prev @| payload in 
	      let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) buf in 
	      //IO.print_string ((string_of_int (List.Tot.length hsm))^" messages\n");
	      //IO.print_string ((string_of_int (length rem))^" left\n");
	      (match hsm with 
	      | [] -> recvHSRecordRec rem tcp pv kex log 
	      | [(hs_msg,to_log)] ->  hs_msg, log @| to_log)

let recvHSRecord = recvHSRecordRec empty_bytes

let sendAppDataRecord tcp pv msg = 
  let r = Record.makePacket Content.Application_data pv msg in
  let Correct _ = Platform.Tcp.send tcp r in
  ()

let sendCCSRecord tcp pv = 
  let r = Record.makePacket Content.Change_cipher_spec pv HandshakeMessages.ccsBytes in
  let Correct _ = Platform.Tcp.send tcp r in
  ()
  
let recvCCSRecord tcp pv = 
  match really_read tcp 5 with 
  | Correct header ->
      match Record.parseHeader header with  
      | Correct (Content.Change_cipher_spec,pv,len)  ->
         match really_read tcp len  with
         | Correct cipher -> cipher


let recvEncHSRecord tcp pv kex log rd = 
  match really_read tcp 5 with 
  | Correct header ->
      match Record.parseHeader header with  
      | Correct (Content.Handshake,pv,len)  ->
         match really_read tcp len  with
         | Correct cipher -> 
	      let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
	      let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
     	      let [(hs_msg,to_log)] = hsm in
	      hs_msg, log @| to_log	      


let recvEncAppDataRecord tcp pv rd = 
  match really_read tcp 5 with 
  | Correct header ->
      match Record.parseHeader header with  
      | Correct (Content.Application_data,pv,len)  ->
         match really_read tcp len  with
         | Correct cipher -> 
	      let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
	      payload

let deriveKeys_TLS12_AES_GCM_128_SHA256 ms cr sr = 
  let b = TLSPRF.kdf (PRF_TLS_1p2 kdf_label ((HMAC CoreCrypto.SHA256))) ms (sr @| cr) 40 in
  let cekb, b = split b 16 in
  let sekb, b = split b 16 in
  let civb, sivb = split b 4 in
  (cekb,civb,sekb,sivb)

    
let main host port =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect host port in
  let log = empty_bytes in
  let (ch,chb) = Handshake.prepareClientHello config None None in
  let pv = ch.ch_protocol_version in 
  let kex = TLSConstants.Kex_ECDHE in
  IO.print_string "Sending ClientHello\n";
  let log = sendHSRecord tcp pv log chb in
  let ServerHello(sh),log = recvHSRecord tcp pv kex log in
  IO.print_string "Received ServerHello\n";
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let Certificate(sc),log = recvHSRecord tcp pv kex log in
  IO.print_string "Received ServerCertificate\n";
  let ServerKeyExchange(ske),log = recvHSRecord tcp pv kex log in
  IO.print_string "Received ServerKeyExchange\n";
  let ServerHelloDone,log = recvHSRecord tcp pv kex log in
  IO.print_string "Received ServerHelloDone\n";
  let KEX_S_DHE gy = ske.ske_kex_s in
  let gx, pms = CommonDH.dh_responder gy in
  let cke = {cke_kex_c = kex_c_of_dh_key gx} in
  let ckeb = clientKeyExchangeBytes sh.sh_protocol_version cke in
  IO.print_string "Sending ClientKeyExchange\n";
  let log = sendHSRecord tcp pv log ckeb in
  let ms = TLSPRF.prf (pv,cs) pms (utf8 "master secret") (ch.ch_client_random @| sh.sh_server_random)  48 in
  IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n");
  let (ck,civ,sk,siv) = deriveKeys_TLS12_AES_GCM_128_SHA256 ms ch.ch_client_random sh.sh_server_random in
  IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n");
  let wr = encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = decryptor_TLS12_AES_GCM_128_SHA256 sk siv in
  IO.print_string "Sending ClientCCS\n";
  sendCCSRecord tcp pv;
  let cfin = {fin_vd = TLSPRF.verifyData (pv,cs) ms Client log} in 
  let cfinb = finishedBytes cfin in
  let efinb = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake cfinb in
  IO.print_string "Sending ClientFinished\n";
  let log = sendHSRecord tcp pv log efinb in
  let _ = recvCCSRecord tcp pv in
  IO.print_string "Received ServerCCS\n";
  let Finished(sfin),log = recvEncHSRecord tcp pv kex log rd in
  IO.print_string "Received ServerFinished\n";
  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in
  IO.print_string "Sending AppData(GET /)\n";
  sendAppDataRecord tcp pv get;
  let ad = recvEncAppDataRecord tcp pv rd in
  IO.print_string "Received AppData:\n";
  IO.print_string ((iutf8 ad)^"\n");
  ()
  

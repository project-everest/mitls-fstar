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
open HandshakeLog

(* FlexRecord *)

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
         safe_resumption = true;
	 }

let id = {
    msId = noMsId;
    kdfAlg = PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256);
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
      ne_keyShare = None
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

(* We should use Content.mk_fragment |> Content.repr, not Record.makePacket *)
(* Even better, we should move to TLS.send *)

let sendRecord tcp pv ct msg str = 
  let r = Record.makePacket ct pv msg in
  let Correct _ = Platform.Tcp.send tcp r in
  match ct with
  | Content.Application_data ->   IO.print_string ("Sending Data("^str^")\n")
  | Content.Handshake ->   IO.print_string ("Sending HS("^str^")\n")
  | Content.Change_cipher_spec ->   IO.print_string ("Sending CCS\n")
  | Content.Alert ->   IO.print_string ("Sending Alert("^str^")\n")

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
//      IO.print_string ("GOT HEADER "^(Platform.Bytes.print_bytes header)^"\n");
      match Record.parseHeader header with  
      | Correct (ct,pv,len)  ->
         match really_read tcp len  with
         | Correct payload -> (ct,pv,payload)

let makeHSRecord pv hs_msg log =
  let mb = log @@ hs_msg in 
  (string_of_handshakeMessage hs_msg,mb)

let sendHSRecord tcp pv hs_msg log = 
  let (str,hs) = makeHSRecord pv hs_msg log in
  sendRecord tcp pv Content.Handshake hs str

let recvHSRecord tcp pv kex log = 
  let (Content.Handshake,rpv,pl) = recvRecord tcp pv in
  let Correct (rem,[(hs_msg,to_log)]) = Handshake.parseHandshakeMessages (Some pv) (Some kex) pl in 
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = log @@ hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  hs_msg

let recvCCSRecord tcp pv = 
  let (Content.Change_cipher_spec,_,ccs) = recvRecord tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex log rd = 
  let (Content.Handshake,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = log @@ hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  hs_msg

let recvEncAppDataRecord tcp pv rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

(* Flex Handshake *)


let main host port =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect host port in
  let rid = new_region root in
  let log = HandshakeLog.init TLS_1p2 rid in

  let ks = KeySchedule.create #rid config Client in
  let cr, _ = KeySchedule.ks_client_init_12 ks in  
  let _, ch, _ = Handshake.prepareClientHello config None None in
  let ch = {ch with ch_client_random = cr} in

  let pv = ch.ch_protocol_version in 
  let kex = TLSConstants.Kex_ECDHE in
  sendHSRecord tcp pv (ClientHello ch) log;

  let ServerHello(sh) = recvHSRecord tcp pv kex log in
  let Correct n = TLSExtensions.negotiateClientExtensions sh.sh_protocol_version config ch.ch_extensions sh.sh_extensions sh.sh_cipher_suite None false in
  let pv = sh.sh_protocol_version in
  let cs = sh.sh_cipher_suite in
  let sr = sh.sh_server_random in
  let CipherSuite kex sa ae = cs in
  let ems = n.ne_extended_ms in

  let Certificate(sc) = recvHSRecord tcp pv kex log in
  let ServerKeyExchange(ske) = recvHSRecord tcp pv kex log in
  let ServerHelloDone = recvHSRecord tcp pv kex log in

  let dhp = CommonDH.ECP ({CoreCrypto.curve = CoreCrypto.ECC_P256; CoreCrypto.point_compression = false; }) in
  let KEX_S_DHE gy = ske.ske_kex_s in
  let gx = KeySchedule.ks_client_12_full_dh ks sr pv cs ems dhp gy in
  let cke = {cke_kex_c = kex_c_of_dh_key gx} in

  sendHSRecord tcp pv (ClientKeyExchange cke) log;
  let lb = HandshakeLog.getBytes log in
  if ems then KeySchedule.ks_client_12_set_session_hash ks lb;
  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";

//  IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n");
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n");
  let wr = encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = decryptor_TLS12_AES_GCM_128_SHA256 sk siv in

  let lb = HandshakeLog.getBytes log in
  let cfin = {fin_vd = KeySchedule.ks_client_12_verify_data ks lb} in
  let (str,cfinb) = makeHSRecord pv (Finished cfin) log in
  let efinb = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake cfinb in

  sendRecord tcp pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Client";
  sendRecord tcp pv Content.Handshake efinb str;

  let _ = recvCCSRecord tcp pv in
  let Finished(sfin) = recvEncHSRecord tcp pv kex log rd in

  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in

  sendRecord tcp pv Content.Application_data get "GET /";
  let ad = recvEncAppDataRecord tcp pv rd in
//  let ad = recvEncAppDataRecord tcp pv rd in
//  let ad = recvEncAppDataRecord tcp pv rd in
//  let ad = recvEncAppDataRecord tcp pv rd in
//  let ad = recvEncAppDataRecord tcp pv rd in
//  let ad = recvEncAppDataRecord tcp pv rd in
  ()

  




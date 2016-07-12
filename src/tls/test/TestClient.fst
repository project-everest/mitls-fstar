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
open StAE
open Negotiation
open HandshakeLog
open Handshake


let id =
  let er = createBytes 32 (Char.char_of_int 0) in
  let kdf = PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256) in
  let gx = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let g = CommonDH.key_params gx in
  let gy, gxy = CommonDH.dh_responder gx in
  let msid = StandardMS (PMS.DHPMS(g, (CommonDH.share_of_key gx), (CommonDH.share_of_key gy), (PMS.ConcreteDHPMS gxy))) (er @| er) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256) er er Client

let encryptor_TLS12_AES_GCM_128_SHA256 key iv =
  let r = HyperHeap.root in
  let w: writer id =
    assume (~(authId id));
    let seqn: HyperHeap.rref r seqn_t = ralloc r 0 in
    let st: StAE.state id Writer =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      StLHAE () (AEAD_GCM.State #id #Writer #r #r key iv () counter)
    in
    st
  in
  w

let decryptor_TLS12_AES_GCM_128_SHA256 key iv =
  let r = HyperHeap.root in
  let r: reader id =
    assume (~(authId id));
    let seqn: HyperHeap.rref r seqn_t = ralloc r 0 in
    let st: StAE.state id Reader =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      StLHAE () (AEAD_GCM.State #id #Reader #r #r key iv () counter)
    in
    st
  in
  r

let encryptRecord_TLS12_AES_GCM_128_SHA256 w ct plain : bytes =
  let pv = TLS_1p2 in
  let text = plain in
  let rg: Range.frange id = 0, length text in
  // DataStream.fragment -> DataStream.pre_fragment -> bytes
  let f: DataStream.fragment id rg = text |> unsafe_coerce in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id w f

let decryptRecord_TLS12_AES_GCM_128_SHA256 rd ct cipher =
  let Some d = StAE.decrypt #id rd (ct,cipher) in
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

let sendHSRecord tcp pv (m,b) = 
  let str = string_of_handshakeMessage m in
  sendRecord tcp pv Content.Handshake b str


let hsbuf = alloc ([] <: list (hs_msg * bytes))

let recvHSRecord tcp pv kex log = 
  let (hs_msg, to_log) = match !hsbuf with
    | [] -> 
      let (ct,rpv,pl) = recvRecord tcp pv in
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
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string "no\n";
  hs_msg,to_log

let recvEncAppDataRecord tcp pv rd = 
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

(* Flex Handshake *)

let main config host port =
  IO.print_string "===============================================\n Starting test TLS client...\n";
  let tcp = Platform.Tcp.connect host port in
  let rid = new_region root in
  let log = HandshakeLog.create #rid in

  let ks, cr = KeySchedule.create #rid Client log in
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks log None None in
  let pv = ch.ch_protocol_version in 
  let kex = TLSConstants.Kex_ECDHE in

  sendHSRecord tcp pv (ClientHello ch,chb);

  let (ServerHello(sh),shb) = recvHSRecord tcp pv kex log in
  
  let Correct (n,None) = Handshake.processServerHello config ks log None ch (ServerHello(sh),shb) in

  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let ems = n.n_extensions.ne_extended_ms in
  let sal = n.n_extensions.ne_signature_algorithms in

  let (Certificate(sc),scb) = recvHSRecord tcp pv kex log in
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true (Some host) config.ca_file then
      "OK" else "FAIL")^"\n");

  let (ServerKeyExchange(ske),skeb) = recvHSRecord tcp pv kex log in
  let (ServerHelloDone,shdb) = recvHSRecord tcp pv kex log in

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

  sendHSRecord tcp pv (ClientKeyExchange cke,ckeb);

  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
//  IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n");
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n");
  let wr = encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = decryptor_TLS12_AES_GCM_128_SHA256 sk siv in

  let (Finished cfin, cfinb) = Handshake.prepareClientFinished ks log in
  let str = string_of_handshakeMessage (Finished cfin) in 
  let efinb = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake cfinb in

  sendRecord tcp pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Client";
  sendRecord tcp pv Content.Handshake efinb str;

  let _ = recvCCSRecord tcp pv in
  let (Finished(sfin),sfinb) = recvEncHSRecord tcp pv kex log rd in
  let Correct svd = Handshake.processServerFinished ks log (Finished sfin, sfinb) in


  IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n";


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

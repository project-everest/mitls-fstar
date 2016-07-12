module TLSClient

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
open Negotiation
open HandshakeLog
open Handshake
open FFICallbacks

(* FlexRecord *)

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
    let st: AEAD_GCM.state id Writer =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      AEAD_GCM.State key iv () counter
    in
    st
  in
  // StatefulLHAE.writer -> StatefulLHAE.state
  w


let decryptor_TLS12_AES_GCM_128_SHA256 key iv = 
  let r = HyperHeap.root in
  let r: reader id =
    assume (~(authId id));
    let seqn: HyperHeap.rref r seqn_t = ralloc r 0 in
    let st: AEAD_GCM.state id Reader =
      // The calls to [unsafe_coerce] are here because we're breaking
      // abstraction, as both [key] and [iv] are declared as private types.
      let key: AEAD_GCM.key id = key |> unsafe_coerce in
      let iv: AEAD_GCM.iv id = iv |> unsafe_coerce in
      let log: HyperHeap.rref r _ = ralloc r Seq.createEmpty in
      let counter = ralloc r 0 in
      AEAD_GCM.State key iv () counter
    in
    st
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
  StatefulLHAE.encrypt #id w ad rg f

let decryptRecord_TLS12_AES_GCM_128_SHA256 rd ct cipher = 
  let ad: StatefulPlain.adata id = StatefulPlain.makeAD id ct in
  let (Some d) = StatefulLHAE.decrypt #id rd ad cipher in
  Content.repr id d

let hsbuf = alloc ([] <: list (hs_msg * bytes))

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
  
private val really_read_rec_callback: b:bytes -> callbacks -> l:nat -> (result (lbytes (l+length b)))

let rec really_read_rec_callback prev callbacks len = 
    if len = 0 
    then Correct prev
    else 
      match recvTcpPacket callbacks len with
      | Correct b -> 
            let lb = length b in
      	    if lb = len then Correct(prev @| b)
      	    else really_read_rec_callback (prev @| b) callbacks (len - lb)
      | Error e -> Error e

private let really_read_callback = really_read_rec_callback empty_bytes

val recvRecordCallback: callbacks -> protocolVersion -> 
  (result (Content.contentType * protocolVersion * b:bytes { length b <= max_TLSCiphertext_fragment_length}))
let recvRecordCallback callbacks pv =
  match really_read_callback callbacks 5 with 
  | Correct header -> (
      match Record.parseHeader header with  
      | Correct (ct,pv,len) -> (
         match really_read_callback callbacks len with
         | Correct payload  -> Correct (ct,pv,payload)
         | Error e          -> Error e )
      | Error e             -> Error e )
  | Error e                 -> Error e

(*let hsbuf = alloc ([] <: list (hs_msg * bytes)) *)

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
  
let recvHSRecordCallback callbacks pv kex =
  let Correct(Content.Handshake,rpv,pl) = recvRecordCallback callbacks pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg, to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"
  
let recvEncHSRecordCallback callbacks pv kex log rd = 
  let Correct(Content.Handshake,_,cipher) = recvRecordCallback callbacks pv in
  let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
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

let recvCCSRecordCallback callbacks pv = 
  let Correct(Content.Change_cipher_spec,_,ccs) = recvRecordCallback callbacks pv in
  IO.print_string "Received CCS\n";
  ccs
  
let connect config callbacks =
  let rid = new_region root in
  let log = HandshakeLog.create #rid in

  let ks, cr = KeySchedule.create #rid Client log in
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
    (if Cert.validate_chain sc.crt_chain true (config.peer_name) config.ca_file then
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

  sendRecordCallback callbacks pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Client";
  sendRecordCallback callbacks pv Content.Handshake efinb str;

  let _ = recvCCSRecordCallback callbacks pv in
  let (Finished(sfin),sfinb) = recvEncHSRecordCallback callbacks pv kex log rd in
  let Correct svd = Handshake.processServerFinished ks log (Finished sfin, sfinb) in

  IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n";
 
  let sendrecv what v1 v2 = (
  match what with
  | 0 -> (
    let payload = v1 in
    let msg = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in
    let r = makePacket pv Content.Application_data msg "Send" in
    get_cbytes r)
  | 1 -> (
    let aheader = abytes v1 in
    let arecord = abytes v2 in
    let Correct(Content.Application_data,_,cipher) = check_read aheader arecord pv in
    let p = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Application_data cipher in
    get_cbytes p)
  ) in
  sendrecv

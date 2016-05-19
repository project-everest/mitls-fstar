module TestServer

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
      ne_supported_groups = None;
      ne_supported_point_formats = None;
      ne_server_names = None;
      ne_signature_algorithms = None;
      ne_keyShare = None;
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
//  IO.print_string ((Platform.Bytes.print_bytes r) ^ "\n\n");
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
      match Record.parseHeader header with  
      | Correct (ct,pv,len)  ->
         match really_read tcp len  with
         | Correct payload -> (ct,pv,payload)

let makeHSRecord pv hs_msg log =
  let mb = log @@ hs_msg in 
  (string_of_handshakeMessage hs_msg, mb)

let sendHSRecord tcp pv (m,b) = 
  let str = string_of_handshakeMessage m in
  sendRecord tcp pv Content.Handshake b str

let recvHSRecord tcp pv kex = 
  let (Content.Handshake,rpv,pl) = recvRecord tcp pv in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (rem,[(hs_msg,to_log)]) -> 
    	    IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n"); 
	    let logged = handshakeMessageBytes (Some pv) hs_msg in
	    IO.print_string ("Logged message = Parsed message? ");
	    if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n" else IO.print_string ("no\nBEFORE="^(print_bytes to_log)^"\nAFTER="^(print_bytes logged)^"\n");
	    hs_msg,to_log
  | Error (y,x) -> IO.print_string("HS msg parsing error: "^x); failwith "error"

let recvCCSRecord tcp pv = 
  let (Content.Change_cipher_spec,_,ccs) = recvRecord tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex rd = 
  let (Content.Handshake,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord_TLS12_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
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


let deriveKeys_TLS12_AES_GCM_128_SHA256 ms cr sr = 
  let b = TLSPRF.kdf id.kdfAlg ms (sr @| cr) 40 in
  let cekb, b = split b 16 in
  let sekb, b = split b 16 in
  let civb, sivb = split b 4 in
  (cekb,civb,sekb,sivb)

let rec print_chain = function
  | [] -> ()
  | h::t -> IO.print_string (print_bytes h); print_chain t
    
let rec aux config sock =
  let tcp = Platform.Tcp.accept sock in
  let rid = new_region root in
  let log = HandshakeLog.create #rid in
  let dummy_log = HandshakeLog.create #rid in // To avoid duplication with HS
  let pv = TLS_1p2 in
  let kex = TLSConstants.Kex_ECDHE in
  let ks, sr = KeySchedule.create #rid Server in

  // Get client hello
  let ClientHello(ch),chb = recvHSRecord tcp pv kex in

  // Server Hello
  let (nego,(ServerHello sh,shb)) = 
      (match Handshake.prepareServerHello config ks log None (ClientHello ch,chb) with
       | Correct x -> x
       | Error (x,z) -> failwith z) in
  let next = match nego with | {Handshake.n_extensions = n} -> n  in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex (Some sa) ae = cs in
  let alg = (sa, Hash CoreCrypto.SHA256) in
  let ems = next.ne_extended_ms in

  sendHSRecord tcp pv (ServerHello sh,shb);

  // Server Certificate
  let Correct (chain, csk) = Cert.lookup_server_chain config.cert_chain_file config.private_key_file pv (Some sa) None in
  let c = {crt_chain = chain} in
  let cb = certificateBytes pv c in

  let gn = match nego with | {Handshake.n_dh_group = Some n} -> n  in
  let gy = KeySchedule.ks_server_12_init_dh ks ch.ch_client_random pv cs ems gn in
  // Server Key Exchange
  let kex_s = KEX_S_DHE gy in
  let tbs = kex_s_to_bytes kex_s in
  let cr = ch.ch_client_random in
  let sr = sh.sh_server_random in
  let Correct sigv = Cert.sign pv Server (Some (cr @| sr)) csk alg tbs in
  let ske = {ske_kex_s = kex_s; ske_sig = sigv} in
  IO.print_string ("TBS = " ^ (print_bytes tbs) ^ "\n SIG = " ^(print_bytes sigv)^ "\n");

//  print_chain chain;
  IO.print_string ("Signature validation status = " ^
    (if Cert.verify_signature chain pv Server (Some (cr @| sr)) sa next.ne_signature_algorithms tbs sigv then "OK" else "FAIL") ^ "\n");

  let cb = log @@ Certificate(c) in
  sendHSRecord tcp pv (Certificate c,cb);
  let skeb = log @@ ServerKeyExchange(ske) in
  sendHSRecord tcp pv (ServerKeyExchange ske,skeb);
  let shdb = log @@ ServerHelloDone in
  sendHSRecord tcp pv (ServerHelloDone,shdb);

  // Get Client Key Exchange
  let (ClientKeyExchange(cke),ckeb) = recvHSRecord tcp pv kex in
  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
  let gx = match cke with
    | {cke_kex_c = KEX_C_ECDHE u} -> u
    | _ -> failwith "Bad CKE type" in
  IO.print_string ("client share:"^(Platform.Bytes.print_bytes gx)^"\n");

  let _ = log @@ ClientKeyExchange(cke) in
  let lb = HandshakeLog.getBytes log in
  KeySchedule.ks_server_12_cke_dh ks gx lb;

  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  let wr = encryptor_TLS12_AES_GCM_128_SHA256 ck civ in
  let rd = decryptor_TLS12_AES_GCM_128_SHA256 sk siv in

  let _ = recvCCSRecord tcp pv in
  let Finished(cfin) = recvEncHSRecord tcp pv kex rd in
  let _ = log @@ Finished(cfin) in
  let lb = HandshakeLog.getBytes log in
  let svd = KeySchedule.ks_server_12_server_verify_data ks lb in
  let sfin = {fin_vd = svd} in
  let sfinb = log @@ Finished(sfin) in
  let efinb = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Handshake sfinb in
  let str = string_of_handshakeMessage (Finished sfin) in 

  sendRecord tcp pv Content.Change_cipher_spec HandshakeMessages.ccsBytes "Server";
  sendRecord tcp pv Content.Handshake efinb str;

  let req = recvEncAppDataRecord tcp pv rd in

  let text = "You are connected to miTLS*!\r\nThis is the request you sent:\r\n\r\n" ^ (iutf8 req) in
  let payload = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:" ^ (string_of_int (length (abytes text))) ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text in
  let payload = encryptRecord_TLS12_AES_GCM_128_SHA256 wr Content.Application_data (utf8 payload) in

  let _ = sendRecord tcp pv Content.Application_data payload "httpResponse" in
  Platform.Tcp.close tcp;
  IO.print_string "Closing connection...\n";

  aux config sock

let main config host port =
 IO.print_string "===============================================\n Starting test TLS server...\n";
 let sock = Platform.Tcp.listen host port in
 aux config sock



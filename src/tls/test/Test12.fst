module Test12

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages
open HandshakeLog
open Negotiation

module TCP = Platform.Tcp


let pre_id (role:role) =
  let cr  = createBytes 32 0z in
  let sr  = createBytes 32 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256) in
  let gx  = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let g   = CommonDH.key_params gx in
  let gy, gxy = CommonDH.dh_responder gx in
  let pms = PMS.DHPMS (g, (CommonDH.share_of_key gx), (CommonDH.share_of_key gy), (PMS.ConcreteDHPMS gxy)) in
  let msid = StandardMS pms (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256) cr sr role

val encryptor: r:role -> StAE.keyBytes (pre_id r) -> StAE.writer (pre_id r)
let encryptor r key =
  let id = pre_id r in
  assume (~(authId id));
  StAE.coerce HyperHeap.root id key

val decryptor: r:role -> StAE.keyBytes (pre_id r) -> StAE.reader (pre_id r)
let decryptor r key =
  let wr = encryptor r key in
  let id = pre_id r in
  let rgn = new_region (parent (StAE.region #id #Writer wr)) in
  assume (rgn <> (StAE.region #id #Writer wr));
  StAE.genReader rgn #id wr

let encryptRecord r (wr:StAE.writer (pre_id r)) ct plain : bytes =
  let id = pre_id r in
  let rg: Range.frange id = (0, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

#set-options "--lax"

let decryptRecord r (rd:StAE.reader (pre_id r)) ct cipher : bytes =
  let id = pre_id r in
  let ctxt: StAE.decrypted id = (ct, cipher) in
  let Some d = StAE.decrypt #id rd ctxt in
  Content.repr id d

let sendRecord tcp pv ct msg =
  let r = Record.makePacket ct pv msg in
  match TCP.send tcp r with
  | Error z -> failwith z
  | Correct _ -> ()

val really_read_rec: bytes -> TCP.networkStream -> nat -> optResult string bytes
let rec really_read_rec prev tcp len = 
  if len <= 0 then Correct prev
  else
    match TCP.recv tcp len with
    | Correct b ->
      let lb = length b in
      if lb >= len then Correct (prev @| b)
      else really_read_rec (prev @| b) tcp (len - lb)
    | e -> e

let really_read = really_read_rec empty_bytes

let recvRecord tcp pv = 
  match really_read tcp 5 with 
  | Correct header ->
    match Record.parseHeader header with
    | Correct (ct,pv,len)  ->
      match really_read tcp len  with
      | Correct payload -> ct, pv, payload

let sendHSRecord tcp pv msg =
  sendRecord tcp pv Content.Handshake msg

let hsbuf = alloc #(list (hs_msg * bytes)) []

let recvHSRecord tcp pv kex =
  let (hs_msg, to_log) =
    match !hsbuf with
    | [] -> 
      let (ct,rpv,pl) = recvRecord tcp pv in
      let hsml =
	match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
      	| Correct (_,hsml) -> hsml
	| Error (_,z)      -> failwith z in
      let (hs_msg, to_log) :: rem = hsml in
      hsbuf := rem;
      (hs_msg, to_log)
    | h::rem ->
      hsbuf := rem;
      h
  in
  IO.print_string ("Received HS(" ^ (string_of_handshakeMessage hs_msg) ^ ")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n"
  else IO.print_string "no\n";
  hs_msg, to_log

let recvCCSRecord tcp pv = 
  let (Content.Change_cipher_spec,_,ccs) = recvRecord tcp pv in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord r tcp pv kex rd =
  let (_,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord r rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS(" ^ (string_of_handshakeMessage hs_msg) ^ ")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n"
  else IO.print_string "no\n";
  hs_msg, to_log

let recvEncAppDataRecord r tcp pv rd =
  let (Content.Application_data,_,cipher) = recvRecord tcp pv in
  let payload = decryptRecord r rd Content.Application_data cipher in
  IO.print_string ("Received Data:\n" ^ (iutf8 payload) ^ "\n");
  payload


(*-----------------------------------------------------------------------------*)
// TLS 1.2 Server
let rec server_loop config sock =
  let tcp = TCP.accept sock in
  let rid = new_region root in
  let log = HandshakeLog.create #rid in
  let ks, sr = KeySchedule.create #rid Server log in

  let kex = TLSConstants.Kex_ECDHE in
  let pv = TLS_1p2 in

  // Receive ClientHello
  let ClientHello(ch), chb = recvHSRecord tcp pv kex in

  // Send ServerHello
  let (nego, None, (ServerHello sh, shb)) =
    begin
    match Handshake.prepareServerHello config ks log None (ClientHello ch, chb) with
     | Correct x -> x
     | Error (x,z) -> failwith z
    end
  in
  sendHSRecord tcp pv shb;

  // 'Negotiate' ciphersuite, EMS
  let next = match nego with | {Negotiation.n_extensions = n} -> n in
  let cs = sh.sh_cipher_suite in
  let CipherSuite kex (Some sa) ae = cs in
  let alg = (sa, Hash CoreCrypto.SHA256) in
  let ems = next.ne_extended_ms in

  // Send ServerCertificate
  let Correct chain = Cert.lookup_chain config.cert_chain_file in
  let c = {crt_chain = chain} in
  let cb = log @@ Certificate(c) in
  sendHSRecord tcp pv cb;

  // Send ServerKeyExchange
  let gn = match nego with | {Negotiation.n_dh_group = Some n} -> n in
  let gy = KeySchedule.ks_server_12_init_dh ks ch.ch_client_random pv cs ems gn in
  let kex_s = KEX_S_DHE gy in
  let sv = kex_s_to_bytes kex_s in
  let cr = ch.ch_client_random in
  let sr = sh.sh_server_random in
  let csr = cr @| sr in
  let tbs = Handshake.to_be_signed pv Server (Some csr) sv in
  let sa, ha = alg in
  let hab, sab = hashAlgBytes ha, sigAlgBytes sa in
  let a = Signature.Use (fun _ -> True) sa [ha] false false in
  let Some csk = Signature.lookup_key #a config.private_key_file in
  let sigv = Signature.sign ha csk tbs in
  let signature = (hab @| sab @| (vlbytes 2 sigv)) in
  let ske = {ske_kex_s = kex_s; ske_sig = signature} in
  //IO.print_string ("TBS = " ^ (print_bytes tbs) ^ "\n SIG = " ^ (print_bytes sigv) ^ "\n");
  let skeb = log @@ ServerKeyExchange(ske) in
  sendHSRecord tcp pv skeb;

  // Send ServerHelloDone
  let shdb = log @@ ServerHelloDone in
  sendHSRecord tcp pv shdb;

  // Get ClientKeyExchange
  let (ClientKeyExchange(cke), ckeb) = recvHSRecord tcp pv kex in
  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
  let gx =
    begin
    match cke.cke_kex_c with
    | KEX_C_ECDHE u -> u
    | _ -> failwith "Bad CKE type"
    end
  in
  IO.print_string ("Client key share:" ^ (Platform.Bytes.print_bytes gx) ^ "\n");

  // Derive keys
  let _ = log @@ ClientKeyExchange(cke) in
  KeySchedule.ks_server_12_cke_dh ks gx;
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  let wr = encryptor Server (ck @| civ) in
  let rd = decryptor Server (sk @| siv) in

  // Receive CCS and ClientFinished
  let _ = recvCCSRecord tcp pv in
  let Finished(cfin), cfinb = recvEncHSRecord Server tcp pv kex rd in
  //  let Correct svd = Handshake.processClientFinished n ks log [(Finished cfin, cfinb)] in
  let _ = log @@ Finished(cfin) in
  let lb = HandshakeLog.getBytes log in

  // Send ServerFinished
  let svd = KeySchedule.ks_server_12_server_finished ks in
  let sfin = {fin_vd = svd} in
  let sfinb = log @@ Finished(sfin) in
  let efinb = encryptRecord Server wr Content.Handshake sfinb in
  sendRecord tcp pv Content.Change_cipher_spec ccsBytes;
  sendRecord tcp pv Content.Handshake efinb;

  // Receive Client request, whatever
  let req = recvEncAppDataRecord Server tcp pv rd in

  // Send Response
  let text = "You are connected to miTLS*!\r\nThis is the request you sent:\r\n\r\n" ^ (iutf8 req) in
  let payload = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:" ^ (string_of_int (length (abytes text))) ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text in
  let payload = encryptRecord Server wr Content.Application_data (utf8 payload) in
  let _ = sendRecord tcp pv Content.Application_data payload in

  // Close connection and restart
  TCP.close tcp;
  IO.print_string "Closing connection...\n";
  server_loop config sock

let server config host port =
  IO.print_string "===============================================\n Starting test TLS 1.2 server...\n";
  let sock = TCP.listen host port in
  server_loop config sock


(*-----------------------------------------------------------------------------*)
// TLS 1.2 Client
let client config host port =
  IO.print_string "===============================================\n Starting test TLS 1.2 client...\n";
  let tcp = TCP.connect host port in
  let rid = new_region root in
  let log = HandshakeLog.create #rid in
  let ks, cr = KeySchedule.create #rid Client log in

  // Send ClientHello
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks log None None in   let pv = ch.ch_protocol_version in
  let kex = TLSConstants.Kex_ECDHE in
  sendHSRecord tcp pv chb;

  // Receive ServerHello
  let ServerHello(sh), shb = recvHSRecord tcp pv kex in
  let Correct (n,None) = Handshake.processServerHello config ks log None ch (ServerHello(sh), shb) in

  let pv = n.n_protocol_version in
  let cs = n.n_cipher_suite in
  let CipherSuite kex sa ae = cs in
  let ems = n.n_extensions.ne_extended_ms in
  let sal = n.n_extensions.ne_signature_algorithms in

  // Receive ServerCertificate, ServerKeyExchange and ServerHelloDone
  let (Certificate(sc),scb) = recvHSRecord tcp pv kex in
  let ServerKeyExchange(ske), skeb = recvHSRecord tcp pv kex in
  let ServerHelloDone, shdb = recvHSRecord tcp pv kex in
  IO.print_string ("Certificate validation status = " ^
    (if Cert.validate_chain sc.crt_chain true (Some host) config.ca_file then
      "OK" else "FAIL")^"\n");

  let tbs = kex_s_to_bytes ske.ske_kex_s in
  let sigv = ske.ske_sig in
  let cr = ch.ch_client_random in
  let sr = sh.sh_server_random in
  let (ClientKeyExchange cke,ckeb) = 
    match Handshake.processServerHelloDone config n ks log
      	    [(Certificate sc,scb);(ServerKeyExchange ske, skeb);(ServerHelloDone,shdb)] [] with
     | Correct [x] -> x 
     | Error (_,z) -> failwith (z ^ "\n") in

  // Send ClientKeyExchange
  sendHSRecord tcp pv ckeb;

  if ems then IO.print_string " ***** USING EXTENDED MASTER SECRET ***** \n";
  //IO.print_string ("master secret:"^(Platform.Bytes.print_bytes ms)^"\n");

  // Derive keys
  let (ck, civ, sk, siv) = KeySchedule.ks_12_get_keys ks in
  IO.print_string ("client AES_GCM write key:"^(Platform.Bytes.print_bytes ck)^"\n");
  IO.print_string ("client AES_GCM salt: iv:"^(Platform.Bytes.print_bytes civ)^"\n");
  IO.print_string ("server AES_GCM write key:"^(Platform.Bytes.print_bytes sk)^"\n");
  IO.print_string ("server AES_GCM salt:"^(Platform.Bytes.print_bytes siv)^"\n");
  let wr = encryptor Client (ck @| civ) in
  let rd = decryptor Client (sk @| siv) in

  // Send CCS and ClientFinished
  let Finished cfin, cfinb = Handshake.prepareClientFinished ks log in
  let efinb = encryptRecord Client wr Content.Handshake cfinb in
  sendRecord tcp pv Content.Change_cipher_spec ccsBytes;
  sendRecord tcp pv Content.Handshake efinb;

  // Receive CCS
  let _ = recvCCSRecord tcp pv in
  let Finished(sfin), sfinb = recvEncHSRecord Client tcp pv kex rd in
  let Correct svd = Handshake.processServerFinished ks log (Finished sfin, sfinb) in

  IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n";

  // Send request
  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord Client wr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data get;

  // Receive response
  let ad = recvEncAppDataRecord Client tcp pv rd in
  ()

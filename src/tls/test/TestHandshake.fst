module TestHandshake

open FStar.Seq
open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open TLSError
open TLSInfo
open TLSConstants
open TLSFormats
open HandshakeMessages
open HandshakeLog
open Negotiation


private let pre_id (role:role) =
  let cr  = createBytes 32 0z in
  let sr  = createBytes 32 0z in
  let kdf = PRF_TLS_1p2 kdf_label (HMAC CoreCrypto.SHA256) in
  let gx  = CommonDH.keygen (CommonDH.ECDH CoreCrypto.ECC_P256) in
  let g   = CommonDH.key_params gx in
  let gy, gxy = CommonDH.dh_responder gx in
  let pms = PMS.DHPMS (g, (CommonDH.share_of_key gx), (CommonDH.share_of_key gy), (PMS.ConcreteDHPMS gxy)) in
  let msid = StandardMS pms (cr @| sr) kdf in
  ID12 TLS_1p2 msid kdf (AEAD CoreCrypto.AES_128_GCM CoreCrypto.SHA256) cr sr role

private val encryptRecord : #id:StAE.stae_id -> wr:StAE.writer id -> ct:Content.contentType -> plain:bytes -> bytes
private let encryptRecord (#id:StAE.stae_id) (wr:StAE.writer id) ct plain : bytes =
  let rg: Range.frange id = (0, length plain) in
  let f: DataStream.fragment id rg = plain in
  let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

private val decryptRecord : #id:StAE.stae_id -> rd:StAE.reader id -> ct:Content.contentType -> cipher:bytes -> bytes
private let decryptRecord (#id:StAE.stae_id) (rd:StAE.reader id) ct cipher : bytes =
  let ctxt: Content.decrypted id = (ct, cipher) in
  let Some d = StAE.decrypt #id rd ctxt in
  Content.repr id d

private let sendRecordE encrypted tcp pv ct msg =
  let r = Record.makePacket ct encrypted pv msg in
  match Transport.send tcp r with
  | Error z -> failwith z
  | Correct _ -> ()
private let sendRecord = sendRecordE false

private let sendHSRecord tcp pv msg =
  sendRecord tcp pv Content.Handshake msg

private let hsbuf = ralloc #(list (hs_msg * bytes)) root []

private let recvHSRecord tcp pv kex =
  let (hs_msg, to_log) =
    match !hsbuf with
    | [] -> 
      let Correct (ct,rpv,pl) = Record.read tcp in
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

private let recvCCSRecord tcp =
  let Correct (Content.Change_cipher_spec,_,ccs) = Record.read tcp in
  IO.print_string "Received CCS\n";
  ccs

private let enc_hsbuf = ralloc #(list (hs_msg * bytes)) root []

private let recvEncHSRecord tcp pv kex rd =
  let (hs_msg, to_log) =
    match !enc_hsbuf with
    | [] ->
      let Correct(_,_,cipher) = Record.read tcp in
      let payload = decryptRecord rd Content.Handshake cipher in
      let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in
      let h :: rem = hsm in
      enc_hsbuf := rem; h
    | h::rem -> enc_hsbuf := rem; h
    in
  IO.print_string ("Received HS(" ^ (string_of_handshakeMessage hs_msg) ^ ")\n");
  let logged = handshakeMessageBytes (Some pv) hs_msg in
  IO.print_string ("Logged message = Parsed message? ");
  if (Platform.Bytes.equalBytes logged to_log) then IO.print_string "yes\n"
  else IO.print_string "no\n";
  hs_msg, to_log

private let recvEncAppDataRecord tcp pv rd =
  let Correct (Content.Application_data,_,cipher) = Record.read tcp in
  let payload = decryptRecord rd Content.Application_data cipher in
  IO.print_string ("Received Data:\n" ^ (iutf8 payload) ^ "\n");
  payload


(*-----------------------------------------------------------------------------*)
// TLS 1.2 Server
private let rec server_loop_12 config sock =
  let raw_tcp = Platform.Tcp.accept sock in
  let tcp = Transport.wrap raw_tcp in 
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
  let a = Signature.Use (fun _ -> true) sa [ha] false false in
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
  let KeySchedule.StAEInstance rd wr = KeySchedule.ks_12_get_keys ks in

  // Receive CCS and ClientFinished
  let _ = recvCCSRecord tcp in
  let Finished(cfin), cfinb = recvEncHSRecord tcp pv kex rd in
  //  let Correct svd = Handshake.processClientFinished n ks log [(Finished cfin, cfinb)] in
  let _ = log @@ Finished(cfin) in
  let lb = HandshakeLog.getBytes log in

  // Send ServerFinished
  let svd = KeySchedule.ks_server_12_server_finished ks in
  let sfin = {fin_vd = svd} in
  let sfinb = log @@ Finished(sfin) in
  let efinb = encryptRecord wr Content.Handshake sfinb in
  sendRecord tcp pv Content.Change_cipher_spec ccsBytes;
  sendRecord tcp pv Content.Handshake efinb;

  // Receive Client request, whatever
  let req = recvEncAppDataRecord tcp pv rd in

  // Send Response
  let text = "You are connected to miTLS*!\r\nThis is the request you sent:\r\n\r\n" ^ (iutf8 req) in
  let payload = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:" ^ (string_of_int (length (abytes text))) ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text in
  let payload = encryptRecord wr Content.Application_data (utf8 payload) in
  let _ = sendRecord tcp pv Content.Application_data payload in

  // Close connection and restart
  Platform.Tcp.close raw_tcp;
  IO.print_string "Closing connection...\n";
  server_loop_12 config sock

let server_12 config host port =
  IO.print_string "===============================================\n Starting test TLS 1.2 server...\n";
  let sock = Transport.listen host port in
  server_loop_12 config sock


(*-----------------------------------------------------------------------------*)
// TLS 1.2 Client
let client_12 config host port : ML unit =
  IO.print_string "===============================================\n Starting test TLS 1.2 client...\n";
  let tcp = Transport.connect host port in
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
  let KeySchedule.StAEInstance rd wr = KeySchedule.ks_12_get_keys ks in

  // Send CCS and ClientFinished
  let Finished cfin, cfinb = Handshake.prepareClientFinished ks log in
  let efinb = encryptRecord wr Content.Handshake cfinb in
  sendRecord tcp pv Content.Change_cipher_spec ccsBytes;
  sendRecord tcp pv Content.Handshake efinb;

  // Receive CCS
  let _ = recvCCSRecord tcp in
  let Finished(sfin), sfinb = recvEncHSRecord tcp pv kex rd in
  let Correct svd = Handshake.processServerFinished ks log (Finished sfin, sfinb) in

  IO.print_string ("Recd fin = expected fin? ");
  if (Platform.Bytes.equalBytes sfin.fin_vd svd) then IO.print_string "yes\n" else IO.print_string "no\n";

  // Send request
  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord wr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data get;

  // Receive response
  let ad = recvEncAppDataRecord tcp pv rd in
  ()


(*-----------------------------------------------------------------------------*)
// TLS 1.3 Client
let client_13 config host port : ML unit =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Transport.connect host port in
  let rid = new_region root in
  let lg = HandshakeLog.create #rid in
  let ks, cr = KeySchedule.create #rid Client lg in

  // This will call KS.ks_client_13_init_1rtt
  let (ClientHello ch,chb) = Handshake.prepareClientHello config ks lg None None in
  let pv = ch.ch_protocol_version in
  let kex = TLSConstants.Kex_ECDHE in
  sendHSRecord tcp pv chb;

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

  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let rc = CoreCrypto.hash h zeroes in
  let cv_log = (HandshakeLog.getHash lg h) @| rc in

  let CertificateVerify(cv),_ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ CertificateVerify(cv) in

  //let _ = IO.debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n") in
  let Some ((sa,h), sigv) = Handshake.sigHashAlg_of_ske cv.cv_sig in
  let a = Signature.Use (fun _ -> true) sa [h] false false in
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
  let cfinb = HandshakeMessages.handshakeMessageBytes (Some pv) (Finished cfin) in
  let _ = lg @@ (Finished cfin) in

  IO.print_string "before encrypt \n";
  let efinb = encryptRecord wr Content.Handshake cfinb in
  sendRecordE true tcp pv Content.Application_data efinb;

  let payload = "GET / HTTP/1.1\r\nHost: " ^ host ^ "\r\n\r\n" in
  let get = encryptRecord dwr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data get;
  let ad = recvEncAppDataRecord tcp pv drd in
  ()

private let sendEncHSRecord tcp pv msg wr =
  let hs = HandshakeMessages.handshakeMessageBytes (Some pv) msg in
  let er = encryptRecord wr Content.Handshake hs in
  sendRecordE true tcp pv Content.Application_data er

(*-----------------------------------------------------------------------------*)
// TLS 1.3 Server
private let rec server_loop_13 config sock =
  let raw_tcp = Platform.Tcp.accept sock in
  let tcp = Transport.wrap raw_tcp in 
  let rid = new_region root in
  let lg = HandshakeLog.create #rid in
  let ks, sr = KeySchedule.create #rid Server lg in

  let kex = TLSConstants.Kex_ECDHE in
  let pv = TLS_1p3 in
  let h = CoreCrypto.SHA256 in
  let sa = CoreCrypto.RSASIG in
  let cs = CipherSuite kex (Some sa) (AEAD CoreCrypto.AES_128_GCM h) in

  let ClientHello(ch), chb = recvHSRecord tcp pv kex in

  let (cr, sid, csl, ext) = (match ch with
    | {ch_protocol_version = TLS_1p3;
       ch_client_random = cr;
       ch_sessionID = sid;
       ch_cipher_suites = csl;
       ch_extensions = Some ext} -> (cr, sid, csl, ext)
    | _ -> failwith "Bad client hello (probably not 1.3)") in

  let (nego, Some keys, (ServerHello sh, shb)) =
  (match Handshake.prepareServerHello config ks lg None (ClientHello ch, chb) with
     | Correct z -> z
     | Error (x,z) -> failwith z) in

  sendHSRecord tcp pv shb;
  let KeySchedule.StAEInstance rd wr = keys in

  let Correct chain = Cert.lookup_chain config.cert_chain_file in
  let crt = {crt_chain = chain} in
  sendEncHSRecord tcp pv (EncryptedExtensions ({ee_extensions=[]})) wr;
  sendEncHSRecord tcp pv (Certificate crt) wr;

  let _ = lg @@ (EncryptedExtensions ({ee_extensions=[]})) in
  let _ = lg @@ (Certificate crt) in

  let hL = CoreCrypto.hashSize h in
  let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
  let rc = CoreCrypto.hash h zeroes in
  let cv_log = (HandshakeLog.getHash lg h) @| rc in

  let tbs = Handshake.to_be_signed pv Server None cv_log in
  let ha = Hash h in
  let hab, sab = hashAlgBytes ha, sigAlgBytes sa in
  let a = Signature.Use (fun _ -> true) sa [ha] false false in
  let Some csk = Signature.lookup_key #a config.private_key_file in
  let sigv = Signature.sign ha csk tbs in
  let signature = (hab @| sab @| (vlbytes 2 sigv)) in
  sendEncHSRecord tcp pv (CertificateVerify ({cv_sig = signature})) wr;
  let _ = lg @@ (CertificateVerify ({cv_sig = signature})) in

  let svd = KeySchedule.ks_server_13_server_finished ks in
  sendEncHSRecord tcp pv (Finished ({fin_vd = svd})) wr;
  let _ = lg @@ (Finished ({fin_vd = svd})) in
  let KeySchedule.StAEInstance drd dwr = KeySchedule.ks_server_13_sf ks in

  let cvd = KeySchedule.ks_server_13_client_finished ks in
  let Finished({fin_vd = cfin}), _ = recvEncHSRecord tcp pv kex rd in
  let _ = lg @@ (Finished ({fin_vd = cfin})) in

  (if equalBytes cfin cvd then
    IO.print_string ("Server finished OK:"^(print_bytes svd)^"\n")
  else
    failwith "Failed to verify server finished");

  let req = recvEncAppDataRecord tcp pv drd in
  let text = "You are connected to miTLS* 1.3!\r\nThis is the request you sent:\r\n\r\n" ^ (iutf8 req) in
  let payload = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:" ^ (string_of_int (length (abytes text))) ^ "\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n" ^ text in

  let res = encryptRecord dwr Content.Application_data (utf8 payload) in
  sendRecord tcp pv Content.Application_data res;

  Platform.Tcp.close raw_tcp;
  IO.print_string "Closing connection...\n";

  server_loop_13 config sock

let server_13 config host port : ML unit =
 IO.print_string "===============================================\n Starting test TLS 1.3 server...\n";
 let sock = Platform.Tcp.listen host port in
 server_loop_13 config sock

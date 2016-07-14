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
open StAE
open CoreCrypto

let encryptRecord_TLS13_AES_GCM_128_SHA256 (#id:StAE.stae_id) (wr:writer id) ct plain : bytes =
  let rg: Range.frange id = (0, length plain) |> unsafe_coerce in
  let f: (b:Range.rbytes rg{Content.fragmentRepr ct rg b}) = plain |> unsafe_coerce in let f: Content.fragment id = Content.mk_fragment id ct rg f in
  StAE.encrypt #id wr f

let decryptRecord_TLS13_AES_GCM_128_SHA256 (#id:StAE.stae_id) (rd:reader id) ct cipher : bytes =
  let Some d = StAE.decrypt #id rd (ct,cipher) in
  Content.repr id d

let sendRecord tcp pv ct msg str =
  let r = Record.makePacket ct pv msg in
  let Correct _ = Transport.send tcp r in
  IO.print_string ("Sending " ^ Content.ctToString ct ^ "Data(" ^ str ^ ")\n")

let makeHSRecord pv hs_msg =
  let hs = HandshakeMessages.handshakeMessageBytes (Some pv) hs_msg in
  (string_of_handshakeMessage hs_msg, hs)

let sendHSRecord tcp pv hs_msg = 
  let (str,hs) = makeHSRecord pv hs_msg in
  sendRecord tcp pv Content.Handshake hs str

let recvHSRecord tcp pv kex = 
  let Correct(Content.Handshake,rpv,pl) = Record.read tcp in
  match Handshake.parseHandshakeMessages (Some pv) (Some kex) pl with
  | Correct (_,[(hs_msg,to_log)]) ->
     	    (IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
	     (hs_msg, to_log))
  | Error (x,z) -> IO.print_string (z^"\n"); failwith "error"

let recvCCSRecord tcp pv = 
  let Correct(Content.Change_cipher_spec,_,ccs) = Record.read tcp in
  IO.print_string "Received CCS\n";
  ccs

let recvEncHSRecord tcp pv kex rd = 
  let Correct(Content.Application_data,_,cipher) = Record.read tcp in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Handshake cipher in
  let Correct (rem,hsm) = Handshake.parseHandshakeMessages (Some pv) (Some kex) payload in 
  let [(hs_msg,to_log)] = hsm in
  IO.print_string ("Received HS("^(string_of_handshakeMessage hs_msg)^")\n");
  hs_msg, to_log

let recvEncAppDataRecord tcp pv rd = 
  let Correct(Content.Application_data,_,cipher) = Record.read tcp in
  let payload = decryptRecord_TLS13_AES_GCM_128_SHA256 rd Content.Application_data cipher in
  IO.print_string "Received Data:\n";
  IO.print_string ((iutf8 payload)^"\n");
  payload

let main config host port =
  IO.print_string "===============================================\n Starting test TLS 1.3 client...\n";
  let tcp = Transport.connect host port in
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

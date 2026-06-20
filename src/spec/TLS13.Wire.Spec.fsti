module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module SHC = TLS13.ServerHello.Checks
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module GCE = TLS13.Wire.Generated.CertificateEntry
module GCert = TLS13.Wire.Generated.Certificate
module GCH = TLS13.Wire.Generated.ClientHello
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GHS = TLS13.Wire.Generated.Handshake
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSN = TLS13.Wire.Generated.ServerName
module GHN = TLS13.Wire.Generated.HostName
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module LP = LowParse.Spec

(**
  Wire-level M/L boundary.

  The high-level model (M) is the pure message layer from TLS13.Messages,
  TLS13.Types, TLS13.StateMachine, and TLS13.ConnectionLog.
  The low-level representation (L) for supported wire formats is the
  extraction-oriented TLS13.Impl.Messages layer plus byte-buffer streaming
  views where the active implementation is still header-first.

  Pulse parsers/serializers should be exposed through TLS13.Impl.Parser and
  TLS13.Impl.Serializer and state their correctness by referring to the parse_*
  and serialize_* functions in this module.  The older framing modules are
  implementation backends only, not the public M/L codec boundary.
**)

type parse_error = T.tls_error

val read_u16:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  GTot nat

val lemma_read_u16_definition:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  Lemma (read_u16 input pos ==
         U8.v (Seq.index input pos) * 256 +
         U8.v (Seq.index input (pos + 1)))

val read_u24:
  input:B.bytes ->
  pos:nat{pos + 3 <= B.length input} ->
  GTot nat

val lemma_read_u24_one:
  input:B.bytes{B.length input >= 4} ->
  Lemma (read_u24 input 1 == 1 <==>
         (U8.v (Seq.index input 1) == 0 /\
          U8.v (Seq.index input 2) == 0 /\
          U8.v (Seq.index input 3) == 1))

val synth_cipher_suite:
  c:GCS.cipherSuite ->
  GTot T.cipher_suite

val lemma_synth_cipher_suite:
  c:GCS.cipherSuite ->
  Lemma (synth_cipher_suite c ==
    (match c with
     | GCS.TLS_CHACHA20_POLY1305_SHA256 -> T.TLS_CHACHA20_POLY1305_SHA256
     | GCS.Unknown_cipherSuite v -> T.UnknownCipherSuite (U16.v v)))

val synth_cipher_suites:
  l:list GCS.cipherSuite ->
  GTot (list T.cipher_suite)

val lemma_synth_cipher_suites_nil:
  unit ->
  Lemma (synth_cipher_suites [] == [])

val lemma_synth_cipher_suites_cons:
  c:GCS.cipherSuite ->
  tl:list GCS.cipherSuite ->
  Lemma (synth_cipher_suites (c :: tl) ==
         synth_cipher_suite c :: synth_cipher_suites tl)

val key_exchange_to_key32:
  ke:GKSE.keyShareEntry_key_exchange ->
  GTot (option (B.bytes_of_len 32))

val lemma_key_exchange_to_key32:
  ke:GKSE.keyShareEntry_key_exchange ->
  Lemma (key_exchange_to_key32 ke ==
    (let b : B.bytes = (ke <: B.bytes) in
     if B.length b = 32 then Some (b <: B.bytes_of_len 32) else None))

val ch_find_key_share:
  l:list GKSE.keyShareEntry ->
  GTot (option (B.bytes_of_len 32))

val lemma_ch_find_key_share_nil:
  unit ->
  Lemma (ch_find_key_share [] == None)

val lemma_ch_find_key_share_cons:
  e:GKSE.keyShareEntry ->
  tl:list GKSE.keyShareEntry ->
  Lemma (ch_find_key_share (e :: tl) ==
         (if GNG.X25519? e.GKSE.group
          then (match key_exchange_to_key32 e.GKSE.key_exchange with
                | Some k -> Some k
                | None -> ch_find_key_share tl)
          else ch_find_key_share tl))

val synth_signature_scheme:
  s:GSS.signatureScheme ->
  GTot T.signature_scheme

val synth_sig_schemes:
  l:list GSS.signatureScheme ->
  GTot (list T.signature_scheme)

val lemma_synth_sig_schemes_nil:
  unit ->
  Lemma (synth_sig_schemes [] == [])

val lemma_synth_sig_schemes_cons:
  s:GSS.signatureScheme ->
  tl:list GSS.signatureScheme ->
  Lemma (synth_sig_schemes (s :: tl) ==
         synth_signature_scheme s :: synth_sig_schemes tl)

val ch_server_name:
  snl:list GSN.serverName ->
  GTot (option T.hostname)

val lemma_ch_server_name_nil:
  unit ->
  Lemma (ch_server_name [] == None)

val lemma_ch_server_name_host:
  h:GHN.hostName ->
  tl:list GSN.serverName ->
  Lemma (ch_server_name (GSN.Name_host_name h :: tl) ==
         Some ((h <: B.bytes) <: T.hostname))

val ch_extensions:
  l:list GECH.extensionClientHello ->
  server_name:option T.hostname ->
  key_share:option (B.bytes_of_len 32) ->
  saw_supported_versions:bool ->
  signature_schemes:list T.signature_scheme ->
  GTot (option (option T.hostname & option (B.bytes_of_len 32) & bool & list T.signature_scheme))

val lemma_ch_extensions_nil:
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions [] sn ks sv ss == (if sv then Some (sn, ks, sv, ss) else None))

val lemma_ch_extensions_cons_sn:
  snl:GESN.extensionClientHello_extension_data_server_name ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_server_name snl :: tl) sn ks sv ss ==
         (match ch_server_name snl with
          | Some name -> ch_extensions tl (Some name) ks sv ss
          | None -> None))

val lemma_ch_extensions_cons_sg:
  sgl:GESG.extensionClientHello_extension_data_supported_groups ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_supported_groups sgl :: tl) sn ks sv ss ==
         ch_extensions tl sn ks sv ss)

val lemma_ch_extensions_cons_sa:
  ssl:GESA.extensionClientHello_extension_data_signature_algorithms ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_signature_algorithms ssl :: tl) sn ks sv ss ==
         ch_extensions tl sn ks sv (synth_sig_schemes ssl))

val lemma_ch_extensions_cons_ks:
  kscl:GESK.extensionClientHello_extension_data_key_share ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_key_share kscl :: tl) sn ks sv ss ==
         (match ch_find_key_share kscl with
          | Some k -> ch_extensions tl sn (Some k) sv ss
          | None -> None))

val lemma_ch_extensions_cons_sv:
  svl:GESV.extensionClientHello_extension_data_supported_versions ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma (ch_extensions (GECH.Extension_data_supported_versions svl :: tl) sn ks sv ss ==
         (if FStar.List.Tot.mem GPV.TLS_1p3 svl
          then ch_extensions tl sn ks true ss
          else None))

val lemma_ch_extensions_cons_other:
  e:GECH.extensionClientHello ->
  tl:list GECH.extensionClientHello ->
  sn:option T.hostname ->
  ks:option (B.bytes_of_len 32) ->
  sv:bool ->
  ss:list T.signature_scheme ->
  Lemma
    (requires
      not (GECH.Extension_data_server_name? e) /\
      not (GECH.Extension_data_supported_groups? e) /\
      not (GECH.Extension_data_signature_algorithms? e) /\
      not (GECH.Extension_data_key_share? e) /\
      not (GECH.Extension_data_supported_versions? e))
    (ensures ch_extensions (e :: tl) sn ks sv ss ==
             ch_extensions tl sn ks sv ss)

val synth_client_hello:
  c:GCH.clientHello ->
  GTot (option M.client_hello)

val lemma_synth_client_hello:
  c:GCH.clientHello ->
  Lemma (synth_client_hello c ==
    (if not (GPV.TLS_1p2? c.GCH.legacy_version) then None
     else match ch_extensions c.GCH.extensions None None false [] with
          | Some (server_name, Some key_share, _, signature_schemes) ->
            let cipher_suites = synth_cipher_suites c.GCH.cipher_suites in
            if FStar.List.Tot.length cipher_suites <= M.client_hello_max_cipher_suites &&
               FStar.List.Tot.length signature_schemes <= M.client_hello_max_signature_schemes &&
               (match server_name with
                | Some hostname -> B.length hostname <= M.client_hello_server_name_max_len
                | None -> True)
            then Some ({ M.random = (c.GCH.random <: B.bytes_of_len 32);
                         M.server_name = server_name;
                         M.key_share = key_share;
                         M.cipher_suites = cipher_suites;
                         M.signature_schemes = signature_schemes;
                         M.body = B.empty })
            else None
          | _ -> None))

val parse_client_hello:
  input:B.bytes ->
  GTot (option M.client_hello)

val sh_key_share:
  l:list GESH.extensionServerHello ->
  saw_supported_versions:bool ->
  key_share:option (B.bytes_of_len 32) ->
  GTot (option (B.bytes_of_len 32))

val lemma_sh_key_share_nil:
  saw_supported_versions:bool ->
  key_share:option (B.bytes_of_len 32) ->
  Lemma (sh_key_share [] saw_supported_versions key_share ==
    (if saw_supported_versions then key_share else None))

val lemma_sh_key_share_cons:
  e:GESH.extensionServerHello ->
  tl:list GESH.extensionServerHello ->
  saw_supported_versions:bool ->
  key_share:option (B.bytes_of_len 32) ->
  Lemma (sh_key_share (e :: tl) saw_supported_versions key_share ==
    (match e with
     | GESH.Extension_data_supported_versions sv ->
       if GPV.TLS_1p3? sv then sh_key_share tl true key_share else None
     | GESH.Extension_data_key_share kse ->
       if GNG.X25519? kse.GKSE.group
       then (match key_exchange_to_key32 kse.GKSE.key_exchange with
             | Some k -> sh_key_share tl saw_supported_versions (Some k)
             | None -> None)
       else None
     | _ -> sh_key_share tl saw_supported_versions key_share))

val synth_server_hello:
  sh:GSH.serverHello ->
  GTot (option M.server_hello)

val parse_server_hello:
  input:B.bytes ->
  GTot (option M.server_hello)

val synth_cert_chain:
  l:list GCE.certificateEntry ->
  GTot (list B.bytes)

val cert_chain_total_bytes:
  chain:list B.bytes ->
  GTot nat

val cert_chain_fits:
  chain:list B.bytes ->
  GTot bool

val lemma_synth_cert_chain_nil:
  unit ->
  Lemma (synth_cert_chain [] == [])

val lemma_synth_cert_chain_cons:
  e:GCE.certificateEntry ->
  tl:list GCE.certificateEntry ->
  Lemma (synth_cert_chain (e :: tl) ==
         (e.GCE.cert_data <: B.bytes) :: synth_cert_chain tl)

val lemma_synth_cert_chain_length:
  l:list GCE.certificateEntry ->
  Lemma (FStar.List.Tot.length (synth_cert_chain l) ==
         FStar.List.Tot.length l)

val lemma_cert_chain_total_bytes_nil:
  unit ->
  Lemma (cert_chain_total_bytes [] == 0)

val lemma_cert_chain_total_bytes_snoc:
  chain:list B.bytes ->
  x:B.bytes ->
  Lemma (cert_chain_total_bytes (FStar.List.Tot.append chain [x]) ==
         cert_chain_total_bytes chain + B.length x)

val lemma_cert_chain_total_bytes_prefix_le:
  prefix:list B.bytes ->
  x:B.bytes ->
  rest:list B.bytes ->
  Lemma (cert_chain_total_bytes prefix + B.length x <=
         cert_chain_total_bytes (FStar.List.Tot.append prefix (x :: rest)))

val parse_certificate_msg:
  input:B.bytes ->
  GTot (option M.certificate_msg)

val alpn_first_name:
  pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation ->
  GTot (option B.bytes)

val synth_encrypted_extensions:
  l:list GEEE.extensionEncryptedExtensions ->
  GTot (option M.encrypted_extensions)

val lemma_synth_encrypted_extensions_nil:
  unit ->
  Lemma (synth_encrypted_extensions [] ==
    Some ({ M.negotiated_alpn = None; M.body = B.empty }))

val lemma_synth_encrypted_extensions_cons_non_alpn:
  e:GEEE.extensionEncryptedExtensions ->
  tl:list GEEE.extensionEncryptedExtensions ->
  Lemma
    (requires not (GEEE.Extension_data_application_layer_protocol_negotiation? e))
    (ensures synth_encrypted_extensions (e :: tl) == synth_encrypted_extensions tl)

val lemma_synth_encrypted_extensions_cons_alpn:
  pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation ->
  tl:list GEEE.extensionEncryptedExtensions ->
  Lemma (synth_encrypted_extensions
           (GEEE.Extension_data_application_layer_protocol_negotiation pnl :: tl)
         == (match alpn_first_name pnl with
             | Some name -> Some ({ M.negotiated_alpn = Some name; M.body = B.empty })
             | None -> None))

val parse_encrypted_extensions:
  input:B.bytes ->
  GTot (option M.encrypted_extensions)

val parse_certificate_verify:
  input:B.bytes ->
  GTot (option M.certificate_verify)

val parse_finished:
  input:B.bytes ->
  GTot (option M.finished)

val parse_ignored_post_handshake:
  input:B.bytes ->
  GTot (option B.bytes)

val lemma_parse_ignored_post_handshake_def:
  input:B.bytes ->
  Lemma (parse_ignored_post_handshake input ==
    (if B.length input >= 4 &&
        U8.v (Seq.index input 0) = 4 &&
        (U8.v (Seq.index input 1) * 65536 +
         U8.v (Seq.index input 2) * 256 +
         U8.v (Seq.index input 3)) + 4 = B.length input
     then Some (Seq.slice input 4 (B.length input))
     else None))

val parse_key_update:
  input:B.bytes ->
  GTot (option M.key_update_request)

val lemma_parse_key_update_def:
  input:B.bytes ->
  Lemma (parse_key_update input ==
    (if B.length input = 5 &&
        U8.v (Seq.index input 0) = 24 &&
        U8.v (Seq.index input 1) = 0 &&
        U8.v (Seq.index input 2) = 0 &&
        U8.v (Seq.index input 3) = 1
     then (match U8.v (Seq.index input 4) with
           | 0 -> Some M.UpdateNotRequested
           | 1 -> Some M.UpdateRequested
           | _ -> None)
     else None))

val synth_handshake_msg_of:
  h:GHS.handshake ->
  GTot (option M.handshake_msg)

val lemma_synth_handshake_msg_finished:
  b:GHS.handshake_body_finished ->
  Lemma (synth_handshake_msg_of (GHS.Body_finished b) ==
    Some (M.Finished ({ M.verify_data = (b <: B.bytes_of_len 32) })))

val lemma_synth_handshake_msg_certificate_verify:
  b:GHS.handshake_body_certificate_verify ->
  Lemma (synth_handshake_msg_of (GHS.Body_certificate_verify b) ==
    (if B.length (b.GCV.signature <: B.bytes) <= M.signature_max_len
     then Some (M.CertificateVerify ({
            M.scheme = synth_signature_scheme b.GCV.algorithm;
            M.signature = (b.GCV.signature <: B.bytes);
            M.body = LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify b) }))
     else None))

val lemma_synth_handshake_msg_key_update:
  b:GHS.handshake_body_key_update ->
  Lemma (synth_handshake_msg_of (GHS.Body_key_update b) == None)

val lemma_synth_handshake_msg_client_hello:
  b:GHS.handshake_body_client_hello ->
  Lemma (synth_handshake_msg_of (GHS.Body_client_hello b) ==
    (match synth_client_hello b with
     | Some ch ->
       let full = LP.serialize GHS.handshake_serializer (GHS.Body_client_hello b) in
       if B.length full <= M.client_hello_max_len
       then Some (M.ClientHello ({ ch with M.body = full }))
       else None
     | None -> None))

val lemma_synth_handshake_msg_server_hello_bad_version:
  b:GHS.handshake_body_server_hello ->
  Lemma (requires not (GPV.TLS_1p2? b.GSH.legacy_version))
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) == None)

val lemma_synth_handshake_msg_server_hello_hrr:
  b:GHS.handshake_body_server_hello ->
  shb:GSHBody.serverHelloBody ->
  Lemma (requires GPV.TLS_1p2? b.GSH.legacy_version /\
                  b.GSH.body == GSHB.HelloRetryRequest shb)
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) == Some M.HelloRetryRequest)

val lemma_synth_handshake_msg_server_hello_sh:
  b:GHS.handshake_body_server_hello ->
  sf:GSHB.serverHello_body_false ->
  Lemma (requires GPV.TLS_1p2? b.GSH.legacy_version /\
                  b.GSH.body == GSHB.ServerHello_body_false sf)
        (ensures synth_handshake_msg_of (GHS.Body_server_hello b) ==
          (if U8.v sf.GSHB.value.GSHBody.legacy_compression_method <> 0 then None
           else match sh_key_share sf.GSHB.value.GSHBody.extensions false None with
                | Some ks ->
                  if B.length (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello b))
                     <= M.server_hello_max_len
                  then (match sf.GSHB.value.GSHBody.cipher_suite with
                        | GCS.TLS_CHACHA20_POLY1305_SHA256 ->
                          Some (M.ServerHello ({
                            M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
                            M.key_share = ks;
                            M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
                            M.body = LP.serialize GHS.handshake_serializer (GHS.Body_server_hello b) }))
                        | GCS.Unknown_cipherSuite _ -> None)
                  else None
                | None -> None))

val lemma_synth_handshake_msg_encrypted_extensions:
  b:GHS.handshake_body_encrypted_extensions ->
  Lemma (synth_handshake_msg_of (GHS.Body_encrypted_extensions b) ==
    (match synth_encrypted_extensions b with
     | Some x -> Some (M.EncryptedExtensions ({ x with
         M.body = LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions b) }))
     | None -> None))

val lemma_synth_handshake_msg_certificate:
  b:GHS.handshake_body_certificate ->
  Lemma (synth_handshake_msg_of (GHS.Body_certificate b) ==
    (let chain = synth_cert_chain (b.GCert.certificate_list <: list GCE.certificateEntry) in
     if FStar.List.Tot.length chain <= M.certificate_chain_max_entries &&
        cert_chain_total_bytes chain <= M.certificate_chain_max_bytes
     then Some (M.Certificate ({ M.chain = chain;
            M.body = LP.serialize GHS.handshake_serializer (GHS.Body_certificate b) }))
     else None))

val parse_handshake:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_handshake_msg:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_supported_server_hello:
  input:B.bytes ->
  GTot (option M.server_hello)

val lemma_parse_supported_server_hello_ok:
  input:B.bytes ->
  Lemma (Some? (parse_supported_server_hello input) <==>
         SHC.server_hello_ok input)

val lemma_parse_supported_server_hello_fields:
  input:B.bytes ->
  Lemma
    (requires SHC.server_hello_ok input)
    (ensures (
      match parse_supported_server_hello input with
      | Some sh ->
        Seq.equal sh.M.random (Seq.slice input 6 38) /\
        ((SHC.server_hello_ok_52 input /\
          Seq.equal sh.M.key_share (Seq.slice input 52 84)) \/
         (SHC.server_hello_ok_58 input /\
          Seq.equal sh.M.key_share (Seq.slice input 58 90)))
      | None -> False))

val parse_certificate_leaf_der:
  input:B.bytes ->
  GTot (option B.bytes)

val serialize_client_hello:
  hello:M.client_hello ->
  GTot B.bytes

val serialize_server_hello:
  hello:M.server_hello ->
  GTot B.bytes

val serialize_encrypted_extensions:
  ee:M.encrypted_extensions ->
  GTot B.bytes

val serialize_certificate_msg:
  cert:M.certificate_msg ->
  GTot B.bytes

val serialize_certificate_verify:
  cv:M.certificate_verify ->
  GTot B.bytes

val serialize_finished:
  fin:M.finished ->
  GTot B.bytes

val serialize_supported_client_hello:
  hello:M.client_hello ->
  GTot B.bytes

val serialize_handshake:
  msg:M.handshake_msg ->
  GTot B.bytes

val serialize_handshake_msg:
  msg:M.handshake_msg ->
  GTot B.bytes

val lemma_serialize_finished_len:
  fin:M.finished ->
  Lemma (B.length (serialize_finished fin) == 32 /\
         B.length (serialize_handshake (M.Finished fin)) == 36 /\
         B.length (serialize_handshake_msg (M.Finished fin)) == 36)

val lemma_serialize_server_hello_len:
  sh:M.server_hello ->
  Lemma (B.length (serialize_handshake (M.ServerHello sh)) <= M.server_hello_max_len /\
         B.length (serialize_handshake_msg (M.ServerHello sh)) <= M.server_hello_max_len)

val serialize_server_hello_from_selection:
  sh:M.server_hello ->
  GTot B.bytes

val lemma_serialize_server_hello_from_selection_len:
  sh:M.server_hello ->
  Lemma
    (requires B.length sh.M.random == 32 /\
              B.length sh.M.key_share == 32)
    (ensures B.length (serialize_server_hello_from_selection sh) == 90)

val serialize_empty_encrypted_extensions:
  unit ->
  GTot B.bytes

val serialize_certificate_from_credential:
  cert:M.certificate_msg ->
  GTot B.bytes

val lemma_serialize_certificate_from_single_chain_len:
  certificate:B.bytes ->
  Lemma
    (B.length
      (serialize_certificate_msg { M.chain = [certificate]; M.body = B.empty }) ==
        9 + B.length certificate /\
     B.length
      (serialize_handshake (M.Certificate { M.chain = [certificate]; M.body = B.empty })) ==
        13 + B.length certificate /\
     B.length
      (serialize_certificate_from_credential { M.chain = [certificate]; M.body = B.empty }) ==
        13 + B.length certificate)

val serialize_certificate_verify_from_signature:
  cv:M.certificate_verify ->
  GTot B.bytes

val lemma_serialize_certificate_verify_from_signature_len:
  cv:M.certificate_verify ->
  Lemma
    (B.length (serialize_certificate_verify cv) == 4 + B.length cv.M.signature /\
     (B.length cv.M.body == 0 ==>
      B.length (serialize_handshake (M.CertificateVerify cv)) ==
        8 + B.length cv.M.signature) /\
     B.length (serialize_certificate_verify_from_signature cv) ==
       8 + B.length cv.M.signature)

val serialize_server_finished:
  fin:M.finished ->
  GTot B.bytes

val lemma_fixed_server_handshake_serializers:
  sh:M.server_hello ->
  cert:M.certificate_msg ->
  cv:M.certificate_verify ->
  fin:M.finished ->
  Lemma
    (requires B.length sh.M.body == 0 /\
              B.length cert.M.body == 0 /\
              B.length cv.M.body == 0)
    (ensures Seq.equal
       (serialize_server_hello_from_selection sh)
       (serialize_handshake (M.ServerHello sh)) /\
     Seq.equal
       (serialize_empty_encrypted_extensions ())
       (serialize_handshake (M.EncryptedExtensions { M.negotiated_alpn = None; M.body = B.empty })) /\
     Seq.equal
       (serialize_certificate_from_credential cert)
       (serialize_handshake (M.Certificate cert)) /\
     Seq.equal
       (serialize_certificate_verify_from_signature cv)
       (serialize_handshake (M.CertificateVerify cv)) /\
     Seq.equal
       (serialize_server_finished fin)
       (serialize_handshake (M.Finished fin)))

val serialize_server_certificate_verify_input:
  transcript_hash:B.bytes ->
  GTot B.bytes

val lemma_serialize_server_certificate_verify_input_len32:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (serialize_server_certificate_verify_input transcript_hash)
    (H.certificate_verify_input transcript_hash))

val parse_record:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

val parse_record_wire:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

val lemma_parse_record_implies_parse_record_wire:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        parse_record_wire input == Some (content_type, fragment, consumed)
      | None -> True))

val lemma_parse_record_wire_some_consumed_positive:
  input:B.bytes ->
  content_type:T.content_type ->
  fragment:M.sealed_record ->
  consumed:nat ->
  Lemma
    (requires parse_record_wire input == Some (content_type, fragment, consumed))
    (ensures consumed > 0 /\ consumed <= B.length input)

val parse_record_header:
  input:B.bytes ->
  GTot (option (T.content_type & nat))

val lemma_parse_record_header_some_iff:
  input:B.bytes{B.length input == 5} ->
  Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     (Seq.index input 2 = 0x03uy ||
      (Seq.index input 0 = 0x16uy && Seq.index input 2 = 0x01uy)) &&
     read_u16 input 3 <= 16640))

val serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot B.bytes

val lemma_parse_record_serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma
    (B.length (serialize_record content_type fragment) == 5 + B.length fragment /\
     parse_record (serialize_record content_type fragment) ==
      Some (content_type, fragment, B.length (serialize_record content_type fragment)))

val parse_plaintext:
  input:B.bytes ->
  GTot (option M.plaintext)

val serialize_plaintext:
  pt:M.plaintext ->
  GTot B.bytes

val parse_sealed_record:
  input:B.bytes ->
  GTot (option M.sealed_record)

val serialize_sealed_record:
  record:M.sealed_record ->
  GTot B.bytes

val parse_tls_message:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot (option M.tls_message)

val lemma_parse_handshake_none_of_lp_none:
  fragment:B.bytes ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures parse_handshake fragment == None)

val lemma_parse_handshake_none_of_synth_none:
  fragment:B.bytes ->
  v:GHS.handshake ->
  consumed:LP.consumed_length fragment ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              synth_handshake_msg_of v == None)
    (ensures parse_handshake fragment == None)

val lemma_ptm_handshake_fallback:
  fragment:B.bytes ->
  Lemma
    (requires parse_handshake fragment == None)
    (ensures parse_tls_message T.Handshake fragment ==
      (match parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

val serialize_tls_message:
  msg:M.tls_message ->
  GTot (T.content_type & B.bytes)

val lemma_serialize_tls_message_handshake:
  hs:M.handshake_msg ->
  Lemma (serialize_tls_message (M.TlsHandshake hs) == (T.Handshake, serialize_handshake hs))

val lemma_serialize_tls_message_application_data:
  data:B.bytes ->
  Lemma (serialize_tls_message (M.TlsApplicationData data) == (T.ApplicationData, data))

val lemma_serialize_tls_message_close_notify:
  unit ->
  Lemma (serialize_tls_message (M.TlsAlert T.CloseNotify) ==
    (T.Alert, B.of_list [2uy; 0uy]))

val lemma_serialize_tls_message_key_update_not_requested:
  unit ->
  Lemma (serialize_tls_message (M.TlsKeyUpdate M.UpdateNotRequested) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]))

val parse_tls_record:
  input:B.bytes ->
  GTot (option (M.tls_record & nat))

val serialize_tls_record:
  record:M.tls_record ->
  GTot B.bytes

val lemma_parse_record_serializes:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        consumed > 0 /\
        consumed <= B.length input /\
        consumed == B.length (serialize_record content_type fragment) /\
        Seq.equal (serialize_record content_type fragment)
                  (Seq.slice input 0 consumed)
      | None -> True))

val lemma_parse_record_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_record_wire_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record_wire input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_tls_message_round_trip:
  content_type:T.content_type ->
  fragment:B.bytes ->
  Lemma
    (ensures (
      match parse_tls_message content_type fragment with
      | Some (M.TlsHandshake (M.ClientHello ch)) ->
        Seq.equal fragment (serialize_handshake (M.ClientHello ch))
      | Some (M.TlsHandshake (M.ServerHello sh)) ->
        Seq.equal fragment (serialize_handshake (M.ServerHello sh))
      | Some (M.TlsHandshake (M.EncryptedExtensions ee)) ->
        Seq.equal fragment (serialize_handshake (M.EncryptedExtensions ee))
      | Some (M.TlsHandshake (M.Certificate c)) ->
        Seq.equal fragment (serialize_handshake (M.Certificate c))
      | Some (M.TlsHandshake (M.CertificateVerify cv)) ->
        Seq.equal fragment (serialize_handshake (M.CertificateVerify cv))
      | _ -> True))

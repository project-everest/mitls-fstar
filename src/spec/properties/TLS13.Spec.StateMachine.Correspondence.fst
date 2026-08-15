module TLS13.Spec.StateMachine.Correspondence

(**
  Auxiliary: message and key-share correspondence / pairing predicates over the
  core state machine (client/server handshake message correspondence, x25519
  key-share projections, key-schedule lineage). Builds on TLS13.Spec.StateMachine.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module K = TLS13.Keys
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module Seq = FStar.Seq
module W = TLS13.Wire.Spec

open FStar.List.Tot

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers

let lemma_client_hello_key_share_equal_from_sem
  (ch1:GCH.clientHello)
  (ch2:GCH.clientHello)
  : Lemma
      (requires
        Sem.clientHello_key_share_x25519 ch1 ==
          Sem.clientHello_key_share_x25519 ch2 /\
        (match Sem.clientHello_key_share_x25519 ch1 with
         | Some k -> B.length k == 32
         | None -> False) /\
        (match Sem.clientHello_key_share_x25519 ch2 with
         | Some k -> B.length k == 32
         | None -> False))
      (ensures client_hello_key_share ch1 == client_hello_key_share ch2)
=
  match
    Sem.clientHello_key_share_x25519 ch1,
    Sem.clientHello_key_share_x25519 ch2
  with
  | Some k1, Some k2 ->
    assert (k1 == k2)
  | _, _ ->
    assert False
let append_handshake_bytes (prefix:B.bytes) (msg:M.handshake_msg) : GTot B.bytes =
  B.append prefix (W.serialize_handshake msg)
let transcript_checkpoint_bytes
  (checkpoint:transcript_checkpoint)
  (hs:handshake_state)
  : GTot (option B.bytes) =
  match hs.hs_client_hello with
  | None -> None
  | Some ch ->
    let th_ch = W.serialize_handshake (M.ClientHello ch) in
    (match checkpoint with
     | TH_CH -> Some th_ch
     | _ ->
       match hs.hs_server_hello with
       | None -> None
       | Some sh ->
         let th_sh = append_handshake_bytes th_ch (M.ServerHello sh) in
         (match checkpoint with
          | TH_SH -> Some th_sh
          | _ ->
            match hs.hs_encrypted_extensions, hs.hs_certificate with
            | Some ee, Some cert ->
              let th_ee = append_handshake_bytes th_sh (M.EncryptedExtensions ee) in
              let th_before_cv = append_handshake_bytes th_ee (M.Certificate cert) in
              (match checkpoint with
               | TH_before_CV -> Some th_before_cv
               | _ ->
                 match hs.hs_certificate_verify with
                 | None -> None
                 | Some cv ->
                   let th_before_sf =
                     append_handshake_bytes th_before_cv (M.CertificateVerify cv) in
                   (match checkpoint with
                    | TH_before_SF -> Some th_before_sf
                    | _ ->
                      match hs.hs_server_finished with
                      | None -> None
                      | Some sf ->
                        let th_sf =
                          append_handshake_bytes th_before_sf (M.Finished sf) in
                        (match checkpoint with
                         | TH_SF -> Some th_sf
                         | TH_CF ->
                           (match hs.hs_client_finished with
                            | Some cf ->
                              Some (append_handshake_bytes th_sf (M.Finished cf))
                            | None -> None)
                         | _ -> None))
                 )
            | _, _ -> None))
let key_derivation_checkpoint_transcript
  (checkpoint:key_derivation_checkpoint)
  : option transcript_checkpoint =
  match checkpoint with
  | DeriveHandshakeTraffic -> Some TH_SH
  | DeriveApplicationTraffic -> Some TH_SF
  | DeriveTrafficUpdate _ -> None
let pending_application_consistent (app:application_state) : prop =
  app.app_pending_source_offset <= B.length app.app_pending_source_record /\
  Seq.equal app.app_pending_plaintext
    (CL.raw_slice
      app.app_pending_source_record
      app.app_pending_source_offset
      (B.length app.app_pending_source_record))
let conn_event_is_key_update (ev:conn_event) : bool =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsKeyUpdate _ -> true
     | _ -> false)
  | ConnProtectedHandshake _ ->
    false
  | ConnLocalEvent _ ->
    false
let rec conn_events_no_key_update (events:list conn_event) : bool =
  match events with
  | [] -> true
  | ev :: rest ->
    not (conn_event_is_key_update ev) && conn_events_no_key_update rest
let connection_state_no_key_update_trace (st:connection_state) : prop =
  conn_events_no_key_update st.cs_event_log == true
let same_transcript_checkpoint
  (checkpoint:transcript_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : GTot prop =
  match
    transcript_checkpoint_bytes checkpoint client.cs_model.model_handshake,
    transcript_checkpoint_bytes checkpoint server.cs_model.model_handshake
  with
  | Some client_bytes, Some server_bytes -> Seq.equal client_bytes server_bytes
  | _, _ -> False
let same_key_derivation_checkpoint
  (checkpoint:key_derivation_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : GTot prop =
  match key_derivation_checkpoint_transcript checkpoint with
  | Some transcript_checkpoint ->
    same_transcript_checkpoint transcript_checkpoint client server
  | None -> False
let key_checkpoint_for_epoch (epoch:traffic_epoch) : key_derivation_checkpoint =
  match epoch with
  | TrafficHandshake -> DeriveHandshakeTraffic
  | TrafficApplication -> DeriveApplicationTraffic
let paired_wire_logs
  (client:connection_state)
  (server:connection_state)
  : prop =
  Seq.equal client.cs_wire_log.CL.raw_sent server.cs_wire_log.CL.raw_received /\
  Seq.equal server.cs_wire_log.CL.raw_sent client.cs_wire_log.CL.raw_received
let paired_handshake_events
  (client:connection_state)
  (server:connection_state)
  : prop =
  same_transcript_checkpoint TH_CH client server /\
  same_transcript_checkpoint TH_SH client server /\
  same_transcript_checkpoint TH_before_CV client server /\
  same_transcript_checkpoint TH_before_SF client server /\
  same_transcript_checkpoint TH_SF client server /\
  same_transcript_checkpoint TH_CF client server
let paired_key_derivation_checkpoints
  (client:connection_state)
  (server:connection_state)
  : prop =
  same_key_derivation_checkpoint DeriveHandshakeTraffic client server /\
  same_key_derivation_checkpoint DeriveApplicationTraffic client server
let shared_secret_material_agrees
  (client:connection_state)
  (server:connection_state)
  : prop =
  match
    client.cs_model.model_handshake.hs_keys.ks_shared_secret,
    server.cs_model.model_handshake.hs_keys.ks_shared_secret
  with
  | Some client_shared, Some server_shared ->
    Seq.equal client_shared server_shared
  | _, _ -> False
let supported_profile_key_schedule_lineage
  (keys:key_schedule_state)
  : prop =
  match
    keys.ks_shared_secret,
    keys.ks_early_secret,
    keys.ks_handshake_secret,
    keys.ks_master_secret
  with
  | Some shared, Some early, Some handshake, Some master ->
    Seq.equal early (K.early_secret B.empty) /\
    Seq.equal handshake (K.handshake_secret early shared) /\
    Seq.equal master (K.master_secret handshake)
  | _, _, _, _ -> False
let connection_supported_profile_key_schedule_lineage
  (st:connection_state)
  : prop =
  supported_profile_key_schedule_lineage st.cs_model.model_handshake.hs_keys
let paired_x25519_key_shares
  (client:connection_state)
  (server:connection_state)
  : prop =
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_start,
    client_hs.hs_server_hello,
    server_hs.hs_server_selection,
    server_hs.hs_client_hello
  with
  | Some start, Some (sh:GSH.serverHello), Some selection, Some (ch:GCH.clientHello) ->
    (match
      start.start_client_key_share_private,
      selection.server_key_share_private,
      client_hs.hs_keys.ks_shared_secret,
      server_hs.hs_keys.ks_shared_secret
     with
     | Some client_sk, Some server_sk, Some client_shared, Some server_shared ->
       (match client_hello_key_share ch, server_hello_key_share sh with
        | Some ch_ks, Some sh_ks ->
          ch_ks == start.start_client_key_share_public /\
          sh_ks == selection.server_key_share_public /\
          C.x25519_public_from_private client_sk == start.start_client_key_share_public /\
          C.x25519_public_from_private server_sk == selection.server_key_share_public /\
          C.x25519_shared client_sk sh_ks == Some client_shared /\
          C.x25519_shared server_sk ch_ks == Some server_shared /\
          // The two endpoints negotiated the same AEAD algorithm.  Both read it
          // off their own stored ServerHello; the server's is the message it
          // sent and the client's is the message it received, so this holds for
          // any pair of genuinely peered endpoints.
          negotiated_aead_alg client_hs == negotiated_aead_alg server_hs
        | _, _ -> False)
     | _, _, _, _ -> False)
  | _, _, _, _ -> False
let client_x25519_key_share_projection
  (client:connection_state)
  : prop =
  let hs = client.cs_model.model_handshake in
  match
    hs.hs_start,
    hs.hs_client_hello,
    hs.hs_server_hello,
    hs.hs_keys.ks_shared_secret
  with
  | Some start, Some ch, Some sh, Some shared ->
    (match server_hello_kex sh with
     | Some (| g, sh_ks |) ->
      (match start_kex_private start g with
       | Some client_sk ->
        (match client_hello_kex ch g with
         | Some ch_ks ->
          ch_ks == start_kex_public start g /\
          C.kex_public_from_private g client_sk == start_kex_public start g /\
          C.kex_shared g client_sk sh_ks == Some shared
         | None -> False)
       | None -> False)
     | None ->
      False)
  | _, _, _, _ ->
    False
let client_x25519_pre_shared_secret_projection
  (client:connection_state)
  : prop =
  let hs = client.cs_model.model_handshake in
  match hs.hs_start, hs.hs_client_hello with
  | Some start, Some ch ->
    (forall (g:C.kex_group).
      client_hello_kex ch g == Some (start_kex_public start g) /\
      (match start_kex_private start g with
       | Some client_sk ->
         C.kex_public_from_private g client_sk == start_kex_public start g
       | None ->
         True))
  | _, _ ->
    False
let client_x25519_key_share_projection_stable_control
  (control:connection_control_state)
  : prop =
  match control with
  | ControlHandshaking HsServerHelloReceived
  | ControlHandshaking HsEncryptedExtensionsReceived
  | ControlHandshaking HsCertificateReceived
  | ControlHandshaking HsCertificateValidated
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived
  | ControlHandshaking HsServerFinishedVerified
  | ControlHandshaking HsClientFinishedSent
  | ControlApplicationData
  | ControlClosing
  | ControlClosed
  | ControlFailed _ ->
    True
  | _ ->
    False
let stable_client_x25519_key_share_projection
  (client:connection_state)
  : prop =
  client_x25519_key_share_projection client /\
  client_x25519_key_share_projection_stable_control
    client.cs_model.model_control
let server_x25519_key_share_projection
  (server:connection_state)
  : prop =
  let hs = server.cs_model.model_handshake in
  match
    hs.hs_server_selection,
    hs.hs_client_hello,
    hs.hs_server_hello,
    hs.hs_keys.ks_shared_secret
  with
  | Some selection, Some ch, Some sh, Some shared ->
    (match selection.server_key_share_private with
     | Some server_sk ->
      (match server_hello_key_share sh, client_hello_key_share ch with
       | Some sh_ks, Some ch_ks ->
        sh_ks == selection.server_key_share_public /\
        C.x25519_public_from_private server_sk ==
          selection.server_key_share_public /\
        (* The selection agrees with itself on every group it carries a keypair
           for.  The X25519 conjunct just above is what the ServerHello and the
           ECDH are stated over today; this one is what survives when a second
           group is added. *)
        server_selection_key_share_consistent selection /\
        C.x25519_shared server_sk ch_ks == Some shared
       | _, _ -> False)
     | None ->
      False)
  | _, _, _, _ ->
    False
let server_x25519_pre_server_hello_projection
  (server:connection_state)
  : prop =
  let hs = server.cs_model.model_handshake in
  match
    hs.hs_server_selection,
    hs.hs_client_hello,
    hs.hs_keys.ks_shared_secret
  with
  | Some selection, Some ch, Some shared ->
    (match selection.server_key_share_private with
     | Some server_sk ->
       (match client_hello_key_share ch with
        | Some ch_ks ->
          selection.server_selected_client_hello == ch /\
          C.x25519_public_from_private server_sk ==
            selection.server_key_share_public /\
          server_selection_key_share_consistent selection /\
          C.x25519_shared server_sk ch_ks == Some shared
        | None -> False)
     | None ->
       False)
  | _, _, _ ->
    False
let server_x25519_key_share_projection_stable_control
  (control:connection_control_state)
  : prop =
  match control with
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent
  | ControlHandshaking HsServerFinishedSent
  | ControlHandshaking HsClientFinishedReceived
  | ControlHandshaking HsClientFinishedVerified
  | ControlApplicationData
  | ControlClosing
  | ControlClosed
  | ControlFailed _ ->
    True
  | _ ->
    False
let stable_server_x25519_key_share_projection
  (server:connection_state)
  : prop =
  server_x25519_key_share_projection server /\
  server_x25519_key_share_projection_stable_control
    server.cs_model.model_control
let client_hello_corresponds
  (left:GCH.clientHello)
  (right:GCH.clientHello)
  : prop =
  Sem.clientHello_random left == Sem.clientHello_random right /\
  Sem.clientHello_server_name left == Sem.clientHello_server_name right /\
  Sem.clientHello_key_share_x25519 left == Sem.clientHello_key_share_x25519 right /\
  Sem.clientHello_cipher_suites left == Sem.clientHello_cipher_suites right /\
  Sem.clientHello_sig_algs left == Sem.clientHello_sig_algs right
let server_hello_corresponds
  (left:GSH.serverHello)
  (right:GSH.serverHello)
  : prop =
  Sem.serverHello_random left == Sem.serverHello_random right /\
  Sem.serverHello_key_share_x25519 left == Sem.serverHello_key_share_x25519 right /\
  Sem.serverHello_cipher_suite left == Sem.serverHello_cipher_suite right
let encrypted_extensions_corresponds
  (left:GEE.encryptedExtensions)
  (right:GEE.encryptedExtensions)
  : prop =
  Sem.encryptedExtensions_alpn left == Sem.encryptedExtensions_alpn right
let certificate_msg_corresponds
  (left:GCert.certificate)
  (right:GCert.certificate)
  : prop =
  Sem.certificate_entries left == Sem.certificate_entries right
let certificate_verify_corresponds
  (left:GCV.certificateVerify)
  (right:GCV.certificateVerify)
  : prop =
  Sem.certificateVerify_scheme left == Sem.certificateVerify_scheme right /\
  Sem.certificateVerify_signature_bytes left == Sem.certificateVerify_signature_bytes right
let handshake_msg_corresponds
  (left:M.handshake_msg)
  (right:M.handshake_msg)
  : prop =
  match left, right with
  | M.ClientHello l, M.ClientHello r ->
    client_hello_corresponds l r
  | M.ServerHello l, M.ServerHello r ->
    server_hello_corresponds l r
  | M.EncryptedExtensions l, M.EncryptedExtensions r ->
    encrypted_extensions_corresponds l r
  | M.Certificate l, M.Certificate r ->
    certificate_msg_corresponds l r
  | M.CertificateVerify l, M.CertificateVerify r ->
    certificate_verify_corresponds l r
  | M.Finished l, M.Finished r ->
    l == r
  | M.HelloRetryRequest, M.HelloRetryRequest ->
    True
  | _, _ ->
    False
let lemma_handshake_msg_corresponds_sym
  (left:M.handshake_msg)
  (right:M.handshake_msg)
  : Lemma
      (requires handshake_msg_corresponds left right)
      (ensures handshake_msg_corresponds right left)
=
  match left, right with
  | M.ClientHello l, M.ClientHello r -> ()
  | M.ServerHello l, M.ServerHello r -> ()
  | M.EncryptedExtensions l, M.EncryptedExtensions r -> ()
  | M.Certificate l, M.Certificate r -> ()
  | M.CertificateVerify l, M.CertificateVerify r -> ()
  | M.Finished l, M.Finished r -> ()
  | M.HelloRetryRequest, M.HelloRetryRequest -> ()
  | _, _ -> assert False
let tls_message_corresponds
  (left:M.tls_message)
  (right:M.tls_message)
  : prop =
  match left, right with
  | M.TlsHandshake l, M.TlsHandshake r ->
    handshake_msg_corresponds l r
  | M.TlsApplicationData l, M.TlsApplicationData r ->
    l == r
  | M.TlsAlert l, M.TlsAlert r ->
    l == r
  | M.TlsChangeCipherSpec, M.TlsChangeCipherSpec ->
    True
  | M.TlsKeyUpdate l, M.TlsKeyUpdate r ->
    l == r
  | M.TlsIgnoredPostHandshake l, M.TlsIgnoredPostHandshake r ->
    l == r
  | _, _ ->
    False
let lemma_tls_message_corresponds_handshake
  (left:M.handshake_msg)
  (right:M.handshake_msg)
  : Lemma
      (requires tls_message_corresponds (M.TlsHandshake left) (M.TlsHandshake right))
      (ensures handshake_msg_corresponds left right)
=
  ()
let rec tls_messages_correspond
  (left:list M.tls_message)
  (right:list M.tls_message)
  : Tot prop (decreases left) =
  match left, right with
  | [], [] ->
    True
  | l :: left_tail, r :: right_tail ->
    tls_message_corresponds l r /\
    tls_messages_correspond left_tail right_tail
  | _, _ ->
    False
let lemma_tls_messages_correspond_cons
  (left_head:M.tls_message)
  (left_tail:list M.tls_message)
  (right_head:M.tls_message)
  (right_tail:list M.tls_message)
  : Lemma
      (requires tls_messages_correspond (left_head :: left_tail) (right_head :: right_tail))
      (ensures
        tls_message_corresponds left_head right_head /\
        tls_messages_correspond left_tail right_tail)
=
  ()
let lemma_tls_messages_correspond_two_handshakes
  (left0:M.handshake_msg)
  (left1:M.handshake_msg)
  (right0:M.handshake_msg)
  (right1:M.handshake_msg)
  : Lemma
      (requires
        tls_messages_correspond
          [M.TlsHandshake left0; M.TlsHandshake left1]
          [M.TlsHandshake right0; M.TlsHandshake right1])
      (ensures
        handshake_msg_corresponds left0 right0 /\
        handshake_msg_corresponds left1 right1)
=
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left0)
    [M.TlsHandshake left1]
    (M.TlsHandshake right0)
    [M.TlsHandshake right1];
  lemma_tls_message_corresponds_handshake left0 right0;
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left1)
    []
    (M.TlsHandshake right1)
    [];
  lemma_tls_message_corresponds_handshake left1 right1
let lemma_tls_messages_correspond_five_handshakes
  (left0:M.handshake_msg)
  (left1:M.handshake_msg)
  (left2:M.handshake_msg)
  (left3:M.handshake_msg)
  (left4:M.handshake_msg)
  (right0:M.handshake_msg)
  (right1:M.handshake_msg)
  (right2:M.handshake_msg)
  (right3:M.handshake_msg)
  (right4:M.handshake_msg)
  : Lemma
      (requires
        tls_messages_correspond
          [
            M.TlsHandshake left0;
            M.TlsHandshake left1;
            M.TlsHandshake left2;
            M.TlsHandshake left3;
            M.TlsHandshake left4
          ]
          [
            M.TlsHandshake right0;
            M.TlsHandshake right1;
            M.TlsHandshake right2;
            M.TlsHandshake right3;
            M.TlsHandshake right4
          ])
      (ensures
        handshake_msg_corresponds left0 right0 /\
        handshake_msg_corresponds left1 right1 /\
        handshake_msg_corresponds left2 right2 /\
        handshake_msg_corresponds left3 right3 /\
        handshake_msg_corresponds left4 right4)
=
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left0)
    [
      M.TlsHandshake left1;
      M.TlsHandshake left2;
      M.TlsHandshake left3;
      M.TlsHandshake left4
    ]
    (M.TlsHandshake right0)
    [
      M.TlsHandshake right1;
      M.TlsHandshake right2;
      M.TlsHandshake right3;
      M.TlsHandshake right4
    ];
  lemma_tls_message_corresponds_handshake left0 right0;
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left1)
    [
      M.TlsHandshake left2;
      M.TlsHandshake left3;
      M.TlsHandshake left4
    ]
    (M.TlsHandshake right1)
    [
      M.TlsHandshake right2;
      M.TlsHandshake right3;
      M.TlsHandshake right4
    ];
  lemma_tls_message_corresponds_handshake left1 right1;
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left2)
    [
      M.TlsHandshake left3;
      M.TlsHandshake left4
    ]
    (M.TlsHandshake right2)
    [
      M.TlsHandshake right3;
      M.TlsHandshake right4
    ];
  lemma_tls_message_corresponds_handshake left2 right2;
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left3)
    [M.TlsHandshake left4]
    (M.TlsHandshake right3)
    [M.TlsHandshake right4];
  lemma_tls_message_corresponds_handshake left3 right3;
  lemma_tls_messages_correspond_cons
    (M.TlsHandshake left4)
    []
    (M.TlsHandshake right4)
    [];
  lemma_tls_message_corresponds_handshake left4 right4
let paired_cleartext_hello_messages
  (client:connection_state)
  (server:connection_state)
  : prop =
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_client_hello,
    server_hs.hs_client_hello,
    client_hs.hs_server_hello,
    server_hs.hs_server_hello
  with
  | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
    handshake_msg_corresponds
      (M.ClientHello client_ch)
      (M.ClientHello server_ch) /\
    handshake_msg_corresponds
      (M.ServerHello client_sh)
      (M.ServerHello server_sh)
  | _, _, _, _ ->
    False
let paired_handshake_message_correspondence
  (client:connection_state)
  (server:connection_state)
  : prop =
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_client_hello,
    server_hs.hs_client_hello,
    client_hs.hs_server_hello,
    server_hs.hs_server_hello,
    client_hs.hs_encrypted_extensions,
    server_hs.hs_encrypted_extensions,
    client_hs.hs_certificate,
    server_hs.hs_certificate,
    client_hs.hs_certificate_verify,
    server_hs.hs_certificate_verify,
    client_hs.hs_server_finished,
    server_hs.hs_server_finished,
    client_hs.hs_client_finished,
    server_hs.hs_client_finished
  with
  | Some client_ch, Some server_ch,
    Some client_sh, Some server_sh,
    Some client_ee, Some server_ee,
    Some client_cert, Some server_cert,
    Some client_cv, Some server_cv,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    handshake_msg_corresponds
      (M.ClientHello client_ch)
      (M.ClientHello server_ch) /\
    handshake_msg_corresponds
      (M.ServerHello client_sh)
      (M.ServerHello server_sh) /\
    handshake_msg_corresponds
      (M.EncryptedExtensions client_ee)
      (M.EncryptedExtensions server_ee) /\
    handshake_msg_corresponds
      (M.Certificate client_cert)
      (M.Certificate server_cert) /\
    handshake_msg_corresponds
      (M.CertificateVerify client_cv)
      (M.CertificateVerify server_cv) /\
    handshake_msg_corresponds
      (M.Finished client_sf)
      (M.Finished server_sf) /\
    handshake_msg_corresponds
      (M.Finished client_cf)
      (M.Finished server_cf)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ ->
    False
let paired_handshake_message_states
  (client:connection_state)
  (server:connection_state)
  : prop =
  paired_handshake_message_correspondence client server
let derivation_checkpoint_inputs_agree
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match key_id with
  | BaseSecret _ -> True
  | TrafficSecret traffic_id
  | TrafficKey traffic_id
  | TrafficIV traffic_id ->
    same_key_derivation_checkpoint
      (key_checkpoint_for_epoch traffic_id.traffic_id_epoch)
      client
      server
  | FinishedKey _ ->
    same_key_derivation_checkpoint DeriveHandshakeTraffic client server
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    False

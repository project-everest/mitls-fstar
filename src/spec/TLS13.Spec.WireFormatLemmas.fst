module TLS13.Spec.WireFormatLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WR = TLS13.Wire.Spec.Reveal
module WRCP = TLS13.Wire.Spec.Reveal.ClientHello.Parseback
module ID = FStar.IndefiniteDescription
module RTC = FStar.ReflexiveTransitiveClosure

let lemma_seq_equal_sym (#a:Type) (x y:Seq.seq a)
  : Lemma
      (requires Seq.equal x y)
      (ensures Seq.equal y x)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_refl y x

let lemma_seq_equal_trans (#a:Type) (x y z:Seq.seq a)
  : Lemma
      (requires Seq.equal x y /\ Seq.equal y z)
      (ensures Seq.equal x z)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_elim y z;
  Seq.lemma_eq_refl x z

(* ------------------------------------------------------------------------- *)
(* #1  record-wire round trip                                                *)
(* ------------------------------------------------------------------------- *)

let lemma_parse_record_wire_serialize_record
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (ensures
        W.parse_record_wire (W.serialize_record content_type fragment) ==
          Some
            (content_type,
             fragment,
             B.length (W.serialize_record content_type fragment)))
=
  W.lemma_parse_record_serialize_record content_type fragment;
  W.lemma_parse_record_implies_parse_record_wire
    (W.serialize_record content_type fragment)

(* ------------------------------------------------------------------------- *)
(* #2  client-hello round trip (delegated to the reveal layer)               *)
(* ------------------------------------------------------------------------- *)

let lemma_parse_client_hello_serialize_client_hello
  (ch:M.client_hello)
  : Lemma
      (requires exact_client_hello_wire_parseback_profile ch)
      (ensures W.parse_client_hello (W.serialize_client_hello ch) == Some ch)
=
  WRCP.lemma_parse_client_hello_serialize_client_hello ch

let lemma_serialize_tls_message_client_hello (ch:M.client_hello)
  : Lemma
      (W.serialize_tls_message (M.TlsHandshake (M.ClientHello ch)) ==
       (T.Handshake, W.serialize_handshake (M.ClientHello ch)))
=
  W.lemma_serialize_tls_message_handshake (M.ClientHello ch)

(* ------------------------------------------------------------------------- *)
(* #8 / #9  relate a sent canonical ClientHello to the same received record.  *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 10"
let lemma_serialize_handshake_client_hello_record_bound
  (ch:M.client_hello)
  : Lemma
      (requires supported_client_hello_wire_profile ch)
      (ensures B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640)
=
  let hostname : (h:B.bytes{B.length h <= 255}) =
    match ch.M.server_name with
    | Some h -> h
    | None -> B.empty in
  let extensions = WR.client_hello_extensions_bytes hostname ch.M.key_share in
  WR.lemma_client_hello_extensions_len hostname ch.M.key_share;
  WR.lemma_client_hello_prefix_bytes_reveal
    (43 + B.length extensions)
    (B.length extensions)
    ch.M.random;
  WR.lemma_client_hello_handshake_bytes_prefix
    ch.M.random
    hostname
    ch.M.key_share;
  WR.lemma_client_hello_handshake_bytes_reveal ch;
  let prefix =
    WR.client_hello_prefix_bytes
      (43 + B.length extensions)
      (B.length extensions)
      ch.M.random in
  let p1 = B.of_list [
    1uy;
    WR.client_hello_byte ((43 + B.length extensions) / 65536);
    WR.client_hello_byte ((43 + B.length extensions) / 256);
    WR.client_hello_byte (43 + B.length extensions);
    0x03uy; 0x03uy] in
  let p2 = B.of_list [
    0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
    WR.client_hello_byte (B.length extensions / 256);
    WR.client_hello_byte (B.length extensions)] in
  assert_norm (B.length p1 == 6);
  assert_norm (B.length p2 == 9);
  Seq.lemma_len_append ch.M.random p2;
  Seq.lemma_len_append p1 (B.append ch.M.random p2);
  Seq.lemma_eq_elim prefix (B.append p1 (B.append ch.M.random p2));
  assert (B.length prefix == 47);
  Seq.lemma_len_append prefix extensions;
  assert (B.length extensions <= 329);
  assert (B.length (WR.client_hello_handshake_bytes ch.M.random hostname ch.M.key_share) <= 376);
  assert (B.length (W.serialize_handshake (M.ClientHello ch)) <= 376)
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_serialize_handshake_client_hello_empty_sni_eq_none
  (ch:M.client_hello)
  (hostname:B.bytes{ch.M.server_name == Some hostname /\ B.length hostname == 0})
  : Lemma
      (requires supported_client_hello_wire_profile ch)
      (ensures
        Seq.equal
          (W.serialize_handshake (M.ClientHello ch))
          (W.serialize_handshake (M.ClientHello ({ ch with M.server_name = None }))))
=
  let ch_none = { ch with M.server_name = None } in
  assert (B.length hostname == B.length B.empty);
  assert (forall (i:nat{i < B.length hostname}).
    Seq.index hostname i == Seq.index B.empty i);
  Seq.lemma_eq_intro hostname B.empty;
  Seq.lemma_eq_elim hostname B.empty;
  WR.lemma_client_hello_handshake_bytes_reveal ch;
  WR.lemma_client_hello_handshake_bytes_reveal ch_none;
  assert ((match ch.M.server_name with | Some h -> h | None -> B.empty) == B.empty);
  assert ((match ch_none.M.server_name with | Some h -> h | None -> B.empty) == B.empty);
  assert (Seq.equal
    (W.serialize_handshake (M.ClientHello ch))
    (WR.client_hello_handshake_bytes ch.M.random B.empty ch.M.key_share));
  assert (Seq.equal
    (W.serialize_handshake (M.ClientHello ch_none))
    (WR.client_hello_handshake_bytes ch.M.random B.empty ch.M.key_share));
  Seq.lemma_eq_elim
    (W.serialize_handshake (M.ClientHello ch))
    (WR.client_hello_handshake_bytes ch.M.random B.empty ch.M.key_share);
  Seq.lemma_eq_elim
    (W.serialize_handshake (M.ClientHello ch_none))
    (WR.client_hello_handshake_bytes ch.M.random B.empty ch.M.key_share);
  Seq.lemma_eq_refl
    (WR.client_hello_handshake_bytes ch.M.random B.empty ch.M.key_share)
    (W.serialize_handshake (M.ClientHello ch_none))
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_client_hello_received_body_from_sent_cleartext_and_received_parse
  (sent_ch:M.client_hello)
  (received_ch:M.client_hello)
  (sent_raw:B.bytes)
  (received_raw:B.bytes)
  : Lemma
      (requires
        exact_client_hello_wire_parseback_profile sent_ch /\
        Seq.equal sent_raw received_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello sent_ch))
          sent_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello received_ch))
          received_raw)
      (ensures
        Seq.equal sent_ch.M.random received_ch.M.random /\
        sent_ch.M.server_name == received_ch.M.server_name /\
        Seq.equal sent_ch.M.key_share received_ch.M.key_share /\
        sent_ch.M.cipher_suites == received_ch.M.cipher_suites /\
        sent_ch.M.signature_schemes == received_ch.M.signature_schemes /\
        received_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch))
=
  let sent_fragment = W.serialize_handshake (M.ClientHello sent_ch) in
  let sent_record = W.serialize_record T.Handshake sent_fragment in
  let sent_msg = M.TlsHandshake (M.ClientHello sent_ch) in
  lemma_serialize_handshake_client_hello_record_bound sent_ch;
  WR.lemma_serialize_tls_message_handshake (M.ClientHello sent_ch);
  assert (CS.serialized_cleartext_tls_message sent_msg == sent_record);
  assert (Seq.equal sent_raw (CS.serialized_cleartext_tls_message sent_msg));
  assert (Seq.equal sent_raw sent_record);
  Seq.lemma_eq_elim sent_raw sent_record;
  Seq.lemma_eq_elim received_raw sent_record;
  lemma_parse_record_wire_serialize_record T.Handshake sent_fragment;
  WRCP.lemma_parse_tls_message_serialize_client_hello sent_ch;
  eliminate exists (parsed_ch:M.client_hello).
    W.parse_tls_message T.Handshake sent_fragment ==
     Some (M.TlsHandshake (M.ClientHello parsed_ch)) /\
    Seq.equal sent_ch.M.random parsed_ch.M.random /\
    sent_ch.M.server_name == parsed_ch.M.server_name /\
    Seq.equal sent_ch.M.key_share parsed_ch.M.key_share /\
    sent_ch.M.cipher_suites == parsed_ch.M.cipher_suites /\
    sent_ch.M.signature_schemes == parsed_ch.M.signature_schemes /\
    parsed_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch)
  returns
    Seq.equal sent_ch.M.random received_ch.M.random /\
    sent_ch.M.server_name == received_ch.M.server_name /\
    Seq.equal sent_ch.M.key_share received_ch.M.key_share /\
    sent_ch.M.cipher_suites == received_ch.M.cipher_suites /\
    sent_ch.M.signature_schemes == received_ch.M.signature_schemes /\
    received_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch)
  with _.
  ( eliminate exists (fragment:B.bytes).
      W.parse_record_wire sent_record == Some (T.Handshake, fragment, B.length sent_record) /\
      W.parse_tls_message T.Handshake fragment ==
        Some (M.TlsHandshake (M.ClientHello received_ch))
    returns
      Seq.equal sent_ch.M.random received_ch.M.random /\
      sent_ch.M.server_name == received_ch.M.server_name /\
      Seq.equal sent_ch.M.key_share received_ch.M.key_share /\
      sent_ch.M.cipher_suites == received_ch.M.cipher_suites /\
      sent_ch.M.signature_schemes == received_ch.M.signature_schemes /\
      received_ch.M.body == W.serialize_handshake (M.ClientHello sent_ch)
    with _.
    ( assert (fragment == sent_fragment);
      assert (W.parse_tls_message T.Handshake sent_fragment ==
        Some (M.TlsHandshake (M.ClientHello received_ch)));
      assert (Some (M.TlsHandshake (M.ClientHello parsed_ch)) ==
        Some (M.TlsHandshake (M.ClientHello received_ch)));
      assert (received_ch == parsed_ch);
      Seq.lemma_eq_refl sent_ch.M.random received_ch.M.random;
      Seq.lemma_eq_refl sent_ch.M.key_share received_ch.M.key_share ) )

let lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
  (sent_ch:M.client_hello)
  (received_ch:M.client_hello)
  (sent_raw:B.bytes)
  (received_raw:B.bytes)
  : Lemma
      (requires
        supported_client_hello_wire_profile sent_ch /\
        Seq.equal sent_raw received_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello sent_ch))
          sent_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello received_ch))
          received_raw)
      (ensures client_hello_wire_equivalent sent_ch received_ch)
=
  match sent_ch.M.server_name with
  | None ->
    lemma_client_hello_received_body_from_sent_cleartext_and_received_parse
      sent_ch received_ch sent_raw received_raw
  | Some hostname ->
    if B.length hostname = 0 then
      let sent_none = { sent_ch with M.server_name = None } in
      Seq.lemma_eq_intro hostname B.empty;
      Seq.lemma_eq_elim hostname B.empty;
      lemma_serialize_handshake_client_hello_empty_sni_eq_none sent_ch hostname;
      Seq.lemma_eq_elim
        (W.serialize_handshake (M.ClientHello sent_ch))
        (W.serialize_handshake (M.ClientHello sent_none));
      assert (Seq.equal
        sent_raw
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ClientHello sent_ch))));
      WR.lemma_serialize_tls_message_handshake (M.ClientHello sent_ch);
      WR.lemma_serialize_tls_message_handshake (M.ClientHello sent_none);
      lemma_serialize_tls_message_client_hello sent_ch;
      lemma_serialize_tls_message_client_hello sent_none;
      assert (CS.serialized_cleartext_tls_message
                (M.TlsHandshake (M.ClientHello sent_ch)) ==
              CS.serialized_cleartext_tls_message
                (M.TlsHandshake (M.ClientHello sent_none)));
      assert (Seq.equal
        sent_raw
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ClientHello sent_none))));
      assert (CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello sent_none))
        sent_raw);
      lemma_client_hello_received_body_from_sent_cleartext_and_received_parse
        sent_none received_ch sent_raw received_raw;
      assert (received_ch.M.server_name == sent_none.M.server_name);
      assert (sent_ch.M.server_name == Some B.empty);
      assert (received_ch.M.server_name == None);
      assert (client_hello_server_name_wire_equivalent sent_ch received_ch)
    else
      lemma_client_hello_received_body_from_sent_cleartext_and_received_parse
        sent_ch received_ch sent_raw received_raw
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_server_hello_wire_equivalent_from_sent_cleartext_and_received_cleartext
  (sent_sh:M.server_hello)
  (received_sh:M.server_hello)
  (sent_raw:B.bytes)
  (received_raw:B.bytes)
  : Lemma
      (requires
        Seq.equal sent_raw received_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sent_sh))
          sent_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello received_sh))
          received_raw)
      (ensures server_hello_wire_equivalent sent_sh received_sh)
=
  let sent_fragment = W.serialize_handshake (M.ServerHello sent_sh) in
  let received_fragment = W.serialize_handshake (M.ServerHello received_sh) in
  let sent_record = W.serialize_record T.Handshake sent_fragment in
  let received_record = W.serialize_record T.Handshake received_fragment in
  W.lemma_serialize_server_hello_len sent_sh;
  W.lemma_serialize_server_hello_len received_sh;
  WR.lemma_serialize_tls_message_handshake (M.ServerHello sent_sh);
  WR.lemma_serialize_tls_message_handshake (M.ServerHello received_sh);
  assert (B.length sent_fragment <= 16640);
  assert (B.length received_fragment <= 16640);
  assert (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sent_sh)) == sent_record);
  assert (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello received_sh)) == received_record);
  assert (Seq.equal sent_raw sent_record);
  assert (Seq.equal received_raw received_record);
  lemma_seq_equal_sym received_raw received_record;
  lemma_seq_equal_trans sent_raw received_raw received_record;
  lemma_seq_equal_sym sent_raw sent_record;
  lemma_seq_equal_trans sent_record sent_raw received_record;
  assert (Seq.equal sent_record received_record);
  Seq.lemma_eq_elim sent_record received_record;
  lemma_parse_record_wire_serialize_record T.Handshake sent_fragment;
  lemma_parse_record_wire_serialize_record T.Handshake received_fragment;
  assert (Some (T.Handshake, sent_fragment, B.length sent_record) ==
          Some (T.Handshake, received_fragment, B.length received_record))
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_paired_cleartext_hello_wire_equivalent_from_cleartext_raw
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:M.client_hello)
  (server_ch:M.client_hello)
  (client_sh:M.server_hello)
  (server_sh:M.server_hello)
  (client_ch_raw:B.bytes)
  (server_ch_raw:B.bytes)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh /\
        supported_client_hello_wire_profile client_ch /\
        Seq.equal client_ch_raw server_ch_raw /\
        Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw)
      (ensures paired_cleartext_hello_wire_equivalent client server)
=
  lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
    client_ch
    server_ch
    client_ch_raw
    server_ch_raw;
  lemma_server_hello_wire_equivalent_from_sent_cleartext_and_received_cleartext
    server_sh
    client_sh
    server_sh_raw
    client_sh_raw
#pop-options

(* ------------------------------------------------------------------------- *)
(* Step-level characterisation of how the handshake fields hs_start,         *)
(* hs_server_selection and hs_client_hello may evolve under a single legal   *)
(* (and raw-delta-legal) model step.  Each is either unchanged or freshly    *)
(* established by a role-appropriate event: local client start/sent          *)
(* ClientHello for clients, received ClientHello/local server selection for  *)
(* servers.                                                                  *)
(* ------------------------------------------------------------------------- *)

let step_fields_post
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  : prop =
  let hs0 = model.CS.model_handshake in
  let hs1 = model1.CS.model_handshake in
  let cfg = model.CS.model_config in
  model1.CS.model_config == cfg /\
  (* hs_start *)
  ( hs1.CS.hs_start == hs0.CS.hs_start \/
    ( cfg.CS.config_role == CS.ClientEndpoint /\
      ( match hs1.CS.hs_start with
        | Some start -> CS.start_matches_config cfg start
        | None -> False ) ) ) /\
  (* hs_server_selection *)
  ( hs1.CS.hs_server_selection == hs0.CS.hs_server_selection \/
    ( Some? hs1.CS.hs_server_selection /\
      cfg.CS.config_role == CS.ServerEndpoint ) ) /\
  (* hs_client_hello *)
  ( hs1.CS.hs_client_hello == hs0.CS.hs_client_hello \/
    ( cfg.CS.config_role == CS.ClientEndpoint /\
      ( match hs0.CS.hs_start, hs1.CS.hs_client_hello with
        | Some start, Some ch -> CS.client_hello_matches_start start ch
        | _, _ -> False ) ) \/
    ( cfg.CS.config_role == CS.ServerEndpoint /\
      Some? hs1.CS.hs_client_hello ) )

#push-options "--split_queries always --z3rlimit 10"
let lemma_step_model_handshake_fields
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  (ds:B.bytes)
  (dr:B.bytes)
  : Lemma
      (requires
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev ds dr)
      (ensures step_fields_post model ev model1)
=
  CSL.lemma_step_model_preserves_config model ev model1;
  match ev with
  | CS.ConnLocalEvent local ->
    assert_norm (CS.step_model model (CS.ConnLocalEvent local) ==
                 CS.step_local_event model local);
    assert (CS.legal_local_event model local);
    (match local, model.CS.model_control with
     | CS.LocalStartHandshake start, CS.ControlNew -> ()
     | CS.LocalSelectServerParameters selection,
       CS.ControlHandshaking CS.HsClientHelloReceived -> ()
     | CS.LocalStartServer, CS.ControlNew
     | CS.LocalDeriveSharedSecret _, CS.ControlHandshaking CS.HsServerHelloReceived
     | CS.LocalDeriveSharedSecret _, CS.ControlHandshaking CS.HsClientHelloReceived
     | CS.LocalInstallTrafficKeys _, CS.ControlHandshaking _
     | CS.LocalInstallTrafficKeysForRole _, CS.ControlHandshaking _
     | CS.LocalValidateCertificate _, CS.ControlHandshaking CS.HsCertificateReceived
     | CS.LocalVerifyCertificateSignature _,
       CS.ControlHandshaking CS.HsCertificateVerifyReceived
     | CS.LocalSignCertificateVerify _,
       CS.ControlHandshaking CS.HsServerEncryptedFlightSent
     | CS.LocalVerifyFinished _, CS.ControlHandshaking CS.HsServerFinishedReceived
     | CS.LocalVerifyClientFinished _, CS.ControlHandshaking CS.HsClientFinishedReceived
     | CS.LocalDeliverApplicationData _, CS.ControlApplicationData
     | CS.LocalFail _, _ -> ()
     | _, _ -> ())
  | CS.ConnNetworkEvent msg ->
    assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) ==
                 CS.step_tls_message model msg.CL.message_direction msg.CL.message_value);
    assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
    (match msg.CL.message_value, msg.CL.message_direction, model.CS.model_control with
     | M.TlsHandshake (M.ClientHello ch), CL.Sent, CS.ControlHandshaking CS.HsStarted -> ()
     | M.TlsHandshake (M.ClientHello ch), CL.Received,
       CS.ControlHandshaking CS.HsAwaitingClientHello -> ()
     | M.TlsHandshake (M.ServerHello _), CL.Received,
       CS.ControlHandshaking CS.HsClientHelloSent
     | M.TlsHandshake (M.ServerHello _), CL.Sent,
       CS.ControlHandshaking CS.HsClientHelloReceived
     | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent,
       CS.ControlHandshaking CS.HsServerHelloSent
     | M.TlsHandshake (M.Certificate _), CL.Sent,
       CS.ControlHandshaking CS.HsServerEncryptedFlightSent
     | M.TlsHandshake (M.CertificateVerify _), CL.Sent,
       CS.ControlHandshaking CS.HsServerEncryptedFlightSent
     | M.TlsHandshake (M.Finished _), CL.Sent,
       CS.ControlHandshaking CS.HsServerEncryptedFlightSent
     | M.TlsHandshake (M.EncryptedExtensions _), CL.Received,
       CS.ControlHandshaking CS.HsServerHelloReceived
     | M.TlsHandshake (M.Certificate _), CL.Received,
       CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
     | M.TlsHandshake (M.CertificateVerify _), CL.Received,
       CS.ControlHandshaking CS.HsCertificateValidated
     | M.TlsHandshake (M.Finished _), CL.Received,
       CS.ControlHandshaking CS.HsCertificateVerifyVerified
     | M.TlsHandshake (M.Finished _), CL.Received,
       CS.ControlHandshaking CS.HsServerFinishedSent
     | M.TlsHandshake (M.Finished _), CL.Sent,
       CS.ControlHandshaking CS.HsServerFinishedVerified
     | M.TlsHandshake M.HelloRetryRequest, CL.Received,
       CS.ControlHandshaking CS.HsClientHelloSent
     | M.TlsApplicationData _, _, CS.ControlApplicationData
     | M.TlsIgnoredPostHandshake _, CL.Received, CS.ControlApplicationData
     | M.TlsKeyUpdate _, CL.Received, CS.ControlApplicationData
     | M.TlsKeyUpdate M.UpdateNotRequested, CL.Sent, CS.ControlApplicationData
     | M.TlsAlert T.CloseNotify, CL.Sent, CS.ControlApplicationData
     | M.TlsAlert T.CloseNotify, CL.Received, CS.ControlApplicationData
     | M.TlsAlert T.CloseNotify, CL.Received, CS.ControlClosing
     | M.TlsAlert _, _, _
     | M.TlsChangeCipherSpec, _, CS.ControlHandshaking _ -> ()
     | _, _, _ -> ())
#pop-options

(* ------------------------------------------------------------------------- *)
(* Role invariant of a raw replay: a server selection can only be present on *)
(* a server.  ClientHello is intentionally not role-exclusive: clients send  *)
(* it and servers receive it.                                                *)
(* ------------------------------------------------------------------------- *)

let raw_replay_role_invariant (model:CS.connection_model) : prop =
  (Some? model.CS.model_handshake.CS.hs_server_selection ==>
     model.CS.model_config.CS.config_role == CS.ServerEndpoint)

let lemma_step_raw_replay_role_invariant
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  (ds:B.bytes)
  (dr:B.bytes)
  : Lemma
      (requires
        raw_replay_role_invariant model /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev ds dr)
      (ensures raw_replay_role_invariant model1)
=
  lemma_step_model_handshake_fields model ev model1 ds dr

let rec lemma_raw_replay_role_invariant_preserved
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (rs:B.bytes)
  (rr:B.bytes)
  (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay model events rs rr final /\
        raw_replay_role_invariant model)
      (ensures raw_replay_role_invariant final)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    eliminate exists (model1:CS.connection_model)
                     (delta_sent:B.bytes)
                     (delta_received:B.bytes)
                     (tail_sent:B.bytes)
                     (tail_received:B.bytes).
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final
    returns raw_replay_role_invariant final
    with _.
    ( lemma_step_raw_replay_role_invariant model ev model1 delta_sent delta_received;
      lemma_raw_replay_role_invariant_preserved
        model1 rest tail_sent tail_received final )

let lemma_raw_replay_consistent_role_invariant
  (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_raw_event_replay_consistent st)
      (ensures raw_replay_role_invariant st.CS.cs_model)
=
  lemma_raw_replay_role_invariant_preserved
    (CS.initial_model st.CS.cs_model.CS.model_config)
    st.CS.cs_event_log
    st.CS.cs_wire_log.CL.raw_sent
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_model

(* ------------------------------------------------------------------------- *)
(* #10  consumer-critical: a consistent client's ClientHello reflects the     *)
(* supported configuration profile.  Proved as a reachable-shape invariant.   *)
(* ------------------------------------------------------------------------- *)

let client_config_shape (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  ( ( match st.CS.cs_model.CS.model_handshake.CS.hs_start with
      | Some start ->
        CS.start_matches_config st.CS.cs_model.CS.model_config start
      | None -> True ) /\
    ( match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
      | Some ch ->
        ch.M.cipher_suites == st.CS.cs_model.CS.model_config.CS.config_cipher_suites /\
        ch.M.signature_schemes ==
          st.CS.cs_model.CS.model_config.CS.config_signature_schemes /\
        ch.M.server_name == Some st.CS.cs_model.CS.model_config.CS.config_server_name /\
        B.length ch.M.body == 0
      | None -> True ) )

#push-options "--split_queries always --z3rlimit 10"
let lemma_connection_delta_client_config_shape
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_config_shape st0 /\
        CS.connection_state_single_step st0 st1)
      (ensures client_config_shape st1)
=
  assert (exists delta. CS.legal_connection_delta st0 delta st1);
  let delta : CS.connection_delta =
    ID.indefinite_description_ghost CS.connection_delta
      (fun delta -> CS.legal_connection_delta st0 delta st1) in
  assert (CS.legal_connection_delta st0 delta st1);
  lemma_step_model_handshake_fields
    st0.CS.cs_model
    delta.CS.delta_event
    st1.CS.cs_model
    delta.CS.delta_raw_sent
    delta.CS.delta_raw_received;
  if st0.CS.cs_model.CS.model_config.CS.config_role = CS.ClientEndpoint then
    (match st0.CS.cs_model.CS.model_handshake.CS.hs_start with
     | Some start ->
       Seq.lemma_eq_elim
         start.CS.start_server_name
         st0.CS.cs_model.CS.model_config.CS.config_server_name
     | None -> ())
  else ()
#pop-options

let lemma_initial_client_config_shape
  (cfg:CS.connection_config)
  : Lemma (ensures client_config_shape (CS.initial cfg))
=
  ()

let lemma_connection_state_single_step_client_config_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:CS.connection_state) (y:CS.connection_state).
          {:pattern
            (client_config_shape y);
            (CS.connection_state_single_step x y)}
          client_config_shape x /\
          CS.connection_state_single_step x y ==>
          client_config_shape y)
=
  introduce forall (x:CS.connection_state) (y:CS.connection_state).
    client_config_shape x /\
    CS.connection_state_single_step x y ==>
    client_config_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_client_config_shape x y

let lemma_connection_state_consistent_client_config_shape
  (st:CS.connection_state)
  : Lemma
      (requires CS.connection_state_consistent st)
      (ensures client_config_shape st)
=
  let p = client_config_shape in
  lemma_initial_client_config_shape st.CS.cs_model.CS.model_config;
  lemma_connection_state_single_step_client_config_shape ();
  let stable :
    squash (
      forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (CS.connection_state_single_step x y)}
        p x /\ CS.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    CS.connection_state_single_step
    p
    stable;
  assert (p (CS.initial st.CS.cs_model.CS.model_config));
  assert (CS.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)

let lemma_state_supported_client_hello_wire_profile_from_config
  (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        CS.client_x25519_key_share_projection st /\
        supported_client_config_wire_profile st.CS.cs_model.CS.model_config)
      (ensures state_supported_client_hello_wire_profile st)
=
  lemma_connection_state_consistent_client_config_shape st

(* Raw replay can now relate ClientHello bytes (above).  It still cannot soundly
   produce exact paired ServerHello messages or ServerHello key-share equality
   from the previous #12/#13 preconditions: server-sent ServerHello values use
   [body = B.empty] and canonical serialization, while received values may carry
   the full wire body.  The sound ServerHello conclusion exposed here is
   [server_hello_wire_equivalent]: equality of the serialized handshake image,
   which deliberately does not inspect received structured fields when [body] is
   non-empty. *)

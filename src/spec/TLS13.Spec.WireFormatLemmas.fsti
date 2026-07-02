module TLS13.Spec.WireFormatLemmas

(** Proven supported-profile wire-format parseback and injectivity lemmas. *)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

(**
  The current ClientHello serializer is canonical for the supported profile:
  it emits the single supported cipher suite and signature scheme, and it
  serializes no SNI extension for None or an empty host.  Exact parseback to the
  original M.client_hello therefore needs to exclude Some empty-host, keep the
  hostname within the extracted serializer's fixed buffer, and require the
  supported singleton offer lists.
**)
noextract
let supported_client_hello_fields_profile (ch:M.client_hello) : prop =
  ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
  ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
  (match ch.M.server_name with
   | None -> True
   | Some hostname -> B.length hostname <= 255)

noextract
let supported_client_hello_wire_profile (ch:M.client_hello) : prop =
  supported_client_hello_fields_profile ch /\
  B.length ch.M.body == 0

noextract
let exact_client_hello_wire_parseback_profile (ch:M.client_hello) : prop =
  supported_client_hello_wire_profile ch /\
  (match ch.M.server_name with
   | None -> True
   | Some hostname -> B.length hostname > 0)

noextract
let state_exact_client_hello_wire_parseback_profile
  (st:CS.connection_state)
  : prop =
  match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
  | Some ch -> exact_client_hello_wire_parseback_profile ch
  | None -> False

noextract
let state_supported_client_hello_wire_profile (st:CS.connection_state) : prop =
  match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
  | Some ch -> supported_client_hello_wire_profile ch
  | None -> False

noextract
let supported_client_config_wire_profile (cfg:CS.connection_config) : prop =
  cfg.CS.config_role == CS.ClientEndpoint /\
  B.length cfg.CS.config_server_name <= 255 /\
  cfg.CS.config_cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
  cfg.CS.config_signature_schemes == [T.RsaPssRsaeSha256]

noextract
let client_hello_server_name_wire_equivalent
  (sent_ch:M.client_hello)
  (received_ch:M.client_hello)
  : prop =
  sent_ch.M.server_name == received_ch.M.server_name \/
  (sent_ch.M.server_name == Some B.empty /\ received_ch.M.server_name == None)

noextract
let client_hello_wire_equivalent
  (sent_ch:M.client_hello)
  (received_ch:M.client_hello)
  : prop =
  Seq.equal sent_ch.M.random received_ch.M.random /\
  client_hello_server_name_wire_equivalent sent_ch received_ch /\
  Seq.equal sent_ch.M.key_share received_ch.M.key_share /\
  supported_client_hello_wire_profile sent_ch /\
  supported_client_hello_fields_profile received_ch

(**
  ServerHello is asymmetric in the model:

  * a server-sent value is required by [CS.server_hello_matches_selection] to
    have [body = B.empty], so [W.serialize_handshake] uses the canonical
    serializer over the structured fields; but
  * a client-received value produced by the wire parser carries the full
    handshake bytes in [body], so [W.serialize_handshake] replays [body] and does
    not inspect [random/key_share/cipher_suite].

  Therefore raw replay can soundly imply equality of the ServerHello wire image
  below, but not equality of [M.server_hello] records and not equality of
  [key_share] fields unless an additional invariant connects a received
  ServerHello's structured fields to its carried [body].
**)
noextract
let server_hello_wire_equivalent
  (sent_sh:M.server_hello)
  (received_sh:M.server_hello)
  : prop =
  Seq.equal
    (W.serialize_handshake (M.ServerHello sent_sh))
    (W.serialize_handshake (M.ServerHello received_sh))

noextract
let paired_cleartext_hello_wire_equivalent
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_client_hello,
    server_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    server_hs.CS.hs_server_hello
  with
  | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
    client_hello_wire_equivalent client_ch server_ch /\
    server_hello_wire_equivalent server_sh client_sh
  | _, _, _, _ ->
    False

(**
  Stronger than [paired_cleartext_hello_wire_equivalent]: this records the
  key-share equality callers need for X25519 reasoning.  It is intentionally not
  advertised as a consequence of raw replay alone; a received ServerHello with a
  non-empty [body] serializes from [body], so raw bytes alone do not constrain its
  [key_share] field.
**)
noextract
let paired_cleartext_hello_key_shares
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_client_hello,
    server_hs.CS.hs_client_hello,
    client_hs.CS.hs_server_hello,
    server_hs.CS.hs_server_hello
  with
  | Some client_ch, Some server_ch, Some client_sh, Some server_sh ->
    CS.client_hello_key_share client_ch == CS.client_hello_key_share server_ch /\
    CS.server_hello_key_share client_sh == CS.server_hello_key_share server_sh
  | _, _, _, _ ->
    False

(**
  The protected handshake records are parsed into structured messages, but the
  transcript depends only on their serialized handshake bytes.  For messages
  whose received representation carries verbatim wire bodies, byte replay should
  establish this weaker predicate rather than exact [M] record equality.
**)
noextract
let paired_protected_handshake_wire_equivalent
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_encrypted_extensions,
    server_hs.CS.hs_encrypted_extensions,
    client_hs.CS.hs_certificate,
    server_hs.CS.hs_certificate,
    client_hs.CS.hs_certificate_verify,
    server_hs.CS.hs_certificate_verify,
    client_hs.CS.hs_server_finished,
    server_hs.CS.hs_server_finished,
    client_hs.CS.hs_client_finished,
    server_hs.CS.hs_client_finished
  with
  | Some client_ee, Some server_ee,
    Some client_cert, Some server_cert,
    Some client_cv, Some server_cv,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    Seq.equal
      (W.serialize_handshake (M.EncryptedExtensions server_ee))
      (W.serialize_handshake (M.EncryptedExtensions client_ee)) /\
    Seq.equal
      (W.serialize_handshake (M.Certificate server_cert))
      (W.serialize_handshake (M.Certificate client_cert)) /\
    Seq.equal
      (W.serialize_handshake (M.CertificateVerify server_cv))
      (W.serialize_handshake (M.CertificateVerify client_cv)) /\
    Seq.equal
      (W.serialize_handshake (M.Finished server_sf))
      (W.serialize_handshake (M.Finished client_sf)) /\
    Seq.equal
      (W.serialize_handshake (M.Finished client_cf))
      (W.serialize_handshake (M.Finished server_cf))
  | _, _, _, _, _, _, _, _, _, _ ->
    False

val lemma_parse_record_wire_serialize_record
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (ensures
        W.parse_record_wire (W.serialize_record content_type fragment) ==
          Some
            (content_type,
             fragment,
             B.length (W.serialize_record content_type fragment)))

val lemma_parse_client_hello_serialize_client_hello
  (ch:M.client_hello)
  : Lemma
      (requires exact_client_hello_wire_parseback_profile ch)
      (ensures W.parse_client_hello (W.serialize_client_hello ch) == Some ch)

(**
  ClientHello TLS-message parseback is now proved in
  TLS13.Wire.Spec.Reveal.ClientHello.Parseback.  Exact ServerHello message
  equality from raw replay remains intentionally unexposed: server-sent
  ServerHello values serialize canonically with [body = B.empty], while received
  values may carry the full wire body, so raw bytes alone imply only
  [server_hello_wire_equivalent], not record equality (nor ServerHello key-share
  equality).
**)

val lemma_client_hello_received_body_from_sent_cleartext_and_received_parse
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

val lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
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

val lemma_client_hello_serialize_handshake_from_sent_cleartext_and_received_parse
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
      (ensures
        Seq.equal
          (W.serialize_handshake (M.ClientHello sent_ch))
          (W.serialize_handshake (M.ClientHello received_ch)))

val lemma_server_hello_wire_equivalent_from_sent_cleartext_and_received_cleartext
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

val lemma_parse_supported_server_hello_same_fragment
  (sent_sh:M.server_hello)
  (received_sh:M.server_hello)
  (sent_fragment:B.bytes)
  (received_fragment:B.bytes)
  : Lemma
      (requires
        Seq.equal sent_fragment received_fragment /\
        W.parse_supported_server_hello sent_fragment == Some sent_sh /\
        W.parse_supported_server_hello received_fragment == Some received_sh)
      (ensures
        sent_sh == received_sh /\
        CS.server_hello_key_share sent_sh ==
          CS.server_hello_key_share received_sh)

(**
  Corrected paired raw-bytes lemma.  A state-level raw replay proof first needs
  to identify the matching cleartext ClientHello and ServerHello record slices in
  the two logs.  Once those slices are available, the sound conclusion is
  [paired_cleartext_hello_wire_equivalent], not exact
  [CS.paired_cleartext_hello_messages] and not ServerHello key-share equality.
**)
val lemma_paired_cleartext_hello_wire_equivalent_from_cleartext_raw
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

val lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
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
      (ensures
        paired_cleartext_hello_wire_equivalent client server /\
        CS.same_transcript_checkpoint CS.TH_CH client server /\
        CS.same_transcript_checkpoint CS.TH_SH client server /\
        CS.same_key_derivation_checkpoint CS.DeriveHandshakeTraffic client server)

val lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire
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
          client_sh_raw /\
        paired_protected_handshake_wire_equivalent client server)
      (ensures
        paired_cleartext_hello_wire_equivalent client server /\
        paired_protected_handshake_wire_equivalent client server /\
        CS.paired_handshake_events client server /\
        CS.same_key_derivation_checkpoint
          CS.DeriveApplicationTraffic
          client
          server)

val lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
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
          client_sh_raw /\
        W.parse_supported_server_hello
          (W.serialize_handshake (M.ServerHello server_sh)) == Some server_sh /\
        W.parse_supported_server_hello
          (W.serialize_handshake (M.ServerHello client_sh)) == Some client_sh)
      (ensures
        paired_cleartext_hello_wire_equivalent client server /\
        paired_cleartext_hello_key_shares client server)

val lemma_state_supported_client_hello_wire_profile_from_config
  (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        CS.client_x25519_key_share_projection st /\
        supported_client_config_wire_profile st.CS.cs_model.CS.model_config)
      (ensures state_supported_client_hello_wire_profile st)

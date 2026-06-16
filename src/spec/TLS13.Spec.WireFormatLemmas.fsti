module TLS13.Spec.WireFormatLemmas

(**
  Assumption boundary for supported-profile wire-format parseback and
  injectivity lemmas.

  These lemmas are intentionally stated in an interface-only module for now:
  they can be implemented by direct F* proofs over TLS13.Wire.Spec, or replaced
  by EverParse-derived codec theorems.  The rest of the end-to-end agreement
  proof should depend on this narrow surface rather than on ad-hoc parser facts.
**)

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
  original M.client_hello therefore needs to exclude Some empty-host and require
  the supported singleton offer lists.
**)
noextract
let supported_client_hello_wire_profile (ch:M.client_hello) : prop =
  ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
  ch.M.signature_schemes == [T.RsaPssRsaeSha256]

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
  supported_client_hello_wire_profile received_ch

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

val lemma_parse_server_hello_serialize_server_hello
  (sh:M.server_hello)
  : Lemma
      (ensures W.parse_server_hello (W.serialize_server_hello sh) == Some sh)

val lemma_parse_tls_message_serialize_client_hello
  (ch:M.client_hello)
  : Lemma
      (requires exact_client_hello_wire_parseback_profile ch)
      (ensures
        W.parse_tls_message
          T.Handshake
          (W.serialize_handshake (M.ClientHello ch)) ==
            Some (M.TlsHandshake (M.ClientHello ch)))

val lemma_parse_tls_message_serialize_server_hello
  (sh:M.server_hello)
  : Lemma
      (ensures
        W.parse_tls_message
          T.Handshake
          (W.serialize_handshake (M.ServerHello sh)) ==
            Some (M.TlsHandshake (M.ServerHello sh)))

val lemma_serialized_cleartext_client_hello_parseback
  (ch:M.client_hello)
  : Lemma
      (requires exact_client_hello_wire_parseback_profile ch)
      (ensures
        W.parse_record_wire
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ClientHello ch))) ==
          Some
            (T.Handshake,
             W.serialize_handshake (M.ClientHello ch),
             B.length
               (CS.serialized_cleartext_tls_message
                 (M.TlsHandshake (M.ClientHello ch)))) /\
        W.parse_tls_message
          T.Handshake
          (W.serialize_handshake (M.ClientHello ch)) ==
            Some (M.TlsHandshake (M.ClientHello ch)))

val lemma_serialized_cleartext_server_hello_parseback
  (sh:M.server_hello)
  : Lemma
      (ensures
        W.parse_record_wire
          (CS.serialized_cleartext_tls_message
            (M.TlsHandshake (M.ServerHello sh))) ==
          Some
            (T.Handshake,
             W.serialize_handshake (M.ServerHello sh),
             B.length
               (CS.serialized_cleartext_tls_message
                 (M.TlsHandshake (M.ServerHello sh)))) /\
        W.parse_tls_message
          T.Handshake
          (W.serialize_handshake (M.ServerHello sh)) ==
            Some (M.TlsHandshake (M.ServerHello sh)))

val lemma_client_hello_equal_from_sent_cleartext_and_received_parse
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
      (ensures sent_ch == received_ch)

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

val lemma_state_supported_client_hello_wire_profile_from_config
  (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st /\
        CS.client_x25519_key_share_projection st /\
        supported_client_config_wire_profile st.CS.cs_model.CS.model_config)
      (ensures state_supported_client_hello_wire_profile st)

val lemma_server_hello_equal_from_sent_cleartext_and_received_parse
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
      (ensures sent_sh == received_sh)

val lemma_paired_cleartext_hello_messages_from_raw_replay
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        CS.paired_wire_logs client server /\
        CS.client_x25519_key_share_projection client /\
        CS.server_x25519_key_share_projection server /\
        state_exact_client_hello_wire_parseback_profile client)
      (ensures CS.paired_cleartext_hello_messages client server)

val lemma_paired_cleartext_hello_key_shares_from_raw_replay
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        CS.paired_wire_logs client server /\
        CS.client_x25519_key_share_projection client /\
        CS.server_x25519_key_share_projection server /\
        state_supported_client_hello_wire_profile client)
      (ensures paired_cleartext_hello_key_shares client server)

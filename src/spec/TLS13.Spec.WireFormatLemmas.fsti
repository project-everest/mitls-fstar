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
  original M.client_hello therefore needs to exclude Some empty-host, keep the
  hostname within the extracted serializer's fixed buffer, and require the
  supported singleton offer lists.
**)
noextract
let supported_client_hello_wire_profile (ch:M.client_hello) : prop =
  ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
  ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
  (match ch.M.server_name with
   | None -> True
   | Some hostname -> B.length hostname <= 255)

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

(**
  Removed scaffolding lemmas (none of them are referenced by any consumer; the
  only client of this module is TLS13.Impl.Driver.Pairing, which uses solely the
  three [lemma_*_from_raw_replay] / [lemma_state_supported_*] lemmas and the
  predicates [paired_cleartext_hello_key_shares],
  [state_exact_client_hello_wire_parseback_profile] and
  [supported_client_config_wire_profile]).

  - [lemma_parse_server_hello_serialize_server_hello]: FALSE as originally
    stated.  [parse_server_hello] routes through [synth_server_hello], which
    hardcodes [M.body = B.empty], and [serialize_server_hello] ignores
    [sh.M.body], so exact parseback to an arbitrary [sh] cannot hold (any [sh]
    with a non-empty body is a counterexample).

  - [lemma_parse_tls_message_serialize_client_hello]: GENUINELY FALSE.
    [parse_tls_message T.Handshake (serialize_handshake (ClientHello ch))] is
    provably [None] (the received-handshake synthesizer rejects ClientHello, see
    TLS13.Wire.Spec.RevealDecode.lemma_parse_tls_message_no_client_hello), so it
    can never equal [Some (TlsHandshake (ClientHello ch))].  No precondition on
    [ch] can repair this.

  - [lemma_parse_tls_message_serialize_server_hello]: FALSE as stated for the
    same body-canonicalization reason as the server-hello parseback above.

  - [lemma_serialized_cleartext_client_hello_parseback]: its second conjunct is
    exactly [lemma_parse_tls_message_serialize_client_hello], hence unprovable.

  - [lemma_serialized_cleartext_server_hello_parseback]: depends on
    [lemma_parse_tls_message_serialize_server_hello].

  - [lemma_server_hello_equal_from_sent_cleartext_and_received_parse]: requires
    injectivity of [serialize_handshake] on server hellos, which fails because
    the body is serialized verbatim on the sent side but recovered as empty on
    the parse side.

  All six were unused; proving corrected (body = empty) versions would require
  re-deriving the EverParse serverHello grammar round-trip, which is not needed
  by any consumer, so they are removed instead.
**)

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

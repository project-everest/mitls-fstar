module TLS13.Spec.WireFormatLemmas

(** Supported-profile wire-format parseback and injectivity lemmas.

    Re-founded over the QuackyDucky-generated codec: [W.serialize_handshake] is
    now the generated serializer, which is injective, and the message records
    ([GCH.clientHello], [GSH.serverHello], ...) are the canonical wire form (there
    is no longer a verbatim [body] field).  Consequently "same raw bytes" implies
    "same record", and the profile predicates are stated over the total pure
    field accessors in [TLS13.Wire.Semantics]. *)

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

(**
  The supported ClientHello profile: it offers the single supported cipher suite,
  the supported signature schemes and (optionally) an SNI hostname within the
  extracted serializer's fixed buffer.
**)
noextract
let supported_client_hello_fields_profile (ch:GCH.clientHello) : prop =
  Sem.clientHello_cipher_suites ch ==
    [T.TLS_CHACHA20_POLY1305_SHA256; T.TLS_AES_128_GCM_SHA256] /\
  Sem.clientHello_sig_algs ch ==
    Some [T.Rsa_pss_rsae_sha256; T.Ecdsa_secp256r1_sha256] /\
  (match Sem.clientHello_server_name ch with
   | None -> True
   | Some hostname -> B.length hostname <= 255)

(**
  A supported ClientHello whose wire image fits in a single TLS plaintext record
  (fragment <= 16640).  With the generated codec the wire image is no longer
  canonical-by-construction, so the record-size bound (previously implied by the
  hand-written canonical serializer and the empty [body]) is stated explicitly.
**)
noextract
let supported_client_hello_wire_profile (ch:GCH.clientHello) : prop =
  supported_client_hello_fields_profile ch /\
  B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640

noextract
let state_supported_client_hello_wire_profile (st:CS.connection_state) : prop =
  match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
  | Some ch -> supported_client_hello_wire_profile ch
  | None -> False

(**
  The supported ServerHello field profile: the canonical TLS 1.3 ServerHello the
  implementation emits (see [TLS13.Impl.Serializer.Handshake.poc_canonical_sh]).
  It offers the single supported cipher suite and a 32-byte X25519 key-share.
  This mirrors [supported_client_hello_fields_profile] on the client side.
**)
noextract
let supported_server_hello_fields_profile (sh:GSH.serverHello) : prop =
  (match Sem.serverHello_key_share_x25519 sh with
   | Some k -> B.length k == 32
   | None -> False) /\
  (match Sem.serverHello_cipher_suite sh with
   | Some cs -> H.is_supported_cipher_suite cs
   | None -> False)

(**
  A supported ServerHello whose wire image fits in a single TLS plaintext record
  (fragment <= 16640).  With the generated codec the [GSH.serverHello] record is
  unbounded (extensions up to 65535 bytes), so the record-size bound previously
  guaranteed by the hand-written [M.server_hello] type (via [server_hello_max_len]
  and [W.lemma_serialize_server_hello_len]) is now stated explicitly here.  This
  is the exact server analog of [supported_client_hello_wire_profile] and restores
  the client/server symmetry: the old bounded type gave the bound for free, the
  generated one requires it as an explicit profile hypothesis.
**)
noextract
let supported_server_hello_wire_profile (sh:GSH.serverHello) : prop =
  supported_server_hello_fields_profile sh /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640

noextract
let state_supported_server_hello_wire_profile (st:CS.connection_state) : prop =
  match st.CS.cs_model.CS.model_handshake.CS.hs_server_hello with
  | Some sh -> supported_server_hello_wire_profile sh
  | None -> False

noextract
let supported_client_config_wire_profile (cfg:CS.connection_config) : prop =
  cfg.CS.config_role == CS.ClientEndpoint /\
  B.length cfg.CS.config_server_name <= 255 /\
  cfg.CS.config_cipher_suites ==
    [T.TLS_CHACHA20_POLY1305_SHA256; T.TLS_AES_128_GCM_SHA256] /\
  cfg.CS.config_signature_schemes ==
    [T.Rsa_pss_rsae_sha256; T.Ecdsa_secp256r1_sha256]

noextract
let client_hello_server_name_wire_equivalent
  (sent_ch:GCH.clientHello)
  (received_ch:GCH.clientHello)
  : prop =
  Sem.clientHello_server_name sent_ch == Sem.clientHello_server_name received_ch \/
  (Sem.clientHello_server_name sent_ch == Some B.empty /\
   Sem.clientHello_server_name received_ch == None)

noextract
let client_hello_wire_equivalent
  (sent_ch:GCH.clientHello)
  (received_ch:GCH.clientHello)
  : prop =
  Seq.equal (Sem.clientHello_random sent_ch) (Sem.clientHello_random received_ch) /\
  client_hello_server_name_wire_equivalent sent_ch received_ch /\
  Sem.clientHello_key_share_x25519 sent_ch ==
    Sem.clientHello_key_share_x25519 received_ch /\
  supported_client_hello_wire_profile sent_ch /\
  supported_client_hello_fields_profile received_ch

(**
  ServerHello wire equivalence: equality of the serialized handshake image.  With
  the injective generated codec this actually coincides with record equality, but
  the wire-image form is what the transcript depends on.
**)
noextract
let server_hello_wire_equivalent
  (sent_sh:GSH.serverHello)
  (received_sh:GSH.serverHello)
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
  Stronger than [paired_cleartext_hello_wire_equivalent]: records the key-share
  equality callers need for X25519 reasoning.  With the injective codec this now
  follows from raw replay alone.
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
    // The secp256r1 offer travels with the X25519 one, for the same reason the
    // ServerHello's whole key-share extension does.
    Sem.clientHello_key_share_secp256r1 client_ch ==
      Sem.clientHello_key_share_secp256r1 server_ch /\
    CS.server_hello_key_share client_sh == CS.server_hello_key_share server_sh /\
    // The negotiated group travels with the share.  [paired_x25519_key_shares]
    // and both key-share projections are group-indexed and read the group off a
    // ServerHello, so peering has to pin the whole key-share extension, not only
    // its X25519 instance.  Both sides hold the same parsed message, so this is
    // as free as the line above.
    Sem.serverHello_kex_share client_sh == Sem.serverHello_kex_share server_sh /\
    // Both endpoints read the negotiated AEAD algorithm off their own stored
    // ServerHello, so peering must pin the selected cipher suite as well.
    Sem.serverHello_cipher_suite client_sh == Sem.serverHello_cipher_suite server_sh
  | _, _, _, _ ->
    False

(**
  Protected handshake records are parsed into structured messages, but the
  transcript depends only on their serialized handshake bytes.  Byte replay
  establishes this wire-image equivalence.
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

(**
  For a supported ClientHello the wire image fits in a single TLS plaintext
  record.  Now immediate from [supported_client_hello_wire_profile].
**)
val lemma_serialize_handshake_client_hello_record_bound
  (ch:GCH.clientHello)
  : Lemma
      (requires supported_client_hello_wire_profile ch)
      (ensures B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640)

(**
  For a supported ServerHello the wire image fits in a single TLS plaintext
  record.  Immediate from [supported_server_hello_wire_profile].  This is the
  server analog of [lemma_serialize_handshake_client_hello_record_bound] and
  restores the record-parseability bound the deleted [M.server_hello_max_len] /
  [W.lemma_serialize_server_hello_len] previously provided.
**)
val lemma_serialize_handshake_server_hello_record_bound
  (sh:GSH.serverHello)
  : Lemma
      (requires supported_server_hello_wire_profile sh)
      (ensures B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)

(**
  A sent (canonical) supported ClientHello and the ClientHello obtained by
  parsing the same raw record coincide field-by-field (indeed as records).
**)
val lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
  (sent_ch:GCH.clientHello)
  (received_ch:GCH.clientHello)
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

val lemma_received_client_hello_raw_length
  (ch:GCH.clientHello)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          raw)
      (ensures
        B.length raw ==
          B.length
            (CS.serialized_cleartext_tls_message
              (M.TlsHandshake (M.ClientHello ch))))

val lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
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
        B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640 /\
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
        TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_CH client server /\
        TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_SH client server /\
        TLS13.Spec.StateMachine.Correspondence.same_key_derivation_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.DeriveHandshakeTraffic client server)

val lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
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
        B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640 /\
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
        TLS13.Spec.StateMachine.Correspondence.paired_handshake_events client server /\
        TLS13.Spec.StateMachine.Correspondence.same_key_derivation_checkpoint
          TLS13.Spec.StateMachine.KeyIdentifiers.DeriveApplicationTraffic
          client
          server)

(**
  Key-share pairing.  With the injective codec, raw replay already forces
  [client_sh == server_sh] and [client_ch == server_ch], so the previous
  [parse_supported_server_hello] side conditions are no longer required.
**)
val lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
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
        B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640 /\
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
        paired_cleartext_hello_key_shares client server)

val lemma_state_supported_client_hello_wire_profile_from_config
  (st:CS.connection_state)
  : Lemma
      (requires
        TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
        TLS13.Spec.StateMachine.Correspondence.client_x25519_key_share_projection st /\
        supported_client_config_wire_profile st.CS.cs_model.CS.model_config)
      (ensures state_supported_client_hello_wire_profile st)

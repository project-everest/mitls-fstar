module TLS13.Spec.WireFormatLemmas

(** Supported-profile wire-format parseback and injectivity lemmas.

    Re-founded over the QuackyDucky-generated codec.  [W.serialize_handshake] is
    now the generated serializer, so it is injective and the message records
    ([GCH.clientHello], [GSH.serverHello], ...) are the canonical wire form.
    Consequently the old hand-written parseback machinery collapses to:

    * the free record-framing round trip ([lemma_parse_record_wire_serialize_record]),
    * codec injectivity ([TLS13.Wire.Spec.Reveal.Injective]),
    * the generated parse/serialize round trip ([W.lemma_parse_tls_message_round_trip]).

    "Same raw wire bytes" now forces "same record", which is strictly stronger
    than the field-wise equivalence the previous version could establish. *)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module M = TLS13.Messages
module Sem = TLS13.Wire.Semantics
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WRD = TLS13.Wire.Spec.RevealDecode
module WRI = TLS13.Wire.Spec.Reveal.Injective
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

let lemma_serialize_handshake_cong
  (h1 h2:M.handshake_msg)
  : Lemma
      (requires h1 == h2)
      (ensures
        Seq.equal
          (W.serialize_handshake h1)
          (W.serialize_handshake h2))
=
  Seq.lemma_eq_intro
    (W.serialize_handshake h1)
    (W.serialize_handshake h2)

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
(* #2  supported ClientHello record-size bound                               *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 10"
let lemma_serialize_handshake_client_hello_record_bound
  (ch:GCH.clientHello)
  : Lemma
      (requires supported_client_hello_wire_profile ch)
      (ensures B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640)
=
  ()
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_serialize_handshake_server_hello_record_bound
  (sh:GSH.serverHello)
  : Lemma
      (requires supported_server_hello_wire_profile sh)
      (ensures B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)
=
  ()
#pop-options

(* ------------------------------------------------------------------------- *)
(* Core: a sent (canonical) ClientHello and the ClientHello obtained by       *)
(* parsing the same raw record are the SAME record (codec injectivity).       *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_client_hello_sent_received_eq
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
      (ensures sent_ch == received_ch)
=
  let sent_fragment = W.serialize_handshake (M.ClientHello sent_ch) in
  let sent_record = W.serialize_record T.Handshake sent_fragment in
  let sent_msg = M.TlsHandshake (M.ClientHello sent_ch) in
  lemma_serialize_handshake_client_hello_record_bound sent_ch;
  W.lemma_serialize_tls_message_handshake (M.ClientHello sent_ch);
  assert (CS.serialized_cleartext_tls_message sent_msg == sent_record);
  assert (Seq.equal sent_raw sent_record);
  Seq.lemma_eq_elim sent_raw sent_record;
  Seq.lemma_eq_elim received_raw sent_record;
  lemma_parse_record_wire_serialize_record T.Handshake sent_fragment;
  eliminate exists (fragment:B.bytes).
    W.parse_record_wire received_raw ==
      Some (T.Handshake, fragment, B.length received_raw) /\
    W.parse_tls_message T.Handshake fragment ==
      Some (M.TlsHandshake (M.ClientHello received_ch))
  with
  ( assert (fragment == sent_fragment);
    assert (W.parse_tls_message T.Handshake sent_fragment ==
      Some (M.TlsHandshake (M.ClientHello received_ch)));
    W.lemma_parse_tls_message_round_trip T.Handshake sent_fragment;
    assert (Seq.equal
      (W.serialize_handshake (M.ClientHello sent_ch))
      (W.serialize_handshake (M.ClientHello received_ch)));
    WRI.lemma_serialize_handshake_client_hello_injective sent_ch received_ch )
#pop-options

(* ------------------------------------------------------------------------- *)
(* Core: a sent (canonical) ServerHello and the ServerHello obtained by       *)
(* replaying the same raw record are the SAME record (framing + codec inj.).  *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_server_hello_sent_received_eq
  (sent_sh:GSH.serverHello)
  (received_sh:GSH.serverHello)
  (sent_raw:B.bytes)
  (received_raw:B.bytes)
  : Lemma
      (requires
        B.length (W.serialize_handshake (M.ServerHello sent_sh)) <= 16640 /\
        Seq.equal sent_raw received_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sent_sh))
          sent_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello received_sh))
          received_raw)
      (ensures sent_sh == received_sh)
=
  let sent_fragment = W.serialize_handshake (M.ServerHello sent_sh) in
  let received_fragment = W.serialize_handshake (M.ServerHello received_sh) in
  let sent_record = W.serialize_record T.Handshake sent_fragment in
  let received_record = W.serialize_record T.Handshake received_fragment in
  W.lemma_serialize_tls_message_handshake (M.ServerHello sent_sh);
  W.lemma_serialize_tls_message_handshake (M.ServerHello received_sh);
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
  if B.length received_fragment > 16640 then (
    W.lemma_parse_record_serialize_record T.Handshake sent_fragment;
    W.lemma_serialize_record_oversize T.Handshake received_fragment;
    assert (B.length sent_record >= 5);
    assert (B.length received_record == 0);
    Seq.lemma_eq_elim sent_record received_record;
    assert False
  );
  assert (B.length received_fragment <= 16640);
  WRI.lemma_serialize_record_injective T.Handshake sent_fragment received_fragment;
  WRI.lemma_serialize_handshake_server_hello_injective sent_sh received_sh
#pop-options

(* ------------------------------------------------------------------------- *)
(* External: ClientHello wire equivalence from a sent/received raw pair.      *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
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
=
  lemma_client_hello_sent_received_eq sent_ch received_ch sent_raw received_raw;
  Seq.lemma_eq_intro
    (Sem.clientHello_random sent_ch)
    (Sem.clientHello_random received_ch);
  assert (client_hello_server_name_wire_equivalent sent_ch received_ch);
  assert (client_hello_wire_equivalent sent_ch received_ch)
#pop-options

(* ------------------------------------------------------------------------- *)
(* Received ClientHello raw length agrees with the canonical serialization.   *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 10"
let lemma_received_client_hello_raw_length
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
=
  eliminate exists (fragment:B.bytes).
    W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
    W.parse_tls_message T.Handshake fragment ==
      Some (M.TlsHandshake (M.ClientHello ch))
  with
  ( W.lemma_parse_tls_message_round_trip T.Handshake fragment;
    assert (Seq.equal fragment (W.serialize_handshake (M.ClientHello ch)));
    W.lemma_serialize_tls_message_handshake (M.ClientHello ch);
    W.lemma_parse_record_wire_fragment_bound raw;
    assert (B.length fragment <= 16640);
    WRD.lemma_parse_record_wire_serialized_length
      raw
      T.Handshake
      fragment
      (B.length raw);
    W.lemma_parse_record_serialize_record T.Handshake fragment;
    Seq.lemma_eq_elim fragment (W.serialize_handshake (M.ClientHello ch));
    assert (CS.serialized_cleartext_tls_message
      (M.TlsHandshake (M.ClientHello ch)) ==
      W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch)));
    assert (B.length raw ==
      B.length
        (CS.serialized_cleartext_tls_message
          (M.TlsHandshake (M.ClientHello ch)))) )
#pop-options

(* ------------------------------------------------------------------------- *)
(* Paired cleartext hello: wire equivalence + handshake-traffic checkpoint.   *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
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
=
  lemma_client_hello_sent_received_eq
    client_ch server_ch client_ch_raw server_ch_raw;
  lemma_server_hello_sent_received_eq
    server_sh client_sh server_sh_raw client_sh_raw;
  (* records coincide; assemble the wire-equivalence view *)
  lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
    client_ch server_ch client_ch_raw server_ch_raw;
  lemma_serialize_handshake_cong
    (M.ServerHello server_sh) (M.ServerHello client_sh);
  assert (server_hello_wire_equivalent server_sh client_sh);
  assert (paired_cleartext_hello_wire_equivalent client server);
  (* transcript checkpoints from the (equal) serialized handshake images *)
  lemma_serialize_handshake_cong
    (M.ClientHello client_ch) (M.ClientHello server_ch);
  Seq.lemma_eq_elim
    (W.serialize_handshake (M.ClientHello client_ch))
    (W.serialize_handshake (M.ClientHello server_ch));
  Seq.lemma_eq_elim
    (W.serialize_handshake (M.ServerHello server_sh))
    (W.serialize_handshake (M.ServerHello client_sh));
  assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_CH client server);
  assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_SH client server);
  assert (TLS13.Spec.StateMachine.Correspondence.same_key_derivation_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.DeriveHandshakeTraffic client server)
#pop-options

(* ------------------------------------------------------------------------- *)
(* Paired handshake events: full transcript agreement through the protected   *)
(* flight, given byte-replay of the protected handshake records.              *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire
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
=
  lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
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
    Seq.lemma_eq_elim
      (W.serialize_handshake (M.EncryptedExtensions server_ee))
      (W.serialize_handshake (M.EncryptedExtensions client_ee));
    Seq.lemma_eq_elim
      (W.serialize_handshake (M.Certificate server_cert))
      (W.serialize_handshake (M.Certificate client_cert));
    Seq.lemma_eq_elim
      (W.serialize_handshake (M.CertificateVerify server_cv))
      (W.serialize_handshake (M.CertificateVerify client_cv));
    Seq.lemma_eq_elim
      (W.serialize_handshake (M.Finished server_sf))
      (W.serialize_handshake (M.Finished client_sf));
    Seq.lemma_eq_elim
      (W.serialize_handshake (M.Finished client_cf))
      (W.serialize_handshake (M.Finished server_cf));
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_CH client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_SH client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_before_CV client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_before_SF client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_SF client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_transcript_checkpoint TLS13.Spec.StateMachine.KeyIdentifiers.TH_CF client server);
    assert (TLS13.Spec.StateMachine.Correspondence.paired_handshake_events client server);
    assert (TLS13.Spec.StateMachine.Correspondence.same_key_derivation_checkpoint
      TLS13.Spec.StateMachine.KeyIdentifiers.DeriveApplicationTraffic
      client
      server)
  | _, _, _, _, _, _, _, _, _, _ ->
    assert False
#pop-options

(* ------------------------------------------------------------------------- *)
(* Paired cleartext hello key shares: X25519 key-share agreement.             *)
(* With the injective codec this needs no [parse_supported_server_hello]      *)
(* side conditions -- raw replay already forces record equality.             *)
(* ------------------------------------------------------------------------- *)

#push-options "--split_queries always --z3rlimit 20"
let lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
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
=
  lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
    client
    server
    client_ch
    server_ch
    client_sh
    server_sh
    client_ch_raw
    server_ch_raw
    client_sh_raw
    server_sh_raw;
  lemma_client_hello_sent_received_eq
    client_ch server_ch client_ch_raw server_ch_raw;
  lemma_server_hello_sent_received_eq
    server_sh client_sh server_sh_raw client_sh_raw;
  assert (CS.client_hello_key_share client_ch ==
          CS.client_hello_key_share server_ch);
  assert (CS.server_hello_key_share client_sh ==
          CS.server_hello_key_share server_sh);
  assert (paired_cleartext_hello_key_shares client server)
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
     | M.TlsAlert T.Close_notify, CL.Sent, CS.ControlApplicationData
     | M.TlsAlert T.Close_notify, CL.Received, CS.ControlApplicationData
     | M.TlsAlert T.Close_notify, CL.Received, CS.ControlClosing
     | M.TlsAlert _, _, _
     | M.TlsChangeCipherSpec, _, CS.ControlHandshaking _ -> ()
     | _, _, _ -> ())
  | CS.ConnProtectedHandshake step ->
    assert_norm (
      CS.step_model model (CS.ConnProtectedHandshake step) ==
        CS.step_protected_handshake model step);
    assert (CS.legal_protected_handshake_step model step);
    (match
       step.CS.protected_handshake_message,
       model.CS.model_control
     with
     | M.EncryptedExtensions _,
       CS.ControlHandshaking CS.HsServerHelloReceived
     | M.Certificate _,
       CS.ControlHandshaking CS.HsEncryptedExtensionsReceived
     | M.CertificateVerify _,
       CS.ControlHandshaking CS.HsCertificateValidated
     | M.Finished _,
       CS.ControlHandshaking CS.HsCertificateVerifyVerified -> ()
     | _, _ -> assert False)
#pop-options

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
        Sem.clientHello_cipher_suites ch ==
          st.CS.cs_model.CS.model_config.CS.config_cipher_suites /\
        Sem.clientHello_sig_algs ch ==
          Some st.CS.cs_model.CS.model_config.CS.config_signature_schemes /\
        Sem.clientHello_server_name ch ==
          Some st.CS.cs_model.CS.model_config.CS.config_server_name /\
        B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640
      | None -> True ) )

#push-options "--split_queries always --z3rlimit 10"
let lemma_connection_delta_client_config_shape
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        client_config_shape st0 /\
        TLS13.Spec.StateMachine.Reachability.connection_state_single_step st0 st1)
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
            (TLS13.Spec.StateMachine.Reachability.connection_state_single_step x y)}
          client_config_shape x /\
          TLS13.Spec.StateMachine.Reachability.connection_state_single_step x y ==>
          client_config_shape y)
=
  introduce forall (x:CS.connection_state) (y:CS.connection_state).
    client_config_shape x /\
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step x y ==>
    client_config_shape y
  with
    introduce _ ==> _ with
    lemma_connection_delta_client_config_shape x y

let lemma_connection_state_consistent_client_config_shape
  (st:CS.connection_state)
  : Lemma
      (requires TLS13.Spec.StateMachine.Reachability.connection_state_consistent st)
      (ensures client_config_shape st)
=
  let p = client_config_shape in
  lemma_initial_client_config_shape st.CS.cs_model.CS.model_config;
  lemma_connection_state_single_step_client_config_shape ();
  let stable :
    squash (
      forall (x:CS.connection_state) (y:CS.connection_state).
        {:pattern (p y); (TLS13.Spec.StateMachine.Reachability.connection_state_single_step x y)}
        p x /\ TLS13.Spec.StateMachine.Reachability.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    TLS13.Spec.StateMachine.Reachability.connection_state_single_step
    p
    stable;
  assert (p (CS.initial st.CS.cs_model.CS.model_config));
  assert (TLS13.Spec.StateMachine.Reachability.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)

#push-options "--split_queries always --z3rlimit 10"
let lemma_state_supported_client_hello_wire_profile_from_config
  (st:CS.connection_state)
  : Lemma
      (requires
        TLS13.Spec.StateMachine.Reachability.connection_state_consistent st /\
        TLS13.Spec.StateMachine.Correspondence.client_x25519_key_share_projection st /\
        supported_client_config_wire_profile st.CS.cs_model.CS.model_config)
      (ensures state_supported_client_hello_wire_profile st)
=
  lemma_connection_state_consistent_client_config_shape st
#pop-options

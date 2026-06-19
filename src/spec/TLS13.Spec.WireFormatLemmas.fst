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
module WRD = TLS13.Wire.Spec.RevealDecode
module ID = FStar.IndefiniteDescription
module RTC = FStar.ReflexiveTransitiveClosure

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
  WR.lemma_parse_client_hello_serialize_client_hello ch

(* ------------------------------------------------------------------------- *)
(* Vacuity workhorse: the received-message synthesizer never returns a       *)
(* ClientHello, so a received-cleartext ClientHello record is impossible.    *)
(* ------------------------------------------------------------------------- *)

let lemma_received_client_hello_raw_absurd
  (ch:M.client_hello)
  (raw:B.bytes)
  : Lemma
      (requires
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw)
      (ensures False)
=
  assert (exists (fragment:B.bytes).
    W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
    W.parse_tls_message T.Handshake fragment ==
      Some (M.TlsHandshake (M.ClientHello ch)));
  let fragment_w =
    ID.indefinite_description_ghost B.bytes
      (fun (fragment:B.bytes) ->
        W.parse_record_wire raw == Some (T.Handshake, fragment, B.length raw) /\
        W.parse_tls_message T.Handshake fragment ==
          Some (M.TlsHandshake (M.ClientHello ch))) in
  let fragment : B.bytes = fragment_w in
  assert (W.parse_tls_message T.Handshake fragment ==
            Some (M.TlsHandshake (M.ClientHello ch)));
  WRD.lemma_parse_tls_message_no_client_hello T.Handshake fragment ch

(* ------------------------------------------------------------------------- *)
(* #8 / #9  the received side is a ClientHello, which is vacuous.            *)
(* ------------------------------------------------------------------------- *)

let lemma_client_hello_equal_from_sent_cleartext_and_received_parse
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
=
  lemma_received_client_hello_raw_absurd received_ch received_raw

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
  lemma_received_client_hello_raw_absurd received_ch received_raw

(* ------------------------------------------------------------------------- *)
(* Step-level characterisation of how the handshake fields hs_start,         *)
(* hs_server_selection and hs_client_hello may evolve under a single legal   *)
(* (and raw-delta-legal) model step.  Each is either unchanged or freshly    *)
(* established by exactly one kind of event, and that establishing event     *)
(* fixes the connection role.  The received-ClientHello transition is        *)
(* excluded because its raw delta is unsatisfiable.                          *)
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
        | _, _ -> False ) ) )

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
       CS.ControlHandshaking CS.HsAwaitingClientHello ->
       assert (CS.received_cleartext_tls_message_raw
                 (M.TlsHandshake (M.ClientHello ch)) dr);
       lemma_received_client_hello_raw_absurd ch dr
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
(* Role invariant of a raw replay:                                           *)
(*   a ClientHello can only be present on a client,                          *)
(*   a server selection can only be present on a server.                     *)
(* The first half relies on the impossibility of received-ClientHello raw    *)
(* deltas; together they make a server with both fields set contradictory.   *)
(* ------------------------------------------------------------------------- *)

let raw_replay_role_invariant (model:CS.connection_model) : prop =
  (Some? model.CS.model_handshake.CS.hs_client_hello ==>
     model.CS.model_config.CS.config_role == CS.ClientEndpoint) /\
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
        ch.M.server_name == Some st.CS.cs_model.CS.model_config.CS.config_server_name
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

(* ------------------------------------------------------------------------- *)
(* #12 / #13  consumer-critical, vacuous: a server in a raw replay cannot     *)
(* have set hs_client_hello, but server_x25519_key_share_projection forces    *)
(* both hs_client_hello and hs_server_selection to be present, which the role *)
(* invariant rules out (Client and Server at once).                           *)
(* ------------------------------------------------------------------------- *)

let lemma_paired_cleartext_hello_messages_from_raw_replay
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
=
  lemma_raw_replay_consistent_role_invariant server;
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello)

let lemma_paired_cleartext_hello_key_shares_from_raw_replay
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
=
  lemma_raw_replay_consistent_role_invariant server;
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello)

module TLS13.Impl.Driver.PairingNoTailServerShape

#lang-pulse

open Pulse.Lib.Pervasives

module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GFin  = TLS13.Wire.Generated.Finished
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver

noextract
let server_no_tail_start_spine
  (server:CS.connection_state)
  : prop =
  exists e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [ CS.ConnLocalEvent CS.LocalStartServer;
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]

(**
  Final-state SERVER witnesses that follow role-locally from
  [SD.server_driver_application_ready]: the cleartext hello/model slots are
  populated and both application traffic directions have key-schedule material.
  This is deliberately a final-model fact; it does not claim that the event log
  has already been inverted to the prefix/protected-flight shape below.
**)
noextract
let server_no_tail_final_model_witnesses
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material).
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      Some selection /\
    server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
      Some server_shared /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
    CS.traffic_material_for_label
      server.CS.cs_model.CS.model_handshake.CS.hs_keys
      CS.TrafficApplication
      CS.ServerTraffic == Some server_app_write_material /\
    CS.traffic_material_for_label
      server.CS.cs_model.CS.model_handshake.CS.hs_keys
      CS.TrafficApplication
      CS.ClientTraffic == Some server_app_read_material

(**
  The intended full role-local SERVER no-tail shape.

  This is recorded as a predicate so downstream proof attempts have a precise
  normalized/local target: protected-flight messages are role-local witnesses,
  not paired/exact cross-endpoint record equalities.
**)
noextract
let server_no_tail_desired_shape
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (server_material:CS.traffic_key_material)
    (sent_msg0:M.handshake_msg)
    (sent_msg1:M.handshake_msg)
    (server_auth_skip:CS.local_event)
    (sent_msg2:M.handshake_msg)
    (sent_msg3:M.handshake_msg)
    (server_app_write_material:CS.traffic_key_material)
    (received_msg4:M.handshake_msg)
    (cf:GFin.finished)
    (server_app_read_material:CS.traffic_key_material).
    received_msg4 == M.Finished cf /\
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (PWL.server_protected_handshake_contiguous_replay_events
          server_material
          sent_msg0
          sent_msg1
          server_auth_skip
          sent_msg2
          sent_msg3
          server_app_write_material
          received_msg4
          [
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_app_read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ])

val lemma_server_no_tail_start_spine
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures server_no_tail_start_spine server)

val lemma_server_no_tail_final_model_witnesses
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures server_no_tail_final_model_witnesses server)

val lemma_server_no_tail_final_model_witnesses16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures server_no_tail_final_model_witnesses server)

val lemma_server_no_tail_start_spine_and_final_model_witnesses
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        server_no_tail_start_spine server /\
        server_no_tail_final_model_witnesses server)

(**
  One-step role-local inversion after [LocalStartServer].

  This variant keeps the explicit non-CCS premise: [TlsChangeCipherSpec] is a
  legal no-op in handshaking states, so the clean no-leading-no-op corollary
  needs an additional minimum-progress argument.
**)
val lemma_server_no_tail_second_event_client_hello_if_not_ccs
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15 /\
        (exists e1 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_server_no_tail_second_event_client_hello_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists e1 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_server_no_tail_second_event_client_hello_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_server_no_tail_third_event_select_parameters_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch selection rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest)

val lemma_server_no_tail_fourth_event_derive_shared_secret_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch selection server_shared rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            rest)

val lemma_server_no_tail_fifth_event_server_hello_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch selection server_shared sh rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            rest)

val lemma_server_no_tail_desired_shape_start_spine
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_desired_shape server)
      (ensures server_no_tail_start_spine server)

val lemma_server_no_tail_desired_shape_length
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_desired_shape server)
      (ensures FStar.List.Tot.length server.CS.cs_event_log == 15)

(**
  Corrected server no-tail boundary shape, at length 16 instead of the stale
  15 used by [server_no_tail_start_spine] above.

  A satisfiable server no-tail trace must be length 16, not 15: the server
  has to install [ServerEndpoint]/[TrafficHandshake] *read* key material
  before it can legally receive the protected [ClientFinished] record in
  [HsServerFinishedSent] (see [TLS13.Spec.StateMachine.legal_event] /
  [step_tls_message] for that receive transition, and
  `PAIRING_THEOREM.md`'s "server-side length-15 milestone is now known to be
  stale" discussion).  [server_no_tail_desired_shape] above and the spec-level
  [PWL.server_protected_handshake_contiguous_replay_events] combinator it is
  built from do not yet expose that read-key install as a distinct event, so
  this predicate is intentionally *only* the generic 16-slot spine (mirroring
  [server_no_tail_start_spine]'s shape at the corrected length) rather than a
  drop-in replacement for [server_no_tail_desired_shape]; naming what occupies
  slots 5 and 6 is the milestone described below.
**)
noextract
let server_no_tail_start_spine16
  (server:CS.connection_state)
  : prop =
  exists e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    server.CS.cs_event_log ==
      [ CS.ConnLocalEvent CS.LocalStartServer;
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ]

val lemma_server_no_tail_start_spine16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures server_no_tail_start_spine16 server)

(**
  Order-insensitive target for the two [ServerEndpoint]/[TrafficHandshake]
  key installs that the length-16 correction above makes room for: the sixth
  and seventh events (indices 5 and 6, i.e. the two events right after the
  fixed 5-event cleartext prefix
  [PWSeg.server_cleartext_handshake_prefix_events]) are each *some*
  [ServerEndpoint]/[TrafficHandshake] install
  ([PNI.server_no_tail_handshake_traffic_install_event]), without committing
  to which one is the write direction (needed before sending the encrypted
  server flight) and which is the read direction (needed before receiving
  the protected [ClientFinished]).

  This predicate is useful as a strengthened/canonical local target.  The old
  model-level skipped-[CertificateVerify] counterexample has been closed:
  [LocalSignCertificateVerify] only stores the signed value/input, while the
  network [Sent CertificateVerify] transition is the step that marks
  [hs_certificate_verify_verified], so [Sent Finished] cannot legally jump over
  the wire CV send.  The remaining reason this predicate is not exposed as a
  bare role-local theorem here is narrower: the local length-16 role trace can
  still include legal [TlsChangeCipherSpec] no-ops unless the caller supplies a
  canonical/no-extra-CCS premise, or derives the staged boundary from paired
  clean byte traces.
**)
noextract
let server_no_tail_next_two_events_handshake_installs
  (server:CS.connection_state)
  : prop =
  exists ch selection server_shared sh e5 e6 rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNI.server_no_tail_handshake_traffic_install_event e5 /\
    PNI.server_no_tail_handshake_traffic_install_event e6

(**
  Direction-sensitive refinement of the post-[ServerHello] two-install
  milestone.  The abstract local scheduler may commute the two server handshake
  installs, but a clean length-16 application-ready run cannot spend both slots
  on the same direction: the pair must cover the server write material used for
  the encrypted flight and the server read material used for the protected
  ClientFinished.
**)
noextract
let server_no_tail_handshake_write_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
  | _ ->
    False

noextract
let server_no_tail_handshake_read_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
    role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
  | _ ->
    False

noextract
let server_no_tail_two_handshake_install_cover
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  : prop =
  (server_no_tail_handshake_write_install_event e5 /\
   server_no_tail_handshake_read_install_event e6) \/
  (server_no_tail_handshake_read_install_event e5 /\
   server_no_tail_handshake_write_install_event e6)

noextract
let server_no_tail_next_two_events_handshake_install_cover
  (server:CS.connection_state)
  : prop =
  exists ch selection server_shared sh e5 e6 rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    server_no_tail_two_handshake_install_cover e5 e6

val lemma_server_no_tail_two_handshake_install_cover_cases
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  : Lemma
      (requires server_no_tail_two_handshake_install_cover e5 e6)
      (ensures
        (server_no_tail_handshake_write_install_event e5 /\
         server_no_tail_handshake_read_install_event e6) \/
        (server_no_tail_handshake_read_install_event e5 /\
         server_no_tail_handshake_write_install_event e6))

val lemma_server_no_tail_handshake_write_install_event_step_model_as_role
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        server_no_tail_handshake_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              })) == Some model1)

val lemma_server_no_tail_handshake_read_install_event_step_model_as_role
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        server_no_tail_handshake_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              })) == Some model1)

module TLS13.Impl.Driver.PairingNoTailClientPostSharedShape

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion

(**
  Client no-tail post-shared-secret inversion milestone.

  After the mandatory [LocalDeriveSharedSecret] event (the fourth event in a
  no-tail, length-16 client event log), the fifth event [e4] is known (see
  [PNI.lemma_client_no_tail_fifth_event_handshake_traffic_install_clean]) to be
  a clean client handshake-traffic install event: it installs exactly one of
  the two [TrafficHandshake] traffic-key directions (client-write or
  server-read), leaving the key schedule's other three still-empty traffic
  slots ([ks_client_handshake_traffic] xor [ks_server_handshake_traffic], and
  both application-traffic slots) untouched.

  This module proves the natural follow-on milestone: the *sixth* event [e5]
  is *also* a clean client handshake-traffic install event, regardless of
  which of the two directions [e4] happened to install first. Combined, this
  gives an order-insensitive characterization of the fifth/sixth event prefix:
  both events are [PNI.client_no_tail_handshake_traffic_install_event],
  independent of whether the client-write or the server-read direction was
  installed first.

  The crux difficulty is the case where [e4] installs the *server-read*
  direction first (leaving [ks_client_handshake_traffic] empty): in that case
  [Received EncryptedExtensions] becomes a legal (non-install) event at
  [HsServerHelloReceived], since its only key-schedule precondition is
  [Some? ks_server_handshake_traffic]. Ruling this out requires showing that a
  client connection that reaches [HsEncryptedExtensionsReceived] (or any of
  the six other "late" handshake stages, or [ControlFailed]) with
  [ks_client_handshake_traffic == None] can *never* subsequently reach
  [ControlApplicationData]: every legal event reachable from one of those
  stages either preserves the invariant (staying stuck) or is directly
  illegal (in particular, the one event that would otherwise complete the
  handshake, [Sent Finished] at [HsServerFinishedVerified], requires
  [Some? ks_client_handshake_traffic] and is therefore illegal whenever the
  invariant holds). This "late-stage stuck-forever" argument
  ([client_late_stuck], [lemma_client_late_stuck_step],
  [lemma_client_late_stuck_replay_not_application_ready]) is the main new
  proof content of this module; it reuses (but does not duplicate) the
  existing no-tail machinery exposed by
  [TLS13.Impl.Driver.PairingNoTailInversion].
**)

(**
  Direction-sensitive refinements of
  [PNI.client_no_tail_handshake_traffic_install_event].  The clean no-tail client
  trace can commute the two post-shared-secret installs, but it cannot spend both
  slots on the same direction and still reach application data in 16 events.
**)
val client_no_tail_handshake_write_install_event
  : ev:CS.conn_event -> Tot prop

val client_no_tail_handshake_read_install_event
  : ev:CS.conn_event -> Tot prop

val client_no_tail_two_handshake_install_cover
  : e4:CS.conn_event -> e5:CS.conn_event -> Tot prop

val lemma_client_no_tail_handshake_write_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_write_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficHandshake /\
          install.CS.install_direction == CS.TrafficWrite
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficWrite
        | _ ->
          False))

val lemma_client_no_tail_handshake_read_install_event_cases
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_read_install_event ev)
      (ensures (
        match ev with
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
          install.CS.install_epoch == CS.TrafficHandshake /\
          install.CS.install_direction == CS.TrafficRead
        | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
          role_install.CS.install_role == CS.ClientEndpoint /\
          role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
          role_install.CS.install_payload.CS.install_direction == CS.TrafficRead
        | _ ->
          False))

val lemma_client_no_tail_handshake_write_install_event_implies_handshake_traffic_install_event
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_write_install_event ev)
      (ensures PNI.client_no_tail_handshake_traffic_install_event ev)

val lemma_client_no_tail_handshake_read_install_event_implies_handshake_traffic_install_event
  (ev:CS.conn_event)
  : Lemma
      (requires client_no_tail_handshake_read_install_event ev)
      (ensures PNI.client_no_tail_handshake_traffic_install_event ev)

val lemma_client_no_tail_two_handshake_install_cover_cases
  (e4:CS.conn_event)
  (e5:CS.conn_event)
  : Lemma
      (requires client_no_tail_two_handshake_install_cover e4 e5)
      (ensures
        (client_no_tail_handshake_write_install_event e4 /\
         client_no_tail_handshake_read_install_event e5) \/
        (client_no_tail_handshake_read_install_event e4 /\
         client_no_tail_handshake_write_install_event e5))

val lemma_client_no_tail_handshake_write_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_handshake_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = material;
              })) == Some model1)

val lemma_client_no_tail_handshake_read_install_event_step_model_as_plain
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        client_no_tail_handshake_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = material;
              })) == Some model1)

val lemma_client_two_handshake_install_cover_model_shape
  (model4 model5 model6:CS.connection_model)
  (e4 e5:CS.conn_event)
  : Lemma
      (requires
        model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        PNI.client_no_tail_handshake_traffic_install_event e4 /\
        PNI.client_no_tail_handshake_traffic_install_event e5 /\
        client_no_tail_two_handshake_install_cover e4 e5 /\
        CS.step_model model4 e4 == Some model5 /\
        CS.step_model model5 e5 == Some model6)
      (ensures
        model6.CS.model_config == model4.CS.model_config /\
        model6.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model6.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model6.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)

(**
  The order-insensitive milestone: after the mandatory
  [LocalStartHandshake]/[Sent ClientHello]/[Received ServerHello]/
  [LocalDeriveSharedSecret] prefix, the fifth and sixth events [e4]/[e5] are
  *both* clean client handshake-traffic install events, regardless of which
  of the two [TrafficHandshake] directions [e4] happened to install first.
**)
val lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            e5 ::
            rest /\
          PNI.client_no_tail_handshake_traffic_install_event e4 /\
          PNI.client_no_tail_handshake_traffic_install_event e5)

val lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 rest.
          client.CS.cs_event_log ==
           CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           e4 ::
           e5 ::
           rest /\
          client_no_tail_two_handshake_install_cover e4 e5)

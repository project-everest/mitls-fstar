module TLS13.Impl.Driver.PairingNoTailClientShape

#lang-pulse

open Pulse.Lib.Pervasives

module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

noextract
let client_no_tail_normalized_shape
  (client:CS.connection_state)
  : prop =
  exists
    (start:CS.handshake_start)
    (client_ch:M.client_hello)
    (client_sh:M.server_hello)
    (client_shared:C.x25519_shared_secret)
    (client_hs_write_material:CS.traffic_key_material)
    (client_material:CS.traffic_key_material)
    (received_msg0:M.handshake_msg)
    (received_msg1:M.handshake_msg)
    (received_msg2:M.handshake_msg)
    (received_msg3:M.handshake_msg)
    (client_auth_skip:CS.local_event)
    (client_verify_skip:CS.local_event)
    (verified_server_finished:M.finished)
    (client_app_write_material:CS.traffic_key_material)
    (client_app_read_material:CS.traffic_key_material)
    (sent_msg4:M.handshake_msg).
    client.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start
          client_ch
          client_sh
          client_shared)
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_hs_write_material;
          }) ::
        PWL.client_protected_handshake_contiguous_replay_events
          client_material
          received_msg0
          received_msg1
          client_auth_skip
          received_msg2
          client_verify_skip
          received_msg3
          verified_server_finished
          client_app_write_material
          client_app_read_material
          sent_msg4
          [])

noextract
let client_no_tail_start_spine
  (client:CS.connection_state)
  : prop =
  exists start e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    client.CS.cs_event_log ==
      [ CS.ConnLocalEvent (CS.LocalStartHandshake start);
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ]

noextract
let client_no_tail_final_model_witnesses
  (client:CS.connection_state)
  : prop =
  exists
    (start:CS.handshake_start)
    (ch:M.client_hello)
    (sh:M.server_hello)
    (client_shared:C.x25519_shared_secret)
    (client_app_write_material:CS.traffic_key_material)
    (client_app_read_material:CS.traffic_key_material).
    client.CS.cs_model.CS.model_handshake.CS.hs_start == Some start /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
    client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
     Some client_shared /\
    CS.traffic_material_for_label
     client.CS.cs_model.CS.model_handshake.CS.hs_keys
     CS.TrafficApplication
     CS.ClientTraffic == Some client_app_write_material /\
    CS.traffic_material_for_label
     client.CS.cs_model.CS.model_handshake.CS.hs_keys
     CS.TrafficApplication
     CS.ServerTraffic == Some client_app_read_material

val lemma_client_no_tail_start_spine
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_start_spine client)

val lemma_client_no_tail_final_model_witnesses
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_final_model_witnesses client)

val lemma_client_no_tail_start_spine_and_final_model_witnesses
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        client_no_tail_start_spine client /\
        client_no_tail_final_model_witnesses client)

(**
  One-step role-local inversion after [LocalStartHandshake].

  This variant keeps the explicit non-CCS premise.  The clean variant below
  discharges that premise from the length-16 no-tail boundary.
**)
val lemma_client_no_tail_second_event_client_hello_if_not_ccs
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        (exists start e1 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists start ch rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_client_no_tail_second_event_client_hello_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_client_no_tail_third_event_server_hello_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh rest.
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
            rest)

val lemma_client_no_tail_fourth_event_derive_shared_secret_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared rest.
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
            rest)

val lemma_client_no_tail_fifth_event_handshake_traffic_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 rest.
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
            rest /\
          PNI.client_no_tail_handshake_traffic_install_event e4)

(**
  Exact client post-cleartext install order is not exposed by the role-local
  application-ready/length facts alone, nor by a bare [ClientCP.client_system]
  valid byte trace: the abstract client API/connection model allows the client
  handshake read/write traffic-key installs to commute.  The exact order below
  is stated under [client_no_tail_normalized_shape], i.e. the canonical client
  driver replay shape.
**)
val lemma_client_no_tail_fifth_event_client_handshake_write_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures
        exists start ch sh client_shared client_hs_write_material rest.
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
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = client_hs_write_material;
              }) ::
            rest)

val lemma_client_no_tail_sixth_event_server_handshake_read_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures
        exists
          start
          ch
          sh
          client_shared
          client_hs_write_material
          client_material
          rest.
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
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = client_hs_write_material;
              }) ::
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeys {
                CS.install_epoch = CS.TrafficHandshake;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = client_material;
              }) ::
            rest)

val lemma_client_no_tail_normalized_shape_start_spine
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures client_no_tail_start_spine client)

val lemma_client_no_tail_normalized_shape_length
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures FStar.List.Tot.length client.CS.cs_event_log == 16)

(**
  Role-local CertificateVerify witness: a client connection that has reached
  application-ready control state must have recorded a [hs_certificate_verify]
  witness in its model handshake state.

  Unlike the server (which can locally sign, i.e. witness, a CertificateVerify
  message via [CS.LocalSignCertificateVerify] without ever emitting a network
  [Sent CertificateVerify] event -- see the counterexample documented for
  [TLS13.Impl.Driver.PairingNoTailServerShape.server_no_tail_next_two_events_handshake_installs]
  in PAIRING_THEOREM.md), the client has no such bypass: every legal client
  transition from [HsCertificateValidated] onward to [ControlApplicationData]
  passes through a genuine network [Received CertificateVerify] event, and
  [hs_certificate_verify] is never reset once set.  This is the client-side
  half of that asymmetry, proved as a connection-state reachability invariant
  in [TLS13.ConnectionState.ClientCertificateVerifyReachability].
**)
val lemma_client_no_tail_certificate_verify_witness
  (client:CS.connection_state)
  : Lemma
      (requires CD.client_driver_application_ready client)
      (ensures Some? client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)

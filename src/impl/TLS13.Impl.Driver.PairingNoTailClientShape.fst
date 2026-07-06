module TLS13.Impl.Driver.PairingNoTailClientShape

#lang-pulse

open Pulse.Lib.Pervasives

module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CVR = TLS13.ConnectionState.ClientCertificateVerifyReachability
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

let lemma_client_no_tail_start_spine
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_start_spine client)
=
  PNI.lemma_client_no_tail_log_spine16 client;
  PNI.lemma_client_no_tail_first_event_start client;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    client.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  returns
    client_no_tail_start_spine client
  with _.
  (
    eliminate exists start rest.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest
    returns
      client_no_tail_start_spine client
    with _.
    (
      assert (client.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest);
      assert (e0 == CS.ConnLocalEvent (CS.LocalStartHandshake start));
      assert (rest == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (client.CS.cs_event_log ==
        [ CS.ConnLocalEvent (CS.LocalStartHandshake start);
          e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ])
    )
  )

let lemma_client_no_tail_final_model_witnesses
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_final_model_witnesses client)
=
  let hs = client.CS.cs_model.CS.model_handshake in
  assert (CS.stable_client_x25519_key_share_projection client);
  assert (CS.client_x25519_key_share_projection client);
  assert (CS.application_record_keys_installed_for_role
    CS.ClientEndpoint
    client.CS.cs_model);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ClientEndpoint
      CS.TrafficWrite == CS.ClientTraffic);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ClientEndpoint
      CS.TrafficRead == CS.ServerTraffic);
  match
    hs.CS.hs_start,
    hs.CS.hs_client_hello,
    hs.CS.hs_server_hello,
    hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some start, Some ch, Some sh, Some client_shared ->
    (match
      CS.traffic_material_for_label
        hs.CS.hs_keys
        CS.TrafficApplication
        CS.ClientTraffic,
      CS.traffic_material_for_label
        hs.CS.hs_keys
        CS.TrafficApplication
        CS.ServerTraffic
    with
    | Some client_app_write_material, Some client_app_read_material ->
      ()
    | _, _ ->
      assert False)
  | _, _, _, _ ->
    assert False

let lemma_client_no_tail_start_spine_and_final_model_witnesses
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        client_no_tail_start_spine client /\
        client_no_tail_final_model_witnesses client)
=
  lemma_client_no_tail_start_spine client;
  lemma_client_no_tail_final_model_witnesses client

let lemma_client_no_tail_second_event_client_hello_if_not_ccs
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
=
  PNI.lemma_client_no_tail_second_event_client_hello client

let lemma_client_no_tail_second_event_client_hello_clean
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
=
  PNI.lemma_client_no_tail_second_event_client_hello_clean client

let lemma_client_no_tail_third_event_server_hello_clean
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
=
  PNI.lemma_client_no_tail_third_event_server_hello_clean client

let lemma_client_no_tail_fourth_event_derive_shared_secret_clean
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
=
  PNI.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client

let lemma_client_no_tail_fifth_event_handshake_traffic_install_clean
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
=
  PNI.lemma_client_no_tail_fifth_event_handshake_traffic_install_clean client

let lemma_client_no_tail_fifth_event_client_handshake_write_install_clean
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
=
  eliminate exists
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
  returns
    exists start' ch sh client_shared' client_hs_write_material' rest.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_hs_write_material';
          }) ::
        rest
  with _.
  (
    let rest =
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
        [] in
    assert_norm
      (FStar.List.Tot.append
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
         rest) ==
       CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
       }) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
       CS.ConnLocalEvent
         (CS.LocalInstallTrafficKeys {
           CS.install_epoch = CS.TrafficHandshake;
           CS.install_direction = CS.TrafficWrite;
           CS.install_material = client_hs_write_material;
         }) ::
       rest);
    assert (client.CS.cs_event_log ==
       CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
       }) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
       CS.ConnLocalEvent
         (CS.LocalInstallTrafficKeys {
           CS.install_epoch = CS.TrafficHandshake;
           CS.install_direction = CS.TrafficWrite;
           CS.install_material = client_hs_write_material;
         }) ::
       rest)
  )

let lemma_client_no_tail_sixth_event_server_handshake_read_install_clean
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
=
  eliminate exists
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
  returns
    exists
      start'
      ch
      sh
      client_shared'
      client_hs_write_material'
      client_material'
      rest.
      client.CS.cs_event_log ==
        CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ServerHello sh);
        }) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_hs_write_material';
          }) ::
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = client_material';
          }) ::
        rest
  with _.
  (
    let rest =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg0;
      } ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg1;
      } ::
      CS.ConnLocalEvent client_auth_skip ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg2;
      } ::
      CS.ConnLocalEvent client_verify_skip ::
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg3;
      } ::
      PWL.client_finished_replay_events
        verified_server_finished
        client_app_write_material
        client_app_read_material
        sent_msg4
        [] in
    assert_norm
      (FStar.List.Tot.append
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
          []) ==
       CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
       rest);
    assert (client.CS.cs_event_log ==
       CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
  )

let lemma_client_no_tail_normalized_shape_start_spine
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures client_no_tail_start_spine client)
=
  eliminate exists
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
  returns
    client_no_tail_start_spine client
  with _.
  (
    let e1 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      } in
    let e2 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
      } in
    let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
    let e4 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = client_hs_write_material;
        }) in
    let e5 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = client_material;
        }) in
    let e6 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg0;
      } in
    let e7 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg1;
      } in
    let e8 = CS.ConnLocalEvent client_auth_skip in
    let e9 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg2;
      } in
    let e10 = CS.ConnLocalEvent client_verify_skip in
    let e11 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg3;
      } in
    let e12 = CS.ConnLocalEvent (CS.LocalVerifyFinished verified_server_finished) in
    let e13 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = client_app_write_material;
        }) in
    let e14 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = client_app_read_material;
        }) in
    let e15 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake sent_msg4;
      } in
    assert_norm
      (FStar.List.Tot.append
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
          []) ==
       [ CS.ConnLocalEvent (CS.LocalStartHandshake start);
         e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ]);
    assert (client.CS.cs_event_log ==
      [ CS.ConnLocalEvent (CS.LocalStartHandshake start);
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ])
  )

let lemma_client_no_tail_normalized_shape_length
  (client:CS.connection_state)
  : Lemma
      (requires client_no_tail_normalized_shape client)
      (ensures FStar.List.Tot.length client.CS.cs_event_log == 16)
=
  eliminate exists
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
  returns
    FStar.List.Tot.length client.CS.cs_event_log == 16
  with _.
  (
    assert_norm
      (FStar.List.Tot.length
        (FStar.List.Tot.append
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
            [])) == 16)
  )

let lemma_client_no_tail_certificate_verify_witness client =
  CVR.lemma_client_application_ready_certificate_verify_witness client

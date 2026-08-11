module TLS13.ConnectionState.ProtectedWireRecordAlignment

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay
open TLS13.ConnectionState.ProtectedWireBase

let lemma_client_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        client.cs_model.model_record.record_write.R.seq ==
          server.cs_model.model_record.record_read.R.seq /\
        peer_record_material_agrees
          (traffic_id epoch ClientTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          client.cs_model
          server.cs_model)
=
  match
    record_direction_material client.cs_model.model_record.record_write,
    record_direction_material server.cs_model.model_record.record_read
  with
  | Some client_write, Some server_read ->
    assert (client.cs_model.model_record.record_write.R.seq ==
      server.cs_model.model_record.record_read.R.seq);
    assert (record_key_iv_material_agrees client_write server_read)
  | _, _ ->
    assert False

let lemma_server_traffic_peer_record_material_agrees_and_seq_write_read_aligned
  (epoch:traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        server.cs_model.model_record.record_write.R.seq ==
          client.cs_model.model_record.record_read.R.seq /\
        peer_record_material_agrees
          (traffic_id epoch ServerTraffic)
          client
          server)
      (ensures
        write_read_record_material_aligned
          server.cs_model
          client.cs_model)
=
  match
    record_direction_material server.cs_model.model_record.record_write,
    record_direction_material client.cs_model.model_record.record_read
  with
  | Some server_write, Some client_read ->
    assert (server.cs_model.model_record.record_write.R.seq ==
      client.cs_model.model_record.record_read.R.seq);
    assert (record_key_iv_material_agrees server_write client_read)
  | _, _ ->
    assert False


#push-options "--split_queries always --z3rlimit 10"
let lemma_step_received_network_event_preserves_record_write
  (model:connection_model)
  (msg:M.tls_message)
  (model_after:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.model_record.record_write ==
          model.model_record.record_write)
=
  ()

let lemma_step_sent_network_event_preserves_record_read
  (model:connection_model)
  (msg:M.tls_message)
  (model_after:connection_model)
  : Lemma
      (requires
        step_model
          model
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some model_after)
      (ensures
        model_after.model_record.record_read ==
          model.model_record.record_read)
=
  ()

let lemma_step_received_network_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (msg:M.tls_message)
  (sender_after:connection_model)
  (receiver:connection_model)
  : Lemma
      (requires
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          }) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)
=
  lemma_step_received_network_event_preserves_record_write
    sender
    msg
    sender_after

let lemma_step_sent_network_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (receiver_after:connection_model)
  : Lemma
      (requires
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)
=
  lemma_step_sent_network_event_preserves_record_read
    receiver
    msg
    receiver_after

let lemma_step_opposite_network_events_preserve_write_read_record_material_alignment
  (sender:connection_model)
  (sender_msg:M.tls_message)
  (sender_after:connection_model)
  (receiver:connection_model)
  (receiver_msg:M.tls_message)
  (receiver_after:connection_model)
  : Lemma
      (requires
        step_model
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = sender_msg;
          }) == Some sender_after /\
        step_model
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = receiver_msg;
          }) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver_after)
=
  lemma_step_received_network_event_preserves_write_read_record_material_alignment
    sender
    sender_msg
    sender_after
    receiver;
  lemma_step_sent_network_event_preserves_write_read_record_material_alignment
    sender_after
    receiver
    receiver_msg
    receiver_after

let lemma_step_non_install_local_event_preserves_record_layer
  (model:connection_model)
  (ev:local_event)
  (model_after:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          model
          (ConnLocalEvent ev) == Some model_after)
      (ensures model_after.model_record == model.model_record)
=
  match ev with
  | LocalInstallTrafficKeys _
  | LocalInstallTrafficKeysForRole _ ->
    assert False
  | LocalStartHandshake _
  | LocalStartServer
  | LocalSelectServerParameters _
  | LocalDeriveSharedSecret _
  | LocalValidateCertificate _
  | LocalVerifyCertificateSignature _
  | LocalSignCertificateVerify _
  | LocalVerifyFinished _
  | LocalVerifyClientFinished _
  | LocalDeliverApplicationData _
  | LocalFail _ ->
    ()

let lemma_step_local_event_preserves_record_write
  (model:connection_model)
  (ev:local_event)
  (model_after:connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        step_model
          model
          (ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.model_record.record_write ==
          model.model_record.record_write)
=
  match ev with
  | LocalInstallTrafficKeys install ->
    (match install.install_epoch, install.install_direction with
     | TrafficApplication, TrafficWrite -> ()
     | _, TrafficRead -> ()
     | _, _ -> assert False)
  | LocalInstallTrafficKeysForRole role_install ->
    let install = role_install.install_payload in
    (match role_install.install_role, install.install_epoch, install.install_direction with
     | ServerEndpoint, TrafficApplication, TrafficWrite ->
       assert False
     | _, _, TrafficRead -> ()
     | ClientEndpoint, TrafficApplication, TrafficWrite -> ()
     | _, _, _ -> assert False)
  | LocalStartHandshake _
  | LocalStartServer
  | LocalSelectServerParameters _
  | LocalDeriveSharedSecret _
  | LocalValidateCertificate _
  | LocalVerifyCertificateSignature _
  | LocalSignCertificateVerify _
  | LocalVerifyFinished _
  | LocalVerifyClientFinished _
  | LocalDeliverApplicationData _
  | LocalFail _ ->
    ()

let lemma_step_local_event_preserves_record_read
  (model:connection_model)
  (ev:local_event)
  (model_after:connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        step_model
          model
          (ConnLocalEvent ev) == Some model_after)
      (ensures
        model_after.model_record.record_read ==
          model.model_record.record_read)
=
  match ev with
  | LocalInstallTrafficKeys install ->
    (match install.install_direction with
     | TrafficWrite -> ()
     | TrafficRead -> assert False)
  | LocalInstallTrafficKeysForRole role_install ->
    (match role_install.install_payload.install_direction with
     | TrafficWrite -> ()
     | TrafficRead -> assert False)
  | LocalStartHandshake _
  | LocalStartServer
  | LocalSelectServerParameters _
  | LocalDeriveSharedSecret _
  | LocalValidateCertificate _
  | LocalVerifyCertificateSignature _
  | LocalSignCertificateVerify _
  | LocalVerifyFinished _
  | LocalVerifyClientFinished _
  | LocalDeliverApplicationData _
  | LocalFail _ ->
    ()

let lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (ev:local_event)
  (sender_after:connection_model)
  (receiver:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          sender
          (ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)
=
  lemma_step_non_install_local_event_preserves_record_layer
    sender
    ev
    sender_after

let lemma_step_sender_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (ev:local_event)
  (sender_after:connection_model)
  (receiver:connection_model)
  : Lemma
      (requires
        local_event_preserves_record_write ev /\
        step_model
          sender
          (ConnLocalEvent ev) == Some sender_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender_after receiver)
=
  lemma_step_local_event_preserves_record_write
    sender
    ev
    sender_after

let lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (ev:local_event)
  (receiver_after:connection_model)
  : Lemma
      (requires
        local_event_does_not_install_record_keys ev /\
        step_model
          receiver
          (ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)
=
  lemma_step_non_install_local_event_preserves_record_layer
    receiver
    ev
    receiver_after

let lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (ev:local_event)
  (receiver_after:connection_model)
  : Lemma
      (requires
        local_event_preserves_record_read ev /\
        step_model
          receiver
          (ConnLocalEvent ev) == Some receiver_after /\
        write_read_record_material_aligned sender receiver)
      (ensures write_read_record_material_aligned sender receiver_after)
=
  lemma_step_local_event_preserves_record_read
    receiver
    ev
    receiver_after

let lemma_next_seq_models_preserve_write_read_record_material_alignment
  (sender:connection_model)
  (receiver:connection_model)
  (sender_after:connection_model)
  (receiver_after:connection_model)
  : Lemma
      (requires
        write_read_record_material_aligned sender receiver /\
        sender_after.model_record.record_write ==
          R.next_seq sender.model_record.record_write /\
        receiver_after.model_record.record_read ==
          R.next_seq receiver.model_record.record_read)
      (ensures write_read_record_material_aligned sender_after receiver_after)
=
  match
    record_direction_material sender.model_record.record_write,
    record_direction_material receiver.model_record.record_read
  with
  | Some sender_write, Some receiver_read ->
    assert (record_key_iv_material_agrees sender_write receiver_read);
    assert (record_direction_material sender_after.model_record.record_write ==
      record_direction_material sender.model_record.record_write);
    assert (record_direction_material receiver_after.model_record.record_read ==
      record_direction_material receiver.model_record.record_read)
  | _, _ ->
    assert False

let lemma_server_handshake_write_client_handshake_read_install_aligned
  (server:connection_model)
  (client:connection_model)
  (material:traffic_key_material)
  (server_after:connection_model)
  (client_after:connection_model)
  : Lemma
      (requires
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = material;
              };
            })) == Some server_after /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)
=
  assert (server_after.model_record.record_write ==
    R.install_keys
      server.model_record.record_write
      R.Handshake
      material.traffic_key
      material.traffic_iv);
  assert (client_after.model_record.record_read ==
    R.install_keys
      client.model_record.record_read
      R.Handshake
      material.traffic_key
      material.traffic_iv)

let lemma_server_handshake_write_client_handshake_read_install_materials_aligned
  (server:connection_model)
  (client:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (server_after:connection_model)
  (client_after:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material) /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            })) == Some server_after /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)
=
  assert (server_after.model_record.record_write ==
    R.install_keys
      server.model_record.record_write
      R.Handshake
      server_material.traffic_key
      server_material.traffic_iv);
  assert (client_after.model_record.record_read ==
    R.install_keys
      client.model_record.record_read
      R.Handshake
      client_material.traffic_key
      client_material.traffic_iv)

let lemma_server_handshake_install_materials_agree_from_key_schedule
  (server_hs:handshake_state)
  (client_hs:handshake_state)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  : Lemma
      (requires
        (match
          server_hs.hs_keys.ks_handshake_secret,
          client_hs.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal server_hs.hs_transcript client_hs.hs_transcript /\
        negotiated_aead_alg server_hs == negotiated_aead_alg client_hs /\
        traffic_install_matches_key_schedule_for_role
          ServerEndpoint
          server_hs
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = server_material;
          } /\
        traffic_install_matches_key_schedule
          client_hs
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficRead;
            install_material = client_material;
          })
      (ensures
        record_key_iv_material_agrees
          (record_material_of_traffic_material server_material)
          (record_material_of_traffic_material client_material))
=
  match
    server_hs.hs_keys.ks_handshake_secret,
    client_hs.hs_keys.ks_handshake_secret
  with
  | Some server_secret, Some client_secret ->
    Seq.lemma_eq_elim server_secret client_secret;
    Seq.lemma_eq_elim server_hs.hs_transcript client_hs.hs_transcript;
    assert (server_material ==
      traffic_key_material_for_secret
        (negotiated_aead_alg server_hs)
        (K.server_handshake_traffic_secret
          server_secret
          (Tr.hash server_hs.hs_transcript)));
    assert (client_material ==
      traffic_key_material_for_secret
        (negotiated_aead_alg client_hs)
        (K.server_handshake_traffic_secret
          client_secret
          (Tr.hash client_hs.hs_transcript)));
    Seq.lemma_eq_elim server_material.traffic_key client_material.traffic_key;
    Seq.lemma_eq_elim server_material.traffic_iv client_material.traffic_iv
  | _, _ ->
    assert False

let lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
  (server:connection_model)
  (client:connection_model)
  (server_material:traffic_key_material)
  (client_material:traffic_key_material)
  (server_after:connection_model)
  (client_after:connection_model)
  : Lemma
      (requires
        (match
          server.model_handshake.hs_keys.ks_handshake_secret,
          client.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some server_secret, Some client_secret ->
          Seq.equal server_secret client_secret
        | _, _ ->
          False) /\
        Seq.equal
          server.model_handshake.hs_transcript
          client.model_handshake.hs_transcript /\
        negotiated_aead_alg server.model_handshake ==
          negotiated_aead_alg client.model_handshake /\
        traffic_install_matches_key_schedule_for_role
          ServerEndpoint
          server.model_handshake
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = server_material;
          } /\
        traffic_install_matches_key_schedule
          client.model_handshake
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficRead;
            install_material = client_material;
          } /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficWrite;
                install_material = server_material;
              };
            })) == Some server_after /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficRead;
              install_material = client_material;
            })) == Some client_after)
      (ensures write_read_record_material_aligned server_after client_after)
=
  lemma_server_handshake_install_materials_agree_from_key_schedule
    server.model_handshake
    client.model_handshake
    server_material
    client_material;
  lemma_server_handshake_write_client_handshake_read_install_materials_aligned
    server
    client
    server_material
    client_material
    server_after
    client_after

let lemma_client_handshake_write_server_handshake_read_install_aligned
  (client:connection_model)
  (server:connection_model)
  (material:traffic_key_material)
  (client_after:connection_model)
  (server_after:connection_model)
  : Lemma
      (requires
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = material;
            })) == Some client_after /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
=
  assert (client_after.model_record.record_write ==
    R.install_keys
      client.model_record.record_write
      R.Handshake
      material.traffic_key
      material.traffic_iv);
  assert (server_after.model_record.record_read ==
    R.install_keys
      server.model_record.record_read
      R.Handshake
      material.traffic_key
      material.traffic_iv)

let lemma_client_handshake_write_server_handshake_read_install_materials_aligned
  (client:connection_model)
  (server:connection_model)
  (client_material:traffic_key_material)
  (server_material:traffic_key_material)
  (client_after:connection_model)
  (server_after:connection_model)
  : Lemma
      (requires
        record_key_iv_material_agrees
          (record_material_of_traffic_material client_material)
          (record_material_of_traffic_material server_material) /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = client_material;
            })) == Some client_after /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
=
  assert (client_after.model_record.record_write ==
    R.install_keys
      client.model_record.record_write
      R.Handshake
      client_material.traffic_key
      client_material.traffic_iv);
  assert (server_after.model_record.record_read ==
    R.install_keys
      server.model_record.record_read
      R.Handshake
      server_material.traffic_key
      server_material.traffic_iv)

let lemma_client_handshake_install_materials_agree_from_key_schedule
  (client_hs:handshake_state)
  (server_hs:handshake_state)
  (client_material:traffic_key_material)
  (server_material:traffic_key_material)
  : Lemma
      (requires
        (match
          client_hs.hs_keys.ks_handshake_secret,
          server_hs.hs_keys.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal client_hs.hs_transcript server_hs.hs_transcript /\
        negotiated_aead_alg client_hs == negotiated_aead_alg server_hs /\
        traffic_install_matches_key_schedule
          client_hs
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = client_material;
          } /\
        traffic_install_matches_key_schedule_for_role
          ServerEndpoint
          server_hs
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficRead;
            install_material = server_material;
          })
      (ensures
        record_key_iv_material_agrees
          (record_material_of_traffic_material client_material)
          (record_material_of_traffic_material server_material))
=
  match
    client_hs.hs_keys.ks_handshake_secret,
    server_hs.hs_keys.ks_handshake_secret
  with
  | Some client_secret, Some server_secret ->
    Seq.lemma_eq_elim client_secret server_secret;
    Seq.lemma_eq_elim client_hs.hs_transcript server_hs.hs_transcript;
    assert (client_material ==
      traffic_key_material_for_secret
        (negotiated_aead_alg client_hs)
        (K.client_handshake_traffic_secret
          client_secret
          (Tr.hash client_hs.hs_transcript)));
    assert (server_material ==
      traffic_key_material_for_secret
        (negotiated_aead_alg server_hs)
        (K.client_handshake_traffic_secret
          server_secret
          (Tr.hash server_hs.hs_transcript)));
    Seq.lemma_eq_elim client_material.traffic_key server_material.traffic_key;
    Seq.lemma_eq_elim client_material.traffic_iv server_material.traffic_iv
  | _, _ ->
    assert False

let lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
  (client:connection_model)
  (server:connection_model)
  (client_material:traffic_key_material)
  (server_material:traffic_key_material)
  (client_after:connection_model)
  (server_after:connection_model)
  : Lemma
      (requires
        (match
          client.model_handshake.hs_keys.ks_handshake_secret,
          server.model_handshake.hs_keys.ks_handshake_secret
        with
        | Some client_secret, Some server_secret ->
          Seq.equal client_secret server_secret
        | _, _ ->
          False) /\
        Seq.equal
          client.model_handshake.hs_transcript
          server.model_handshake.hs_transcript /\
        negotiated_aead_alg client.model_handshake ==
          negotiated_aead_alg server.model_handshake /\
        traffic_install_matches_key_schedule
          client.model_handshake
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficWrite;
            install_material = client_material;
          } /\
        traffic_install_matches_key_schedule_for_role
          ServerEndpoint
          server.model_handshake
          {
            install_epoch = TrafficHandshake;
            install_direction = TrafficRead;
            install_material = server_material;
          } /\
        step_model
          client
          (ConnLocalEvent
            (LocalInstallTrafficKeys {
              install_epoch = TrafficHandshake;
              install_direction = TrafficWrite;
              install_material = client_material;
            })) == Some client_after /\
        step_model
          server
          (ConnLocalEvent
            (LocalInstallTrafficKeysForRole {
              install_role = ServerEndpoint;
              install_payload = {
                install_epoch = TrafficHandshake;
                install_direction = TrafficRead;
                install_material = server_material;
              };
            })) == Some server_after)
      (ensures write_read_record_material_aligned client_after server_after)
=
  lemma_client_handshake_install_materials_agree_from_key_schedule
    client.model_handshake
    server.model_handshake
    client_material
    server_material;
  lemma_client_handshake_write_server_handshake_read_install_materials_aligned
    client
    server
    client_material
    server_material
    client_after
    server_after
#pop-options

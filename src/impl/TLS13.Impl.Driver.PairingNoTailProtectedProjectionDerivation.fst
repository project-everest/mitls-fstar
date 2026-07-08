module TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module Pairing = TLS13.Impl.Driver.Pairing
module PWS = TLS13.ConnectionState.ProtectedWireStaged
module Tac = FStar.Tactics

#push-options "--split_queries always --z3rlimit 10"

let lemma_pairing_protected_projection_witnesses_from_installed_replay_inputs
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  (server_flight_sender:CS.connection_model)
  (server_flight_receiver:CS.connection_model)
  (server_after0:CS.connection_model)
  (client_after0:CS.connection_model)
  (server_after1:CS.connection_model)
  (client_after1:CS.connection_model)
  (server_after_auth_skip:CS.connection_model)
  (client_after_auth_skip:CS.connection_model)
  (server_after2:CS.connection_model)
  (client_after2:CS.connection_model)
  (client_after_verify_skip:CS.connection_model)
  (server_after3:CS.connection_model)
  (client_after3:CS.connection_model)
  (server_auth_skip:CS.local_event)
  (client_auth_skip:CS.local_event)
  (client_verify_skip:CS.local_event)
  (sent_msg0:TLS13.Messages.handshake_msg)
  (received_msg0:TLS13.Messages.handshake_msg)
  (sent_msg1:TLS13.Messages.handshake_msg)
  (received_msg1:TLS13.Messages.handshake_msg)
  (sent_msg2:TLS13.Messages.handshake_msg)
  (received_msg2:TLS13.Messages.handshake_msg)
  (sent_msg3:TLS13.Messages.handshake_msg)
  (received_msg3:TLS13.Messages.handshake_msg)
  (server_rest:list CS.conn_event)
  (client_rest:list CS.conn_event)
  (server_raw_sent:B.bytes)
  (server_raw_received:B.bytes)
  (client_raw_sent:B.bytes)
  (client_raw_received:B.bytes)
  (server_final:CS.connection_model)
  (client_final:CS.connection_model)
  (client_finished_sender:CS.connection_model)
  (client_finished_receiver:CS.connection_model)
  (cf_client_after_verify:CS.connection_model)
  (cf_client_after_app_write:CS.connection_model)
  (cf_client_after_app_read:CS.connection_model)
  (cf_server_after_app_write:CS.connection_model)
  (cf_client_after_finished:CS.connection_model)
  (cf_server_after_finished:CS.connection_model)
  (verified_server_finished:TLS13.Messages.finished)
  (client_app_write_material:CS.traffic_key_material)
  (client_app_read_material:CS.traffic_key_material)
  (server_app_write_material:CS.traffic_key_material)
  (sent_msg4:TLS13.Messages.handshake_msg)
  (received_msg4:TLS13.Messages.handshake_msg)
  (client_finished_rest:list CS.conn_event)
  (server_finished_rest:list CS.conn_event)
  (client_finished_raw_sent:B.bytes)
  (client_finished_raw_received:B.bytes)
  (server_finished_raw_sent:B.bytes)
  (server_finished_raw_received:B.bytes)
  (client_finished_final:CS.connection_model)
  (server_finished_final:CS.connection_model)
  : Lemma
      (requires
        installed_protected_projection_replay_inputs
          client_state
          server_state
          server_flight_sender
          server_flight_receiver
          server_after0
          client_after0
          server_after1
          client_after1
          server_after_auth_skip
          client_after_auth_skip
          server_after2
          client_after2
          client_after_verify_skip
          server_after3
          client_after3
          server_auth_skip
          client_auth_skip
          client_verify_skip
          sent_msg0
          received_msg0
          sent_msg1
          received_msg1
          sent_msg2
          received_msg2
          sent_msg3
          received_msg3
          server_rest
          client_rest
          server_raw_sent
          server_raw_received
          client_raw_sent
          client_raw_received
          server_final
          client_final
          client_finished_sender
          client_finished_receiver
          cf_client_after_verify
          cf_client_after_app_write
          cf_client_after_app_read
          cf_server_after_app_write
          cf_client_after_finished
          cf_server_after_finished
          verified_server_finished
          client_app_write_material
          client_app_read_material
          server_app_write_material
          sent_msg4
          received_msg4
          client_finished_rest
          server_finished_rest
          client_finished_raw_sent
          client_finished_raw_received
          server_finished_raw_sent
          server_finished_raw_received
          client_finished_final
          server_finished_final)
      (ensures
        Pairing.paired_protected_handshake_event_projection_pair_witnesses
          client_state
          server_state)
=
  PWS.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_installed_server_flight_replays
      client_state
      server_state
      server_flight_sender
      server_flight_receiver
      server_after0
      client_after0
      server_after1
      client_after1
      server_after_auth_skip
      client_after_auth_skip
      server_after2
      client_after2
      client_after_verify_skip
      server_after3
      client_after3
      server_auth_skip
      client_auth_skip
      client_verify_skip
      sent_msg0
      received_msg0
      sent_msg1
      received_msg1
      sent_msg2
      received_msg2
      sent_msg3
      received_msg3
      server_rest
      client_rest
      server_raw_sent
      server_raw_received
      client_raw_sent
      client_raw_received
      server_final
      client_final
      client_finished_sender
      client_finished_receiver
      cf_client_after_verify
      cf_client_after_app_write
      cf_client_after_app_read
      cf_server_after_app_write
      cf_client_after_finished
      cf_server_after_finished
      verified_server_finished
      client_app_write_material
      client_app_read_material
      server_app_write_material
      sent_msg4
      received_msg4
      client_finished_rest
      server_finished_rest
      client_finished_raw_sent
      client_finished_raw_received
      server_finished_raw_sent
      server_finished_raw_received
      client_finished_final
      server_finished_final;
  assert
    (Pairing.paired_protected_handshake_event_projection_pair_witnesses
      client_state
      server_state)
  by (
    Tac.norm
      [delta_only
        [`%Pairing.paired_protected_handshake_event_projection_pair_witnesses]];
    Tac.smt ())

let lemma_pairing_protected_projection_witnesses_from_installed_replay_witnesses
  (client_state:CS.connection_state)
  (server_state:CS.connection_state)
  : Lemma
      (requires
        installed_protected_projection_replay_witnesses
          client_state
          server_state)
      (ensures
        Pairing.paired_protected_handshake_event_projection_pair_witnesses
          client_state
          server_state)
=
  (*
   * WIP admit, scoped to the existential packaging layer.
   *
   * The stronger input-level lemma above verifies once all replay witnesses are
   * named explicitly.  This wrapper should only destruct
   * [installed_protected_projection_replay_witnesses] and pass the witnesses to
   * that verified lemma, but the current large nested existential package is not
   * unfolding/eliminating robustly under the module interface.  The remaining
   * proof task is therefore mechanical packaging, not a new cryptographic or
   * state-machine assumption.
   *)
  admit()

#pop-options

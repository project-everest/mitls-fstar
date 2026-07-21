module TLS13.Impl.Driver.PairingNoTailServerFlightReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module X = TLS13.X509.Spec

(**
  A narrow package for exactly the server encrypted-flight part of
  [PairingStagedNormalizedBoundary.paired_supported_normalized_staged_replay_boundary_inputs].

  The two replay predicates start at the post-cleartext models
  [hcb_server_model5] and [hcb_client_model4], use the staged canonical event
  lists (server handshake write install; EE; Certificate; auth-skip;
  CertificateVerify; Finished; rest, and dually on the client), and expose the
  raw streams for that slice.
**)
noeq
type server_flight_replay_witnesses = {
  sfr_server_flight_rest: list CS.conn_event;
  sfr_client_flight_rest: list CS.conn_event;
  sfr_server_raw_sent: B.bytes;
  sfr_server_raw_received: B.bytes;
  sfr_client_raw_sent: B.bytes;
  sfr_client_raw_received: B.bytes;
  sfr_server_final: CS.connection_model;
  sfr_client_final: CS.connection_model;
}

noextract
let server_encrypted_flight_staged_replay_fragment
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (r:server_flight_replay_witnesses)
  : prop =
  Seq.equal r.sfr_server_raw_sent r.sfr_client_raw_received /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_server_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_auth_skip /\
  PWL.local_event_does_not_install_record_keys w.PCB.hcb_client_verify_skip /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg0 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg1 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg2 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg3 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg3 /\
  CS.step_model
    w.PCB.hcb_server_model5
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_material;
        };
      })) == Some w.PCB.hcb_server_after_install /\
  CS.step_model
    w.PCB.hcb_client_model4
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_material;
      })) == Some w.PCB.hcb_client_after_install /\
  CS.step_model
    w.PCB.hcb_server_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg0;
    }) == Some w.PCB.hcb_server_after0 /\
  CS.step_model
    w.PCB.hcb_client_after_install
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg0;
    }) == Some w.PCB.hcb_client_after0 /\
  w.PCB.hcb_server_after0.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_install.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after0.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_install.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg1;
    }) == Some w.PCB.hcb_server_after1 /\
  CS.step_model
    w.PCB.hcb_client_after0
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg1;
    }) == Some w.PCB.hcb_client_after1 /\
  w.PCB.hcb_server_after1.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after0.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after1.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after0.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_server_after1
    (CS.ConnLocalEvent w.PCB.hcb_server_auth_skip) ==
    Some w.PCB.hcb_server_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_client_after1
    (CS.ConnLocalEvent w.PCB.hcb_client_auth_skip) ==
    Some w.PCB.hcb_client_after_auth_skip /\
  CS.step_model
    w.PCB.hcb_server_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg2;
    }) == Some w.PCB.hcb_server_after2 /\
  CS.step_model
    w.PCB.hcb_client_after_auth_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg2;
    }) == Some w.PCB.hcb_client_after2 /\
  w.PCB.hcb_server_after2.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after_auth_skip.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after2.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_auth_skip.CS.model_record.CS.record_read /\
  CS.step_model
    w.PCB.hcb_client_after2
    (CS.ConnLocalEvent w.PCB.hcb_client_verify_skip) ==
    Some w.PCB.hcb_client_after_verify_skip /\
  CS.step_model
    w.PCB.hcb_server_after2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg3;
    }) == Some w.PCB.hcb_server_after3 /\
  CS.step_model
    w.PCB.hcb_client_after_verify_skip
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg3;
    }) == Some w.PCB.hcb_client_after3 /\
  w.PCB.hcb_server_after3.CS.model_record.CS.record_write ==
    R.next_seq w.PCB.hcb_server_after2.CS.model_record.CS.record_write /\
  w.PCB.hcb_client_after3.CS.model_record.CS.record_read ==
    R.next_seq w.PCB.hcb_client_after_verify_skip.CS.model_record.CS.record_read /\
  CS.conn_events_sent_seal_replay
    w.PCB.hcb_server_model5
    (PWL.server_encrypted_flight_replay_events
      w.PCB.hcb_server_material
      w.PCB.hcb_sent_msg0
      w.PCB.hcb_sent_msg1
      w.PCB.hcb_server_auth_skip
      w.PCB.hcb_sent_msg2
      w.PCB.hcb_sent_msg3
      r.sfr_server_flight_rest)
    r.sfr_server_raw_sent
    r.sfr_server_raw_received
    r.sfr_server_final /\
  CS.conn_events_received_decode_replay
    w.PCB.hcb_client_model4
    (PWL.client_receive_server_encrypted_flight_replay_events
      w.PCB.hcb_client_material
      w.PCB.hcb_received_msg0
      w.PCB.hcb_received_msg1
      w.PCB.hcb_client_auth_skip
      w.PCB.hcb_received_msg2
      w.PCB.hcb_client_verify_skip
      w.PCB.hcb_received_msg3
      r.sfr_client_flight_rest)
    r.sfr_client_raw_sent
    r.sfr_client_raw_received
    r.sfr_client_final

(**
  Current clean16 milestones do not yet expose enough information to construct
  the fragment above for an arbitrary [handshake_complete_boundary_witnesses].
  This predicate names the exact remaining fact needed to finish the
  server-flight part of the staged normalized boundary from those milestones.
**)
noextract
let clean16_server_encrypted_flight_semantic_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  PNB.paired_supported_normalized_replay_boundary_inputs client server w /\
  PNTSFS.clean16_server_encrypted_flight_staged_milestone client server ==>
  exists r.
    server_encrypted_flight_staged_replay_fragment client server w r

(**
  Actual server post-[ServerHello] sent/seal suffix obtained from the final
  clean16 server trace.  This is not yet the canonical
  [server_encrypted_flight_replay_events] fragment consumed by the staged
  backend: the first two events are kept in their observed order and related
  only by the write/read install cover.  It is the semantic replay source used
  by the next canonicalization step.
**)
noextract
let server_post_server_hello_sent_seal_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (rest:list CS.conn_event)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_sent_seal_replay
      model5
      (e5 :: e6 :: rest)
      suffix_sent
      suffix_received
      server.CS.cs_model

(**
  The same server sent/seal suffix with the nine-event post-install tail exposed
  in the exact order proved by [PairingNoTailServerPostHelloShape].  The first
  two post-[ServerHello] installs are still order-insensitive; this predicate is
  the precise case-split surface for the next replay canonicalization step.
**)
noextract
let server_post_server_hello_ordered_sent_seal_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          });
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        };
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
      ] in
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: ordered_rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_sent_seal_replay
      model5
      (e5 :: e6 :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model

(**
  Server post-[ServerHello] sent/seal suffix with just the two immediate
  handshake installs canonicalized to write-then-read.  The event log is still
  the observed no-tail log named by
  [server_post_server_hello_ordered_sent_seal_replay_slice]; this predicate only
  exposes an equivalent replay view for the same raw suffix, relying on the fact
  that both local install events have empty raw deltas.

  This is intentionally narrower than the staged-v2 ClientFinished split: the
  server handshake read install remains immediately after the write install,
  where it is a legal replay event.
**)
noextract
let server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_material:CS.traffic_key_material)
    (server_read_material:CS.traffic_key_material)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (server_after_write:CS.connection_model)
    (server_after_read:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let server_write_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          };
        }) in
    let server_read_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_read_material;
          };
        }) in
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          });
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        };
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
      ] in
    server_post_server_hello_ordered_sent_seal_replay_slice server /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.step_model model5 server_write_install == Some server_after_write /\
    CS.step_model server_after_write server_read_install == Some server_after_read /\
    CS.conn_events_sent_seal_replay
      model5
      (server_write_install :: server_read_install :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model

noextract
let server_after_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_material:CS.traffic_key_material)
    (server_read_material:CS.traffic_key_material)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (server_after_write:CS.connection_model)
    (server_after_read:CS.connection_model)
    (installed_suffix_sent:B.bytes)
    (installed_suffix_received:B.bytes).
    let server_write_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          };
        }) in
    let server_read_install =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_read_material;
          };
        }) in
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          });
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        };
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
      ] in
    CS.step_model model5 server_write_install == Some server_after_write /\
    CS.step_model server_after_write server_read_install == Some server_after_read /\
    CS.conn_events_sent_seal_replay
      server_after_read
      ordered_rest
      installed_suffix_sent
      installed_suffix_received
      server.CS.cs_model

val lemma_server_post_server_hello_sent_seal_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTSFS.clean16_server_encrypted_flight_staged_milestone client server /\
        CS.connection_state_sent_seal_replay_consistent server)
      (ensures server_post_server_hello_sent_seal_replay_slice server)

val lemma_server_post_server_hello_ordered_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_sent_seal_replay_slice server /\
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server)
      (ensures server_post_server_hello_ordered_sent_seal_replay_slice server)

val lemma_server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires server_post_server_hello_ordered_sent_seal_replay_slice server)
      (ensures
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server)

val lemma_server_after_handshake_installs_sent_seal_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
          server)
      (ensures server_after_handshake_installs_sent_seal_replay_slice server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_post_server_hello_sent_seal_replay_slice server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_post_server_hello_ordered_sent_seal_replay_slice server)

(**
  Server-side received/decode dual of the post-[ServerHello] sent/seal suffix.
  This is the semantic replay source for the server's protected
  [ClientFinished] receive path.
**)
noextract
let server_post_server_hello_received_decode_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (rest:list CS.conn_event)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_received_decode_replay
      model5
      (e5 :: e6 :: rest)
      suffix_sent
      suffix_received
      server.CS.cs_model

noextract
let server_post_server_hello_ordered_received_decode_replay_slice
  (server:CS.connection_state)
  : prop =
  exists
    (ch:GCH.clientHello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:GSH.serverHello)
    (e5:CS.conn_event)
    (e6:CS.conn_event)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material)
    (model5:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          });
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        };
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
      ] in
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: ordered_rest) /\
    PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model server.CS.cs_model.CS.model_config)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh)
      prefix_sent
      prefix_received
      model5 /\
    CS.conn_events_received_decode_replay
      model5
      (e5 :: e6 :: ordered_rest)
      suffix_sent
      suffix_received
      server.CS.cs_model

val lemma_server_post_server_hello_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTSFS.clean16_server_encrypted_flight_staged_milestone client server /\
        CS.connection_state_received_decode_replay_consistent server)
      (ensures server_post_server_hello_received_decode_replay_slice server)

val lemma_server_post_server_hello_ordered_received_decode_replay_slice
  (server:CS.connection_state)
  : Lemma
      (requires
        server_post_server_hello_received_decode_replay_slice server /\
        PNTPH.server_no_tail_post_two_handshake_installs_tail_order server)
      (ensures server_post_server_hello_ordered_received_decode_replay_slice server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_received_decode_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_post_server_hello_received_decode_replay_slice server)

val lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_received_decode_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_post_server_hello_ordered_received_decode_replay_slice server)

(**
  Client-side dual of [server_post_server_hello_sent_seal_replay_slice].  It
  splits the client's received/decode replay at the four-event cleartext prefix
  ending in [LocalDeriveSharedSecret].  The suffix is the observed clean16
  client post-derive tail, with the commuting handshake write/read install cover
  kept explicit.
**)
noextract
let client_post_derive_received_decode_replay_slice
  (client:CS.connection_state)
  : prop =
  exists
    (start:CS.handshake_start)
    (ch:GCH.clientHello)
    (sh:GSH.serverHello)
    (client_shared:C.x25519_shared_secret)
    (e4:CS.conn_event)
    (e5:CS.conn_event)
    (rest:list CS.conn_event)
    (model4:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    client.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start
          ch
          sh
          client_shared)
        (e4 :: e5 :: rest) /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared)
      prefix_sent
      prefix_received
      model4 /\
    CS.conn_events_received_decode_replay
      model4
      (e4 :: e5 :: rest)
      suffix_sent
      suffix_received
      client.CS.cs_model

(**
  Stronger client-side post-derive slice retaining the exact no-tail receive
  order after the two commuting handshake installs.  This is the client analogue
  of [server_post_server_hello_ordered_sent_seal_replay_slice] and is the
  case-split surface for canonicalizing the server encrypted-flight receiver
  replay.
**)
noextract
let client_post_derive_ordered_received_decode_replay_slice
  (client:CS.connection_state)
  : prop =
  exists
    (start:CS.handshake_start)
    (ch:GCH.clientHello)
    (sh:GSH.serverHello)
    (client_shared:C.x25519_shared_secret)
    (e4:CS.conn_event)
    (e5:CS.conn_event)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (peer:X.peer_identity)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (e13:CS.conn_event)
    (e14:CS.conn_event)
    (cf:GFin.finished)
    (model4:CS.connection_model)
    (prefix_sent:B.bytes)
    (prefix_received:B.bytes)
    (suffix_sent:B.bytes)
    (suffix_received:B.bytes).
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
        e13;
        e14;
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        }
      ] in
    client.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start
          ch
          sh
          client_shared)
        (e4 :: e5 :: ordered_rest) /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_received_decode_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared)
      prefix_sent
      prefix_received
      model4 /\
    CS.conn_events_received_decode_replay
      model4
      (e4 :: e5 :: ordered_rest)
      suffix_sent
      suffix_received
      client.CS.cs_model

(**
  Client-side replay view after the two post-[ServerHello] handshake traffic
  installs have both occurred.  The installs are still observed in the concrete
  no-tail order [e4; e5]; this predicate only peels them off the
  received/decode replay so the protected server-flight projection can start at
  the real already-installed receiver state.
**)
noextract
let client_after_handshake_installs_received_decode_replay_slice
  (client:CS.connection_state)
  : prop =
  exists
    (start:CS.handshake_start)
    (ch:GCH.clientHello)
    (sh:GSH.serverHello)
    (client_shared:C.x25519_shared_secret)
    (e4:CS.conn_event)
    (e5:CS.conn_event)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (peer:X.peer_identity)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (e13:CS.conn_event)
    (e14:CS.conn_event)
    (cf:GFin.finished)
    (model4:CS.connection_model)
    (client_after_e4:CS.connection_model)
    (client_after_installs:CS.connection_model)
    (installed_suffix_sent:B.bytes)
    (installed_suffix_received:B.bytes).
    let ordered_rest =
      [
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        };
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        };
        CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        };
        CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        };
        CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
        e13;
        e14;
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        }
      ] in
    client.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start
          ch
          sh
          client_shared)
        (e4 :: e5 :: ordered_rest) /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    CS.step_model model4 e4 == Some client_after_e4 /\
    CS.step_model client_after_e4 e5 == Some client_after_installs /\
    CS.conn_events_received_decode_replay
      client_after_installs
      ordered_rest
      installed_suffix_sent
      installed_suffix_received
      client.CS.cs_model

val lemma_client_post_derive_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailClientFinishedStaged.paired_no_tail_client_finished_staged_milestone
          client
          server /\
        CS.connection_state_received_decode_replay_consistent client)
      (ensures client_post_derive_received_decode_replay_slice client)

val lemma_client_post_derive_ordered_received_decode_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailClientFinishedStaged.paired_no_tail_client_finished_staged_milestone
          client
          server /\
        CS.connection_state_received_decode_replay_consistent client)
      (ensures client_post_derive_ordered_received_decode_replay_slice client)

val lemma_client_after_handshake_installs_received_decode_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_post_derive_ordered_received_decode_replay_slice client)
      (ensures client_after_handshake_installs_received_decode_replay_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_post_derive_received_decode_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures client_post_derive_received_decode_replay_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_post_derive_ordered_received_decode_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures client_post_derive_ordered_received_decode_replay_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_after_handshake_installs_received_decode_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        TLS13.Impl.Driver.PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures client_after_handshake_installs_received_decode_replay_slice client)

val lemma_server_encrypted_flight_staged_replay_fragment_from_normalized_replay_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)

val lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTSFS.clean16_server_encrypted_flight_staged_milestone
          client
          server /\
        clean16_server_encrypted_flight_semantic_replay_completion
          client
          server
          w)
      (ensures
        exists r.
          server_encrypted_flight_staged_replay_fragment client server w r)

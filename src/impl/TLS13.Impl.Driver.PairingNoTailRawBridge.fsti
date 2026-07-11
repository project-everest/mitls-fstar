module TLS13.Impl.Driver.PairingNoTailRawBridge

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CSL = TLS13.ConnectionState.Lemmas
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

(**
  Role-local cleartext prefixes with endpoint-local parsed values.

  The client and server ClientHello/ServerHello values are deliberately distinct:
  received hellos may retain parser-produced non-empty [body] bytes.
**)
noextract
let role_local_cleartext_prefix_shape
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
  (server_rest:list CS.conn_event)
  : prop =
  client.CS.cs_event_log ==
    CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
    }) ::
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
    }) ::
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
    client_rest /\
  server.CS.cs_event_log ==
    CS.ConnLocalEvent CS.LocalStartServer ::
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
    }) ::
    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
    }) ::
    server_rest

noextract
let normalized_cleartext_raw_wire_bridge
  (client_ch:GCH.clientHello)
  (server_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  : prop =
  exists
    (client_ch_raw:B.bytes)
    (server_ch_raw:B.bytes)
    (client_sh_raw:B.bytes)
    (server_sh_raw:B.bytes).
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
      client_sh_raw

val lemma_server_hello_key_share_from_sent_supported_and_received_projection
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (client_sh:GSH.serverHello)
  (server_sh:GSH.serverHello)
  (client_sh_raw:B.bytes)
  (server_sh_raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_server_hello_wire_profile server_sh /\
        CT.network_input_message_projection
          st0
          content_type
          fragment
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        Seq.equal server_sh_raw client_sh_raw)
      (ensures
        CS.server_hello_key_share client_sh ==
        CS.server_hello_key_share server_sh)

val lemma_sent_supported_client_hello_raw_not_change_cipher_spec
  (ch:GCH.clientHello)
  (client_hello_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          client_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal client_hello_raw ccs_raw)
      (ensures False)

val lemma_received_server_hello_raw_not_change_cipher_spec
  (sh:GSH.serverHello)
  (server_hello_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_server_hello_wire_profile sh /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          server_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal server_hello_raw ccs_raw)
      (ensures False)

val lemma_application_data_raw_not_change_cipher_spec
  (application_raw:B.bytes)
  (ccs_raw:B.bytes)
  : Lemma
      (requires
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw /\
        Seq.equal application_raw ccs_raw)
      (ensures False)

val lemma_equal_stream_head_sent_supported_client_hello_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (ch:GCH.clientHello)
  (client_hello_raw:B.bytes)
  (client_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append client_hello_raw client_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        WFL.supported_client_hello_wire_profile ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello ch))
          client_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)

val lemma_equal_stream_head_application_data_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (application_raw:B.bytes)
  (application_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append application_raw application_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)

val lemma_equal_stream_after_client_hello_application_data_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (sent_ch:GCH.clientHello)
  (received_ch:GCH.clientHello)
  (sent_ch_raw:B.bytes)
  (application_raw:B.bytes)
  (received_ch_raw:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append sent_ch_raw application_raw) /\
        Seq.equal
          right_stream
          (B.append received_ch_raw (B.append ccs_raw ccs_tail)) /\
        WFL.supported_client_hello_wire_profile sent_ch /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello sent_ch))
          sent_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello received_ch))
          received_ch_raw /\
        CS.raw_records_exactly application_raw T.Application_data 1 /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)

val lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (sh:GSH.serverHello)
  (server_hello_raw:B.bytes)
  (server_tail:B.bytes)
  (ccs_raw:B.bytes)
  (ccs_tail:B.bytes)
  : Lemma
      (requires
        WFL.supported_server_hello_wire_profile sh /\
        Seq.equal left_stream right_stream /\
        Seq.equal left_stream (B.append server_hello_raw server_tail) /\
        Seq.equal right_stream (B.append ccs_raw ccs_tail) /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello sh))
          server_hello_raw /\
        CS.cleartext_tls_message_raw
          M.TlsChangeCipherSpec
          ccs_raw)
      (ensures False)

val lemma_client_prefix_sent_client_hello_supported
  (model0:CS.connection_model)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        WFL.supported_client_config_wire_profile model0.CS.model_config /\
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           client_rest)
          raw_sent
          raw_received
          final_model)
      (ensures WFL.supported_client_hello_wire_profile client_ch)

val lemma_server_start_then_received_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw received_tail.
          Seq.equal raw_received (B.append ccs_raw received_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_select_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_select_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_select_shared_then_received_change_cipher_spec_raw_slices
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw ccs_raw received_tail.
          Seq.equal
            raw_received
            (B.append server_ch_raw (B.append ccs_raw received_tail)) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_server_start_client_hello_select_shared_then_sent_change_cipher_spec_raw_slice
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsChangeCipherSpec;
           }) ::
           rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists ccs_raw sent_tail.
          Seq.equal raw_sent (B.append ccs_raw sent_tail) /\
          CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw)

val lemma_client_prefix_raw_slices
  (model0:CS.connection_model)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           client_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists client_ch_raw client_sh_raw sent_tail received_tail.
          Seq.equal raw_sent (B.append client_ch_raw sent_tail) /\
          Seq.equal raw_received (B.append client_sh_raw received_tail) /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello client_ch))
            client_ch_raw /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello client_sh))
            client_sh_raw)

val lemma_client_cleartext_prefix_step_models_from_raw_replay
  (model0:CS.connection_model)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           client_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 model2 model3 model4 tail_sent tail_received.
          CS.step_model
            model0
            (CS.ConnLocalEvent (CS.LocalStartHandshake client_start)) ==
            Some model1 /\
          CS.step_model
            model1
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
            })) == Some model2 /\
          CS.step_model
            model2
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
            })) == Some model3 /\
          CS.step_model
            model3
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
            Some model4 /\
          CS.conn_events_raw_replay
            model4
            client_rest
            tail_sent
            tail_received
            final_model)

val lemma_client_cleartext_prefix_final_hello_slots_from_raw_replay
  (model0:CS.connection_model)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
           }) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
           }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           client_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        final_model.CS.model_handshake.CS.hs_client_hello ==
          Some client_ch /\
        final_model.CS.model_handshake.CS.hs_server_hello ==
          Some client_sh)

val lemma_server_prefix_raw_slices
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
  (server_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
           }) ::
           server_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists server_ch_raw server_sh_raw sent_tail received_tail.
          Seq.equal raw_received (B.append server_ch_raw received_tail) /\
          Seq.equal raw_sent (B.append server_sh_raw sent_tail) /\
          CS.received_cleartext_tls_message_raw
            (M.TlsHandshake (M.ClientHello server_ch))
            server_ch_raw /\
          CS.cleartext_tls_message_raw
            (M.TlsHandshake (M.ServerHello server_sh))
            server_sh_raw)

val lemma_server_cleartext_prefix_step_models_from_raw_replay
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
  (server_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
           }) ::
           server_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        exists model1 model2 model3 model4 model5 tail_sent tail_received.
          CS.step_model
            model0
            (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
          CS.step_model
            model1
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
            })) == Some model2 /\
          CS.step_model
            model2
            (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
            Some model3 /\
          CS.step_model
            model3
            (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
            Some model4 /\
          CS.step_model
            model4
            (CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
            })) == Some model5 /\
          CS.conn_events_raw_replay
            model5
            server_rest
            tail_sent
            tail_received
            final_model)

val lemma_server_cleartext_prefix_final_hello_slots_from_raw_replay
  (model0:CS.connection_model)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
  (server_rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_raw_replay
          model0
          (CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
           }) ::
           server_rest)
          raw_sent
          raw_received
          final_model)
      (ensures
        final_model.CS.model_handshake.CS.hs_client_hello ==
          Some server_ch /\
        final_model.CS.model_handshake.CS.hs_server_hello ==
          Some server_sh)

val lemma_normalized_cleartext_raw_wire_bridge_from_role_local_prefixes
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        role_local_cleartext_prefix_shape
          client
          server
          client_start
          client_ch
          client_sh
          client_shared
          client_rest
          server_ch
          selection
          server_shared
          server_sh
          server_rest /\
        WFL.supported_client_hello_wire_profile client_ch /\
        WFL.supported_server_hello_wire_profile server_sh /\
        WFL.supported_server_hello_wire_profile client_sh /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        CS.paired_wire_logs client server)
      (ensures
        normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh)

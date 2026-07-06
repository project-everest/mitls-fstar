module TLS13.Impl.Driver.PairingNoTailRawBridge

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Seq = FStar.Seq
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
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
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
  (client_ch:M.client_hello)
  (server_ch:M.client_hello)
  (client_sh:M.server_hello)
  (server_sh:M.server_hello)
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

val lemma_normalized_cleartext_raw_wire_bridge_from_role_local_prefixes
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
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
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        CS.paired_wire_logs client server)
      (ensures
        normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh)

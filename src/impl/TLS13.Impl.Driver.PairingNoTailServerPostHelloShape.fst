module TLS13.Impl.Driver.PairingNoTailServerPostHelloShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module ListP = FStar.List.Tot.Properties
module M = TLS13.Messages
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

#push-options "--split_queries always"

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
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
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures server_no_tail_post_server_hello_suffix_shape server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (FStar.List.Tot.length server.CS.cs_event_log == 16);
  eliminate exists client_start client_ch client_sh client_shared e4 e5 client_rest.
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
        e4 ::
        e5 ::
        client_rest /\
    TLS13.Impl.Driver.PairingNoTailInversion.client_no_tail_handshake_traffic_install_event e4 /\
    TLS13.Impl.Driver.PairingNoTailInversion.client_no_tail_handshake_traffic_install_event e5
  returns server_no_tail_post_server_hello_suffix_shape server
  with _.
  (
    eliminate exists server_ch selection server_shared server_sh server_rest.
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
    returns server_no_tail_post_server_hello_suffix_shape server
    with _.
    (
      let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
      let server_ev1 =
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) in
      let server_ev2 =
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
      let server_ev3 =
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
      let server_ev4 =
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        }) in
      let server_prefix : list CS.conn_event =
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
      ListP.append_cons_l
        server_ev0
        (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev1
        (server_ev2 :: server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev2
        (server_ev3 :: server_ev4 :: [])
        server_rest;
      ListP.append_cons_l
        server_ev3
        (server_ev4 :: [])
        server_rest;
      ListP.append_cons_l server_ev4 [] server_rest;
      ListP.append_nil_l server_rest;
      assert (FStar.List.Tot.append server_prefix server_rest ==
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
        server_rest);
      assert (server.CS.cs_event_log ==
        server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
        server_rest);
      assert (server_prefix ==
        PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh);
      ListP.append_length server_prefix server_rest;
      assert_norm
        (FStar.List.Tot.length
          (server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: []) == 5);
      assert (FStar.List.Tot.length server_prefix == 5);
      assert (
        server.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.server_cleartext_handshake_prefix_events
              server_ch
              selection
              server_shared
              server_sh)
            server_rest);
      assert (FStar.List.Tot.length server_rest == 11);
      match server_rest with
      | e5 :: e6 :: rest ->
        assert (FStar.List.Tot.length rest == 9);
        assert (server_no_tail_post_server_hello_suffix_shape server)
      | _ ->
        assert False
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape_with_start_spine16
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
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        server_no_tail_post_server_hello_suffix_shape_with_start_spine16
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_start_spine16 server

#pop-options

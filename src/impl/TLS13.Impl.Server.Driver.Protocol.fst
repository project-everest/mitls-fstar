module TLS13.Impl.Server.Driver.Protocol

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CP = Common.Protocol
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.ConnectionState
module D = TLS13.Impl.Server.Driver
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module TCP = Common.TCP
module TLSP = TLS13.Protocol
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq
type server_network_args = {
  server_network_out: array U8.t;
  server_network_out_len: SZ.t;
  server_network_local_fuel: SZ.t;
  server_network_fuel: SZ.t;
  server_network_st0: Ghost.erased CS.connection_state;
  server_network_tcp0: Ghost.erased TCP.history;
}

noeq
type server_local_args = {
  server_local_payload: array U8.t;
  server_local_payload_len: SZ.t;
  server_local_st0: Ghost.erased CS.connection_state;
  server_local_tcp0: Ghost.erased TCP.history;
}

let server_driver_transport_matches
  (tcp:TCP.history)
  (st:CS.connection_state)
  : prop =
  exists buffered buffered_len.
    D.server_driver_wire_logs_match
      st
      tcp.TCP.tcp_received
      tcp.TCP.tcp_sent
      buffered
      buffered_len

let server_protocol_valid (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  ST.server_end_to_end_invariant st

let lemma_server_protocol_valid_layers
  (st:CS.connection_state)
  : Lemma
      (requires server_protocol_valid st)
      (ensures
        TLSP.tls_record_wire_format.CP.wf_history_matches
          (TLSP.tls_processed_history st)
          (TLSP.tls_wire_log st) /\
        TLSP.tls_transport_exact
          (TLSP.tls_processed_history st)
          st /\
        TLSP.tls_events_refine_wire st /\
        ST.server_end_to_end_invariant st)
  =
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (ST.server_state_correct st);
  assert (ST.server_state_core_correct st);
  assert (ST.server_raw_to_message_replay_consistent st);
  assert (CS.connection_state_full_log_consistent_for_role CS.ServerEndpoint st);
  assert (CS.connection_state_full_log_consistent_for_config_role st);
  assert (CS.connection_state_raw_event_replay_consistent st);
  assert (TLSP.tls_events_refine_wire st);
  TLSP.lemma_tls_state_valid_exact_intro st

noextract
let tls_server_protocol
  : CP.state_machine_protocol
      CS.connection_state
      M.tls_record
      CS.conn_event
  =
  {
    CP.sm_wire_format = TLSP.tls_record_wire_format;
    CP.sm_processed_history = TLSP.tls_processed_history;
    CP.sm_wire_log = TLSP.tls_wire_log;
    CP.sm_event_log = TLSP.tls_event_log;
    CP.sm_transport_matches = TLSP.tls_transport_exact;
    CP.sm_events_refine_wire = TLSP.tls_events_refine_wire;
    CP.sm_step = TLSP.tls_step_relation;
    CP.sm_invariant = ST.server_end_to_end_invariant;
    CP.sm_valid = server_protocol_valid;
    CP.sm_valid_implies_layers = lemma_server_protocol_valid_layers;
  }

noextract
let server_driver_tcp_channel
  (_d:D.server_driver)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
let server_driver_ghost_log
  (_d:D.server_driver)
  (st:CS.connection_state)
  : slprop =
  pure (server_protocol_valid st)

noextract
let server_driver_runtime_resources
  (_d:D.server_driver)
  (_st:CS.connection_state)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
[@@pulse_unfold]
let server_driver_invariant
  (d:D.server_driver)
  (st:CS.connection_state)
  (tcp:TCP.history)
  : slprop =
  exists* certificate_chain credential_identity.
    D.server_driver_connected
      d
      st
      certificate_chain
      credential_identity
      tcp.TCP.tcp_received
      tcp.TCP.tcp_sent

let server_driver_invariant_correct
  (st:CS.connection_state)
  (tcp:TCP.history)
  : GTot prop =
  server_protocol_valid st /\
  server_driver_transport_matches tcp st

let server_tcp_history_matches
  (tcp:TCP.history)
  (st:CS.connection_state)
  : GTot prop =
  D.server_driver_sent_log_exact st tcp.TCP.tcp_sent /\
  D.server_driver_received_log_accounted st tcp.TCP.tcp_received

let server_network_args_state
  (args:server_network_args)
  : GTot CS.connection_state =
  Ghost.reveal args.server_network_st0

let server_network_args_tcp
  (args:server_network_args)
  : GTot TCP.history =
  Ghost.reveal args.server_network_tcp0

let server_local_args_state
  (args:server_local_args)
  : GTot CS.connection_state =
  Ghost.reveal args.server_local_st0

let server_local_args_tcp
  (args:server_local_args)
  : GTot TCP.history =
  Ghost.reveal args.server_local_tcp0

noextract
[@@pulse_unfold]
let server_network_frame
  (d:D.server_driver)
  (args:server_network_args)
  : slprop =
  exists* (old_out: Ghost.erased B.bytes).
    pts_to args.server_network_out old_out **
    pure (B.length (Ghost.reveal old_out) == SZ.v args.server_network_out_len)

noextract
[@@pulse_unfold]
let server_network_extra_post
  (d:D.server_driver)
  (args:server_network_args)
  (result:D.server_receive_result)
  (st1:CS.connection_state)
  (tcp1:TCP.history)
  : slprop =
  let st0 = Ghost.reveal args.server_network_st0 in
  let tcp0 = Ghost.reveal args.server_network_tcp0 in
  exists* out_bytes.
    pts_to args.server_network_out out_bytes **
    pure (
      B.length out_bytes == SZ.v args.server_network_out_len /\
      SZ.v result.D.server_receive_len <= SZ.v args.server_network_out_len /\
      st1.CS.cs_model.CS.model_config ==
        st0.CS.cs_model.CS.model_config /\
      D.server_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
      D.server_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
      D.server_driver_sent_log_exact st1 tcp1.TCP.tcp_sent /\
      D.server_driver_received_log_accounted st1 tcp1.TCP.tcp_received /\
      (exists loop app_out.
        D.server_driver_receive_correct
          st0
          st1
          result
          loop
          tcp0.TCP.tcp_sent
          tcp1.TCP.tcp_sent
          app_out
          out_bytes))

let server_network_effect
  (args:server_network_args)
  (result:D.server_receive_result)
  (st0:CS.connection_state)
  (tcp0:TCP.history)
  (st1:CS.connection_state)
  (tcp1:TCP.history)
  : GTot prop =
  st1.CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config /\
  D.server_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
  D.server_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
  D.server_driver_sent_log_exact st1 tcp1.TCP.tcp_sent /\
  D.server_driver_received_log_accounted st1 tcp1.TCP.tcp_received /\
  (exists out_bytes loop app_out.
    D.server_driver_receive_correct
      st0
      st1
      result
      loop
      tcp0.TCP.tcp_sent
      tcp1.TCP.tcp_sent
      app_out
      out_bytes)

noextract
[@@pulse_unfold]
let server_network_pre
  (d:D.server_driver)
  (args:server_network_args)
  : slprop =
  let st0 = server_network_args_state args in
  let tcp0 = server_network_args_tcp args in
  server_driver_invariant d st0 tcp0 **
  server_network_frame d args **
  pure (CPI.protocol_state_transport
    tls_server_protocol
    server_tcp_history_matches
    tcp0
    st0)

noextract
[@@pulse_unfold]
let server_network_post
  (d:D.server_driver)
  (args:server_network_args)
  (result:D.server_receive_result)
  : slprop =
  let st0 = server_network_args_state args in
  let tcp0 = server_network_args_tcp args in
  exists* (st1: Ghost.erased CS.connection_state) (tcp1: Ghost.erased TCP.history).
    server_driver_invariant d (Ghost.reveal st1) (Ghost.reveal tcp1) **
    server_network_extra_post
      d
      args
      result
      (Ghost.reveal st1)
      (Ghost.reveal tcp1) **
    pure (
      CPI.protocol_network_step
        tls_server_protocol
        server_tcp_history_matches
        st0
        tcp0
        (Ghost.reveal st1)
        (Ghost.reveal tcp1) /\
      server_network_effect
        args
        result
        st0
        tcp0
        (Ghost.reveal st1)
        (Ghost.reveal tcp1))

noextract
[@@pulse_unfold]
let server_local_frame
  (d:D.server_driver)
  (args:server_local_args)
  : slprop =
  let st0 = Ghost.reveal args.server_local_st0 in
  exists* (payload_bytes: Ghost.erased B.bytes).
    pts_to args.server_local_payload payload_bytes **
    pure (
      B.length (Ghost.reveal payload_bytes) == SZ.v args.server_local_payload_len /\
      ST.server_local_event_input_ready
        st0
        ST.LocalSendApplicationData
        (Ghost.reveal payload_bytes))

noextract
[@@pulse_unfold]
let server_local_extra_post
  (d:D.server_driver)
  (args:server_local_args)
  (status:D.server_workflow_status)
  (st1:CS.connection_state)
  (tcp1:TCP.history)
  : slprop =
  let st0 = Ghost.reveal args.server_local_st0 in
  let tcp0 = Ghost.reveal args.server_local_tcp0 in
  exists* (payload_bytes: Ghost.erased B.bytes).
      pts_to args.server_local_payload payload_bytes **
      pure (
        D.server_driver_send_correct
          st0
          st1
          status
          (Ghost.reveal payload_bytes)
          tcp0.TCP.tcp_sent
          tcp1.TCP.tcp_sent /\
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config /\
        D.server_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
        D.server_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
        D.server_driver_sent_log_exact st1 tcp1.TCP.tcp_sent /\
        D.server_driver_received_log_accounted st1 tcp1.TCP.tcp_received)

let server_local_effect
  (args:server_local_args)
  (status:D.server_workflow_status)
  (st0:CS.connection_state)
  (tcp0:TCP.history)
  (st1:CS.connection_state)
  (tcp1:TCP.history)
  : GTot prop =
  st1.CS.cs_model.CS.model_config ==
    st0.CS.cs_model.CS.model_config /\
  D.server_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
  D.server_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
  D.server_driver_sent_log_exact st1 tcp1.TCP.tcp_sent /\
  D.server_driver_received_log_accounted st1 tcp1.TCP.tcp_received /\
  (exists payload.
    D.server_driver_send_correct
      st0
      st1
      status
      payload
      tcp0.TCP.tcp_sent
      tcp1.TCP.tcp_sent)

noextract
[@@pulse_unfold]
let server_local_pre
  (d:D.server_driver)
  (args:server_local_args)
  : slprop =
  let st0 = server_local_args_state args in
  let tcp0 = server_local_args_tcp args in
  server_driver_invariant d st0 tcp0 **
  server_local_frame d args **
  pure (CPI.protocol_state_transport
    tls_server_protocol
    server_tcp_history_matches
    tcp0
    st0)

noextract
[@@pulse_unfold]
let server_local_post
  (d:D.server_driver)
  (args:server_local_args)
  (status:D.server_workflow_status)
  : slprop =
  let st0 = server_local_args_state args in
  let tcp0 = server_local_args_tcp args in
  exists* (st1: Ghost.erased CS.connection_state) (tcp1: Ghost.erased TCP.history).
    server_driver_invariant d (Ghost.reveal st1) (Ghost.reveal tcp1) **
    server_local_extra_post
      d
      args
      status
      (Ghost.reveal st1)
      (Ghost.reveal tcp1) **
    pure (
      CPI.protocol_local_step
        tls_server_protocol
        server_tcp_history_matches
        st0
        tcp0
        (Ghost.reveal st1)
        (Ghost.reveal tcp1) /\
      server_local_effect
        args
        status
        st0
        tcp0
        (Ghost.reveal st1)
        (Ghost.reveal tcp1))

fn server_process_network
  (d:D.server_driver)
  (args:server_network_args)
requires server_network_pre d args
returns result: D.server_receive_result
ensures server_network_post d args result
{
  unfold (server_network_pre d args);
  unfold (server_network_frame d args);
  with old_out. _;
  unfold (server_driver_invariant d args.server_network_st0 args.server_network_tcp0);
  with certificate_chain credential_identity. _;
  let result =
    D.receive
      d
      args.server_network_out
      args.server_network_out_len
      args.server_network_local_fuel
      args.server_network_fuel;
  with st1 received1 sent1 out_bytes. _;
  let st1e = Ghost.hide st1;
  let tcp1 = Ghost.hide { TCP.tcp_received = received1; TCP.tcp_sent = sent1 };
  assert (pure (Ghost.reveal st1e == st1));
  assert (pure (Ghost.reveal tcp1 ==
    { TCP.tcp_received = received1; TCP.tcp_sent = sent1 }));
  TLSP.lemma_tls_wire_history_matches_processed st1;
  assert (pure (CPI.protocol_state_transport
    tls_server_protocol
    server_tcp_history_matches
    (Ghost.reveal tcp1)
    (Ghost.reveal st1e)));
  rewrite
    (D.server_driver_connected
      d
      st1
      certificate_chain
      credential_identity
      received1
      sent1)
    as
    (D.server_driver_connected
      d
      (Ghost.reveal st1e)
      certificate_chain
      credential_identity
      (Ghost.reveal tcp1).TCP.tcp_received
      (Ghost.reveal tcp1).TCP.tcp_sent);
  with certificate_chain credential_identity.
  fold (server_driver_invariant
    d
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1));
  with out_bytes. fold (server_network_extra_post
    d
    args
    result
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1));
  assert (pure (server_network_effect
    args
    result
    args.server_network_st0
    args.server_network_tcp0
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1)));
  assert (pure (CPI.protocol_network_step
    tls_server_protocol
    server_tcp_history_matches
    args.server_network_st0
    args.server_network_tcp0
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1)));
  with st1e tcp1.
  fold (server_network_post d args result);
  result
}

fn server_process_local
  (d:D.server_driver)
  (args:server_local_args)
requires server_local_pre d args
returns status: D.server_workflow_status
ensures server_local_post d args status
{
  unfold (server_local_pre d args);
  unfold (server_local_frame d args);
  with payload_bytes. _;
  unfold (server_driver_invariant d args.server_local_st0 args.server_local_tcp0);
  with certificate_chain credential_identity. _;
  let status =
    D.send
      d
      args.server_local_payload
      args.server_local_payload_len;
  with st1 sent1. _;
  let st1e = Ghost.hide st1;
  let tcp1 =
    Ghost.hide
      { TCP.tcp_received = args.server_local_tcp0.TCP.tcp_received;
        TCP.tcp_sent = sent1 };
  assert (pure (Ghost.reveal st1e == st1));
  assert (pure (Ghost.reveal tcp1 ==
    { TCP.tcp_received = args.server_local_tcp0.TCP.tcp_received;
      TCP.tcp_sent = sent1 }));
  TLSP.lemma_tls_wire_history_matches_processed st1;
  assert (pure (CPI.protocol_state_transport
    tls_server_protocol
    server_tcp_history_matches
    (Ghost.reveal tcp1)
    (Ghost.reveal st1e)));
  rewrite
    (D.server_driver_connected
      d
      st1
      certificate_chain
      credential_identity
      args.server_local_tcp0.TCP.tcp_received
      sent1)
    as
    (D.server_driver_connected
      d
      (Ghost.reveal st1e)
      certificate_chain
      credential_identity
      (Ghost.reveal tcp1).TCP.tcp_received
      (Ghost.reveal tcp1).TCP.tcp_sent);
  with certificate_chain credential_identity.
  fold (server_driver_invariant
    d
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1));
  with payload_bytes. fold (server_local_extra_post
    d
    args
    status
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1));
  assert (pure (server_local_effect
    args
    status
    args.server_local_st0
    args.server_local_tcp0
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1)));
  assert (pure (CPI.protocol_local_step
    tls_server_protocol
    server_tcp_history_matches
    args.server_local_st0
    args.server_local_tcp0
    (Ghost.reveal st1e)
    (Ghost.reveal tcp1)));
  with st1e tcp1.
  fold (server_local_post d args status);
  status
}

noextract
let tls_server_driver_protocol_implementation
  : CPI.protocol_implementation
      D.server_driver
      CS.connection_state
      M.tls_record
      CS.conn_event
      server_network_args
      D.server_receive_result
      server_local_args
      D.server_workflow_status
  =
  {
    CPI.pi_protocol = tls_server_protocol;
    CPI.pi_parse_network = TLSP.tls_parse_network;
    CPI.pi_serialize_network = TLSP.tls_serialize_network;
    CPI.pi_serialized_network = TLSP.tls_serialized_network;
    CPI.pi_parse_network_correct = TLSP.lemma_tls_parse_network_correct;
    CPI.pi_serialize_network_correct = TLSP.lemma_tls_serialize_network_correct;
    CPI.pi_tcp_channel = server_driver_tcp_channel;
    CPI.pi_ghost_log = server_driver_ghost_log;
    CPI.pi_runtime_resources = server_driver_runtime_resources;
    CPI.pi_invariant = server_driver_invariant;
    CPI.pi_tcp_history_matches = server_tcp_history_matches;
    CPI.pi_network_args_state = server_network_args_state;
    CPI.pi_network_args_tcp = server_network_args_tcp;
    CPI.pi_local_args_state = server_local_args_state;
    CPI.pi_local_args_tcp = server_local_args_tcp;
    CPI.pi_network_frame = server_network_frame;
    CPI.pi_network_extra_post = server_network_extra_post;
    CPI.pi_network_effect = server_network_effect;
    CPI.pi_local_frame = server_local_frame;
    CPI.pi_local_extra_post = server_local_extra_post;
    CPI.pi_local_effect = server_local_effect;
    CPI.pi_process_network = server_process_network;
    CPI.pi_process_local = server_process_local;
  }

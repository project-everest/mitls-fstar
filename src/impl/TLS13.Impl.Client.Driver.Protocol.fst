module TLS13.Impl.Client.Driver.Protocol

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CP = Common.Protocol
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Driver
module M = TLS13.Messages
module TCP = Common.TCP
module TLSP = TLS13.Protocol
module SZ = FStar.SizeT
module U8 = FStar.UInt8

noeq
type client_network_args = {
  client_network_out: array U8.t;
  client_network_out_len: SZ.t;
  client_network_local_fuel: SZ.t;
  client_network_fuel: SZ.t;
  client_network_st0: Ghost.erased CS.connection_state;
  client_network_tcp0: Ghost.erased TCP.history;
}

noeq
type client_local_args = {
  client_local_payload: array U8.t;
  client_local_payload_len: SZ.t;
  client_local_st0: Ghost.erased CS.connection_state;
  client_local_tcp0: Ghost.erased TCP.history;
}

let client_driver_transport_matches
  (tcp:TCP.history)
  (st:CS.connection_state)
  : prop =
  exists buffered buffered_len.
    D.client_driver_wire_logs_match
      st
      tcp.TCP.tcp_received
      tcp.TCP.tcp_sent
      buffered
      buffered_len

let client_protocol_valid (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  CT.client_end_to_end_invariant st

let lemma_client_protocol_valid_layers
  (st:CS.connection_state)
  : Lemma
      (requires client_protocol_valid st)
      (ensures
        TLSP.tls_record_wire_format.CP.wf_history_matches
          (TLSP.tls_processed_history st)
          (TLSP.tls_wire_log st) /\
        TLSP.tls_transport_exact
          (TLSP.tls_processed_history st)
          st /\
        TLSP.tls_events_refine_wire st /\
        CT.client_end_to_end_invariant st)
  =
  TLSP.lemma_tls_state_valid_exact_intro st

noextract
let tls_client_protocol
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
    CP.sm_invariant = CT.client_end_to_end_invariant;
    CP.sm_valid = client_protocol_valid;
    CP.sm_valid_implies_layers = lemma_client_protocol_valid_layers;
  }

noextract
let client_driver_tcp_channel
  (_d:D.client_driver)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
let client_driver_ghost_log
  (_d:D.client_driver)
  (st:CS.connection_state)
  : slprop =
  pure (client_protocol_valid st)

noextract
let client_driver_runtime_resources
  (_d:D.client_driver)
  (_st:CS.connection_state)
  (_tcp:TCP.history)
  : slprop =
  emp

noextract
[@@pulse_unfold]
let client_driver_invariant
  (d:D.client_driver)
  (st:CS.connection_state)
  (tcp:TCP.history)
  : slprop =
  D.client_driver_connected d st tcp.TCP.tcp_received tcp.TCP.tcp_sent

let client_driver_invariant_correct
  (st:CS.connection_state)
  (tcp:TCP.history)
  : GTot prop =
  client_protocol_valid st /\
  client_driver_transport_matches tcp st

noextract
[@@pulse_unfold]
let client_network_pre
  (d:D.client_driver)
  (args:client_network_args)
  : slprop =
  let st0 = Ghost.reveal args.client_network_st0 in
  let tcp0 = Ghost.reveal args.client_network_tcp0 in
  client_driver_invariant d st0 tcp0 **
  exists* (old_out: Ghost.erased B.bytes).
    pts_to args.client_network_out old_out **
    pure (B.length (Ghost.reveal old_out) == SZ.v args.client_network_out_len)

noextract
[@@pulse_unfold]
let client_network_post
  (d:D.client_driver)
  (args:client_network_args)
  (result:D.client_receive_result)
  : slprop =
  let st0 = Ghost.reveal args.client_network_st0 in
  let tcp0 = Ghost.reveal args.client_network_tcp0 in
  exists* st1 received1 sent1 out_bytes.
    client_driver_invariant
      d
      st1
      { TCP.tcp_received = received1; TCP.tcp_sent = sent1 } **
    pts_to args.client_network_out out_bytes **
    pure (
      B.length out_bytes == SZ.v args.client_network_out_len /\
      SZ.v result.D.client_receive_len <= SZ.v args.client_network_out_len /\
      st1.CS.cs_model.CS.model_config ==
        st0.CS.cs_model.CS.model_config /\
      D.client_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
      D.client_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
      D.client_driver_sent_log_exact st1 sent1 /\
      D.client_driver_received_log_accounted st1 received1 /\
      (exists obs app_out.
        D.client_driver_receive_correct
          st0
          st1
          result
          obs
          app_out
          out_bytes))

noextract
[@@pulse_unfold]
let client_local_pre
  (d:D.client_driver)
  (args:client_local_args)
  : slprop =
  let st0 = Ghost.reveal args.client_local_st0 in
  let tcp0 = Ghost.reveal args.client_local_tcp0 in
  client_driver_invariant d st0 tcp0 **
  exists* (payload_bytes: Ghost.erased B.bytes).
    pts_to args.client_local_payload payload_bytes **
    pure (
      B.length (Ghost.reveal payload_bytes) == SZ.v args.client_local_payload_len /\
      CT.local_input_wf
        st0
        CT.LocalSendApplicationData
        (Ghost.reveal payload_bytes))

noextract
[@@pulse_unfold]
let client_local_post
  (d:D.client_driver)
  (args:client_local_args)
  (status:D.driver_workflow_status)
  : slprop =
  let st0 = Ghost.reveal args.client_local_st0 in
  let tcp0 = Ghost.reveal args.client_local_tcp0 in
  exists* st1 received1 sent1.
    client_driver_invariant
      d
      st1
      { TCP.tcp_received = received1; TCP.tcp_sent = sent1 } **
    exists* (payload_bytes: Ghost.erased B.bytes).
      pts_to args.client_local_payload payload_bytes **
      pure (
        D.client_driver_send_correct
          st0
          st1
          status
          (Ghost.reveal payload_bytes)
          tcp0.TCP.tcp_sent
          sent1 /\
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config /\
        D.client_driver_sent_log_exact st0 tcp0.TCP.tcp_sent /\
        D.client_driver_received_log_accounted st0 tcp0.TCP.tcp_received /\
        D.client_driver_sent_log_exact st1 sent1 /\
        D.client_driver_received_log_accounted st1 received1)

fn client_process_network
  (d:D.client_driver)
  (args:client_network_args)
requires client_network_pre d args
returns result: D.client_receive_result
ensures client_network_post d args result
{
  unfold (client_network_pre d args);
  unfold (client_driver_invariant d args.client_network_st0 args.client_network_tcp0);
  let result =
    D.receive
      d
      args.client_network_out
      args.client_network_out_len
      args.client_network_local_fuel
      args.client_network_fuel;
  with st1 received1 sent1 out_bytes. _;
  fold (client_driver_invariant
    d
    st1
    { TCP.tcp_received = received1; TCP.tcp_sent = sent1 });
  with st1 received1 sent1 out_bytes.
  fold (client_network_post d args result);
  result
}

fn client_process_local
  (d:D.client_driver)
  (args:client_local_args)
requires client_local_pre d args
returns status: D.driver_workflow_status
ensures client_local_post d args status
{
  unfold (client_local_pre d args);
  unfold (client_driver_invariant d args.client_local_st0 args.client_local_tcp0);
  let status =
    D.send
      d
      args.client_local_payload
      args.client_local_payload_len;
  with st1 received1 sent1. _;
  fold (client_driver_invariant
    d
    st1
    { TCP.tcp_received = received1; TCP.tcp_sent = sent1 });
  with st1 received1 sent1.
  fold (client_local_post d args status);
  status
}

let client_network_signature
  (d:D.client_driver)
  (args:client_network_args)
  : GTot Type0 =
  stt D.client_receive_result
    (client_network_pre d args)
    (client_network_post d args)

let client_local_signature
  (d:D.client_driver)
  (args:client_local_args)
  : GTot Type0 =
  stt D.driver_workflow_status
    (client_local_pre d args)
    (client_local_post d args)

noextract
let tls_client_driver_protocol_implementation
  : CPI.protocol_implementation
      D.client_driver
      CS.connection_state
      M.tls_record
      CS.conn_event
      client_network_args
      D.client_receive_result
      client_local_args
      D.driver_workflow_status
  =
  {
    CPI.pi_protocol = tls_client_protocol;
    CPI.pi_parse_network = TLSP.tls_parse_network;
    CPI.pi_serialize_network = TLSP.tls_serialize_network;
    CPI.pi_serialized_network = TLSP.tls_serialized_network;
    CPI.pi_parse_network_correct = TLSP.lemma_tls_parse_network_correct;
    CPI.pi_serialize_network_correct = TLSP.lemma_tls_serialize_network_correct;
    CPI.pi_tcp_channel = client_driver_tcp_channel;
    CPI.pi_ghost_log = client_driver_ghost_log;
    CPI.pi_runtime_resources = client_driver_runtime_resources;
    CPI.pi_invariant = client_driver_invariant;
    CPI.pi_invariant_correct = client_driver_invariant_correct;
    CPI.pi_network_pre = client_network_pre;
    CPI.pi_network_post = client_network_post;
    CPI.pi_local_pre = client_local_pre;
    CPI.pi_local_post = client_local_post;
    CPI.pi_network_signature = client_network_signature;
    CPI.pi_local_signature = client_local_signature;
  }

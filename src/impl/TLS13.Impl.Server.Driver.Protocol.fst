module TLS13.Impl.Server.Driver.Protocol

#lang-pulse

open Pulse.Lib.Pervasives

module CP = Common.Protocol
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.ConnectionState
module D = TLS13.Impl.Server.Driver
module M = TLS13.Messages
module ST = TLS13.Impl.Server.Types
module TCP = Common.TCP
module TLSP = TLS13.Protocol
module SZ = FStar.SizeT

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
let server_driver_represents
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
      tcp.TCP.tcp_sent **
    pure (
      server_protocol_valid st /\
      server_driver_transport_matches tcp st
    )

noextract
let tls_server_driver_protocol_implementation
  : CPI.protocol_implementation
      D.server_driver
      CS.connection_state
      M.tls_record
      CS.conn_event
  =
  {
    CPI.pi_protocol = tls_server_protocol;
    CPI.pi_represents = server_driver_represents;
  }

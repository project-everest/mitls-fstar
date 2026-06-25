module TLS13.Impl.Client.Driver.Protocol

#lang-pulse

open Pulse.Lib.Pervasives

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
let client_driver_represents
  (d:D.client_driver)
  (st:CS.connection_state)
  (tcp:TCP.history)
  : slprop =
  D.client_driver_connected d st tcp.TCP.tcp_received tcp.TCP.tcp_sent **
  pure (
    client_protocol_valid st /\
    client_driver_transport_matches tcp st
  )

noextract
let tls_client_driver_protocol_implementation
  : CPI.protocol_implementation
      D.client_driver
      CS.connection_state
      M.tls_record
      CS.conn_event
  =
  {
    CPI.pi_protocol = tls_client_protocol;
    CPI.pi_represents = client_driver_represents;
  }

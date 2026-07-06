module TLS13.Impl.Driver.PairingNoTailWireLogs

module B = TLS13.Bytes
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.ConnectionState
module CW = TLS13.Impl.CanonicalWire
module CTypes = TLS13.Impl.CanonicalTypes
module L = FStar.List.Tot
module Seq = FStar.Seq
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module SM = Common.StateMachine
module TCP = Common.TCP
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine

val lemma_wire_parses_as_serialize_with_tail
  (bytes:B.bytes)
  (msgs:list CW.wire_message)
  (residual:B.bytes)
  : Lemma
      (requires
        WF.parses_as
          CW.tls_record_wire_format
          bytes
          msgs
          residual)
      (ensures
        Seq.equal
          bytes
          (WF.serialize_with_tail
            CW.tls_record_wire_format
            msgs
            residual))

val lemma_wire_serialize_all_append
  (left:list CW.wire_message)
  (right:list CW.wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all
            CW.tls_record_wire_format
            (L.append left right))
          (B.append
            (WF.serialize_all CW.tls_record_wire_format left)
            (WF.serialize_all CW.tls_record_wire_format right)))

val lemma_client_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ClientCP.client_step st0 ev st1 out)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs)) /\
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.event_input_messages ev))))

val lemma_server_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ServerCP.server_step st0 ev st1 out)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs)) /\
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.event_input_messages ev))))

val lemma_client_trace_wire_logs_match
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      CTypes.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (ClientCP.client_state_machine initial)
          st0
          trace
          st1)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace))) /\
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace))))

val lemma_server_trace_wire_logs_match
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      CTypes.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (ServerCP.server_state_machine initial)
          st0
          trace
          st1)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace))) /\
        Seq.equal
          st1.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
          (B.append
            st0.CS.cs_wire_log.TLS13.ConnectionLog.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace))))

val lemma_wire_parses_as_serialize_all
  (bytes:B.bytes)
  (msgs:list CW.wire_message)
  : Lemma
      (requires
        WF.parses_as
          CW.tls_record_wire_format
          bytes
          msgs
          Seq.empty)
      (ensures
        Seq.equal
          bytes
          (WF.serialize_all CW.tls_record_wire_format msgs))

val lemma_client_valid_byte_trace_inverts_to_serialized_trace
  (client_initial:CS.connection_state)
  (client_received:B.bytes)
  (client:CS.connection_state)
  (client_sent:B.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          Seq.empty)
      (ensures
        exists trace.
          SM.trace_reaches
            (ClientCP.client_state_machine client_initial)
            client_initial
            trace
            client /\
          Seq.equal
            client_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace)) /\
          Seq.equal
            client_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace)))

val lemma_server_valid_byte_trace_inverts_to_serialized_trace
  (server_initial:CS.connection_state)
  (server_received:B.bytes)
  (server:CS.connection_state)
  (server_sent:B.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          Seq.empty)
      (ensures
        exists trace.
          SM.trace_reaches
            (ServerCP.server_state_machine server_initial)
            server_initial
            trace
            server /\
          Seq.equal
            server_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace)) /\
          Seq.equal
            server_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace)))

val lemma_client_valid_byte_trace_wire_logs_exact
  (client_initial:CS.connection_state)
  (client_received:B.bytes)
  (client:CS.connection_state)
  (client_sent:B.bytes)
  : Lemma
      (requires
        client_initial ==
          CS.initial client_initial.CS.cs_model.CS.model_config /\
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          Seq.empty)
      (ensures
        Seq.equal client_sent client.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent /\
        Seq.equal client_received client.CS.cs_wire_log.TLS13.ConnectionLog.raw_received)

val lemma_server_valid_byte_trace_wire_logs_exact
  (server_initial:CS.connection_state)
  (server_received:B.bytes)
  (server:CS.connection_state)
  (server_sent:B.bytes)
  : Lemma
      (requires
        server_initial ==
          CS.initial server_initial.CS.cs_model.CS.model_config /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          Seq.empty)
      (ensures
        Seq.equal server_sent server.CS.cs_wire_log.TLS13.ConnectionLog.raw_sent /\
        Seq.equal server_received server.CS.cs_wire_log.TLS13.ConnectionLog.raw_received)

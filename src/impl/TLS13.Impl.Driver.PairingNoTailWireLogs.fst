module TLS13.Impl.Driver.PairingNoTailWireLogs

module B = TLS13.Bytes
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CL = TLS13.ConnectionLog
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
module W = TLS13.Wire.Spec

let lemma_b_empty_seq_empty ()
  : Lemma (Seq.equal B.empty Seq.empty)
=
  Seq.lemma_eq_intro B.empty Seq.empty

let rec lemma_serialize_with_b_empty_is_serialize_all
  (msgs:list CW.wire_message)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_with_tail
            CW.tls_record_wire_format
            msgs
            B.empty)
          (WF.serialize_all CW.tls_record_wire_format msgs))
      (decreases msgs)
=
  match msgs with
  | [] ->
    lemma_b_empty_seq_empty ()
  | _ :: rest ->
    lemma_serialize_with_b_empty_is_serialize_all rest

let rec lemma_wire_parses_as_serialize_with_tail
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
      (decreases msgs)
=
  match msgs with
  | [] ->
    assert (Seq.equal bytes residual)
  | msg :: rest ->
    eliminate exists (parsed_msg:CW.wire_message) (bytes_after_msg:B.bytes).
      CW.wire_parse bytes == Some (parsed_msg, bytes_after_msg) /\
      parsed_msg == msg /\
      WF.parses_as
        CW.tls_record_wire_format
        bytes_after_msg
        rest
        residual
    returns
      Seq.equal
        bytes
        (WF.serialize_with_tail
          CW.tls_record_wire_format
          (msg :: rest)
          residual)
    with _.
    (
      match W.parse_record_wire bytes with
      | None ->
        assert False
      | Some (content_type, fragment, consumed) ->
        W.lemma_parse_record_wire_some_consumed_positive
          bytes
          content_type
          fragment
          consumed;
        assert (consumed <= B.length bytes);
        assert (parsed_msg.CW.wm_raw == Seq.slice bytes 0 consumed);
        assert (bytes_after_msg == Seq.slice bytes consumed (B.length bytes));
        Seq.lemma_split bytes consumed;
        lemma_wire_parses_as_serialize_with_tail
          bytes_after_msg
          rest
          residual;
        assert (Seq.equal
          bytes_after_msg
          (WF.serialize_with_tail
            CW.tls_record_wire_format
            rest
            residual));
        assert (CW.wire_serialize msg == msg.CW.wm_raw);
        assert (Seq.equal
          (WF.serialize_with_tail
            CW.tls_record_wire_format
            (msg :: rest)
            residual)
          (B.append
            msg.CW.wm_raw
            (WF.serialize_with_tail
              CW.tls_record_wire_format
              rest
              residual)));
        assert (Seq.equal
          bytes
          (B.append
            (Seq.slice bytes 0 consumed)
            (Seq.slice bytes consumed (B.length bytes))));
        assert (Seq.equal
          bytes
          (WF.serialize_with_tail
            CW.tls_record_wire_format
            (msg :: rest)
            residual))
    )

let rec lemma_wire_serialize_all_append
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
      (decreases left)
=
  match left with
  | [] ->
    Seq.append_empty_l (WF.serialize_all CW.tls_record_wire_format right)
  | hd :: tl ->
    lemma_wire_serialize_all_append tl right;
    Seq.append_assoc
      (CW.wire_serialize hd)
      (WF.serialize_all CW.tls_record_wire_format tl)
      (WF.serialize_all CW.tls_record_wire_format right)

let lemma_client_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ClientCP.client_step st0 ev st1 out)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs)) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.event_input_messages ev))))
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists msg.
      (let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent =
            WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      ClientCP.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == [wire]);
      Seq.append_empty_r (CW.wire_serialize wire)
    )
  | SM.LocalEvent local ->
    let api = CTypes.client_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ClientCP.client_api_event_matches st0 api conn_ev /\
      ClientCP.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ClientCP.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        }
        st1
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == []);
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format [])
        Seq.empty);
      lemma_b_empty_seq_empty ();
      Seq.lemma_eq_elim
        raw_sent
        (WF.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs)
    )

let lemma_server_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ServerCP.server_step st0 ev st1 out)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs)) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.event_input_messages ev))))
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists msg.
      (let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent =
            WF.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      ServerCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == [wire]);
      Seq.append_empty_r (CW.wire_serialize wire)
    )
  | SM.LocalEvent local ->
    let api = CTypes.server_local_event_api local in
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      ServerCP.server_api_event_matches api conn_ev /\
      ServerCP.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ServerCP.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        }
        st1
    returns
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_sent
        (B.append
          st0.CS.cs_wire_log.CL.raw_sent
          (WF.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs)) /\
      Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        (B.append
          st0.CS.cs_wire_log.CL.raw_received
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.event_input_messages ev)))
    with _.
    (
      assert (WFSM.event_input_messages ev == []);
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format [])
        Seq.empty);
      lemma_b_empty_seq_empty ();
      Seq.lemma_eq_elim
        raw_sent
        (WF.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs)
    )

let rec lemma_client_trace_wire_logs_match
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
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace))) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace))))
      (decreases trace)
=
  match trace with
  | [] ->
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  | tr :: rest ->
    assert (ClientCP.client_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output);
    lemma_client_step_wire_log_delta
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_client_trace_wire_logs_match
      initial
      tr.SM.tr_next_state
      rest
      st1;
    let step_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        tr.SM.tr_output.SM.so_wire_outputs in
    let rest_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs rest) in
    let step_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.event_input_messages tr.SM.tr_event) in
    let rest_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages rest) in
    lemma_wire_serialize_all_append
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    lemma_wire_serialize_all_append
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received step_received);
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_sent step_sent rest_sent;
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_received step_received rest_received;
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append
        st0.CS.cs_wire_log.CL.raw_sent
        (B.append step_sent rest_sent)));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append
        st0.CS.cs_wire_log.CL.raw_received
        (B.append step_received rest_received)))

let rec lemma_server_trace_wire_logs_match
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
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (WF.serialize_all
              CW.tls_record_wire_format
              (SM.trace_wire_outputs trace))) /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          (B.append
            st0.CS.cs_wire_log.CL.raw_received
            (WF.serialize_all
              CW.tls_record_wire_format
              (WFSM.trace_input_messages trace))))
      (decreases trace)
=
  match trace with
  | [] ->
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  | tr :: rest ->
    assert (ServerCP.server_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output);
    lemma_server_step_wire_log_delta
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_server_trace_wire_logs_match
      initial
      tr.SM.tr_next_state
      rest
      st1;
    let step_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        tr.SM.tr_output.SM.so_wire_outputs in
    let rest_sent =
      WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs rest) in
    let step_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.event_input_messages tr.SM.tr_event) in
    let rest_received =
      WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages rest) in
    lemma_wire_serialize_all_append
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    lemma_wire_serialize_all_append
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_sent
      (B.append st0.CS.cs_wire_log.CL.raw_sent step_sent);
    Seq.lemma_eq_elim
      tr.SM.tr_next_state.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received step_received);
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_sent step_sent rest_sent;
    Seq.append_assoc st0.CS.cs_wire_log.CL.raw_received step_received rest_received;
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_sent
      (B.append
        st0.CS.cs_wire_log.CL.raw_sent
        (B.append step_sent rest_sent)));
    assert (Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append
        st0.CS.cs_wire_log.CL.raw_received
        (B.append step_received rest_received)))

let lemma_wire_parses_as_serialize_all
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
=
  lemma_wire_parses_as_serialize_with_tail bytes msgs Seq.empty

let lemma_client_valid_byte_trace_inverts_to_serialized_trace
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
=
  eliminate exists trace.
    SM.trace_reaches
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      client /\
    WF.parses_as
      (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
      client_received
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      client_sent
      (WF.serialize_all
        (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
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
          (SM.trace_wire_outputs trace))
  with _.
  (
    lemma_wire_parses_as_serialize_all
      client_received
      (WFSM.trace_input_messages trace);
    assert ((ClientCP.client_system client_initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    assert ((ClientCP.client_system client_initial).WFSM.wfsm_state_machine ==
      ClientCP.client_state_machine client_initial);
    assert ((ClientCP.client_state_machine client_initial).SM.sm_initial_state ==
      client_initial);
    assert (exists trace'.
      SM.trace_reaches
        (ClientCP.client_state_machine client_initial)
        client_initial
        trace'
        client /\
      Seq.equal
        client_received
        (WF.serialize_all
          CW.tls_record_wire_format
          (WFSM.trace_input_messages trace')) /\
      Seq.equal
        client_sent
        (WF.serialize_all
          CW.tls_record_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_server_valid_byte_trace_inverts_to_serialized_trace
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
=
  eliminate exists trace.
    SM.trace_reaches
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      server /\
    WF.parses_as
      (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
      server_received
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      server_sent
      (WF.serialize_all
        (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
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
          (SM.trace_wire_outputs trace))
  with _.
  (
    lemma_wire_parses_as_serialize_all
      server_received
      (WFSM.trace_input_messages trace);
    assert ((ServerCP.server_system server_initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    assert ((ServerCP.server_system server_initial).WFSM.wfsm_state_machine ==
      ServerCP.server_state_machine server_initial);
    assert ((ServerCP.server_state_machine server_initial).SM.sm_initial_state ==
      server_initial);
    assert (exists trace'.
      SM.trace_reaches
        (ServerCP.server_state_machine server_initial)
        server_initial
        trace'
        server /\
      Seq.equal
        server_received
        (WF.serialize_all
          CW.tls_record_wire_format
          (WFSM.trace_input_messages trace')) /\
      Seq.equal
        server_sent
        (WF.serialize_all
          CW.tls_record_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_client_valid_byte_trace_wire_logs_exact
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
        Seq.equal client_sent client.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal client_received client.CS.cs_wire_log.CL.raw_received)
=
  lemma_client_valid_byte_trace_inverts_to_serialized_trace
    client_initial
    client_received
    client
    client_sent;
  eliminate exists trace.
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
        (SM.trace_wire_outputs trace))
  returns
    Seq.equal client_sent client.CS.cs_wire_log.CL.raw_sent /\
    Seq.equal client_received client.CS.cs_wire_log.CL.raw_received
  with _.
  (
    lemma_client_trace_wire_logs_match
      client_initial
      client_initial
      trace
      client;
    assert (Seq.equal client_initial.CS.cs_wire_log.CL.raw_sent B.empty);
    assert (Seq.equal client_initial.CS.cs_wire_log.CL.raw_received B.empty);
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace));
    Seq.lemma_eq_elim
      client.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.lemma_eq_elim
      client.CS.cs_wire_log.CL.raw_received
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace))
  )

let lemma_server_valid_byte_trace_wire_logs_exact
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
        Seq.equal server_sent server.CS.cs_wire_log.CL.raw_sent /\
        Seq.equal server_received server.CS.cs_wire_log.CL.raw_received)
=
  lemma_server_valid_byte_trace_inverts_to_serialized_trace
    server_initial
    server_received
    server
    server_sent;
  eliminate exists trace.
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
        (SM.trace_wire_outputs trace))
  returns
    Seq.equal server_sent server.CS.cs_wire_log.CL.raw_sent /\
    Seq.equal server_received server.CS.cs_wire_log.CL.raw_received
  with _.
  (
    lemma_server_trace_wire_logs_match
      server_initial
      server_initial
      trace
      server;
    assert (Seq.equal server_initial.CS.cs_wire_log.CL.raw_sent B.empty);
    assert (Seq.equal server_initial.CS.cs_wire_log.CL.raw_received B.empty);
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.append_empty_l
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace));
    Seq.lemma_eq_elim
      server.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all
        CW.tls_record_wire_format
        (SM.trace_wire_outputs trace));
    Seq.lemma_eq_elim
      server.CS.cs_wire_log.CL.raw_received
      (WF.serialize_all
        CW.tls_record_wire_format
        (WFSM.trace_input_messages trace))
  )

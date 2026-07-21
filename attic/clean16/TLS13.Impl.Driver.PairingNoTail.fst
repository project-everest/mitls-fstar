module TLS13.Impl.Driver.PairingNoTail

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module ListP = FStar.List.Tot.Properties
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PTS = TLS13.Impl.Driver.PairingTraceShape
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module RTC = FStar.ReflexiveTransitiveClosure
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module SM = Common.StateMachine
module Tac = FStar.Tactics
module TCP = Common.TCP
module WFSM = Common.WireFormatStateMachine

let lemma_client_step_connection_state_single_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ClientCP.client_step st0 ev st1 out)
      (ensures
        CS.connection_state_single_step st0 st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists (msg:M.tls_message).
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
            Common.WireFormat.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      ClientCP.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      CS.connection_state_single_step st0 st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _.
    ( let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent =
          Common.WireFormat.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs;
        CS.delta_raw_received = CW.wire_serialize wire;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (exists delta'. CS.legal_connection_delta st0 delta' st1);
      CSL.lemma_step_model_preserves_config
        st0.CS.cs_model
        conn_ev
        st1.CS.cs_model )
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
      CS.connection_state_single_step st0 st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _.
    ( let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (exists delta'. CS.legal_connection_delta st0 delta' st1);
      CSL.lemma_step_model_preserves_config
        st0.CS.cs_model
        conn_ev
        st1.CS.cs_model )

let lemma_server_step_connection_state_single_step
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires ServerCP.server_step st0 ev st1 out)
      (ensures
        CS.connection_state_single_step st0 st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists (msg:M.tls_message).
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
            Common.WireFormat.serialize_all
              CW.tls_record_wire_format
              out.SM.so_wire_outputs;
          CS.delta_raw_received = CW.wire_serialize wire;
        }
        st1 /\
      ServerCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      CS.connection_state_single_step st0 st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _.
    ( let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent =
          Common.WireFormat.serialize_all
            CW.tls_record_wire_format
            out.SM.so_wire_outputs;
        CS.delta_raw_received = CW.wire_serialize wire;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (exists delta'. CS.legal_connection_delta st0 delta' st1);
      CSL.lemma_step_model_preserves_config
        st0.CS.cs_model
        conn_ev
        st1.CS.cs_model )
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
      CS.connection_state_single_step st0 st1 /\
      st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config
    with _.
    ( let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = B.empty;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (exists delta'. CS.legal_connection_delta st0 delta' st1);
      CSL.lemma_step_model_preserves_config
        st0.CS.cs_model
        conn_ev
        st1.CS.cs_model )

let lemma_connection_state_consistent_step
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_consistent st0 /\
        CS.connection_state_single_step st0 st1 /\
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
      (ensures CS.connection_state_consistent st1)
=
  RTC.closure_step CS.connection_state_single_step st0 st1;
  assert (CS.connection_state_evolves st0 st1);
  assert (RTC.transitive CS.connection_state_evolves);
  assert (CS.connection_state_evolves
    (CS.initial st0.CS.cs_model.CS.model_config)
    st0);
  assert (CS.connection_state_evolves
    (CS.initial st0.CS.cs_model.CS.model_config)
    st1);
  assert (CS.initial st1.CS.cs_model.CS.model_config ==
    CS.initial st0.CS.cs_model.CS.model_config);
  assert (CS.connection_state_consistent st1)

let lemma_client_step_preserves_connection_state_replay_consistent
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires
        ClientCP.client_step st0 ev st1 out /\
        CS.connection_state_sent_seal_replay_consistent st0 /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures
        CS.connection_state_sent_seal_replay_consistent st1 /\
        CS.connection_state_received_decode_replay_consistent st1)
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists (msg:M.tls_message).
      (let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
       let raw_sent =
        Common.WireFormat.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs in
       let raw_received = CW.wire_serialize wire in
       CS.legal_connection_delta
         st0
         {
           CS.delta_event = conn_ev;
           CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = raw_received;
         }
         st1 /\
       CS.sent_event_nonempty_seal_projection
         st0.CS.cs_model
         conn_ev
         raw_sent /\
       CS.received_event_nonempty_decode_projection
         st0.CS.cs_model
         conn_ev
         raw_received /\
       (exists content_type fragment.
         CT.network_input_message_projection
           st0
           content_type
           fragment
           msg
           raw_received) /\
       ClientCP.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      CS.connection_state_sent_seal_replay_consistent st1 /\
      CS.connection_state_received_decode_replay_consistent st1
    with _.
    ( let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      let raw_sent =
        Common.WireFormat.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs in
      let raw_received = CW.wire_serialize wire in
      let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = raw_received;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent);
      assert (CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        raw_received);
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        st0
        delta
        st1;
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        st0
        delta
        st1 )
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
        st1 /\
      CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent /\
      CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        B.empty
    returns
      CS.connection_state_sent_seal_replay_consistent st1 /\
      CS.connection_state_received_decode_replay_consistent st1
    with _.
    ( let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent);
      assert (CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        B.empty);
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        st0
        delta
        st1;
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        st0
        delta
        st1 )

let lemma_server_step_preserves_connection_state_replay_consistent
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.server_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message CTypes.local_output)
  : Lemma
      (requires
        ServerCP.server_step st0 ev st1 out /\
        CS.connection_state_sent_seal_replay_consistent st0 /\
        CS.connection_state_received_decode_replay_consistent st0)
      (ensures
        CS.connection_state_sent_seal_replay_consistent st1 /\
        CS.connection_state_received_decode_replay_consistent st1)
=
  match ev with
  | SM.WireEvent wire ->
    eliminate exists (msg:M.tls_message).
      (let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
       let raw_sent =
        Common.WireFormat.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs in
       let raw_received = CW.wire_serialize wire in
       CS.legal_connection_delta
         st0
         {
           CS.delta_event = conn_ev;
           CS.delta_raw_sent = raw_sent;
           CS.delta_raw_received = raw_received;
         }
         st1 /\
       CS.sent_event_nonempty_seal_projection
         st0.CS.cs_model
         conn_ev
         raw_sent /\
       CS.received_event_nonempty_decode_projection
         st0.CS.cs_model
         conn_ev
         raw_received /\
       ServerCP.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    returns
      CS.connection_state_sent_seal_replay_consistent st1 /\
      CS.connection_state_received_decode_replay_consistent st1
    with _.
    ( let conn_ev =
        CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        } in
      let raw_sent =
        Common.WireFormat.serialize_all
          CW.tls_record_wire_format
          out.SM.so_wire_outputs in
      let raw_received = CW.wire_serialize wire in
      let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = raw_received;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent);
      assert (CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        raw_received);
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        st0
        delta
        st1;
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        st0
        delta
        st1 )
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
        st1 /\
      CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent /\
      CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        B.empty
    returns
      CS.connection_state_sent_seal_replay_consistent st1 /\
      CS.connection_state_received_decode_replay_consistent st1
    with _.
    ( let delta = {
        CS.delta_event = conn_ev;
        CS.delta_raw_sent = raw_sent;
        CS.delta_raw_received = B.empty;
      } in
      assert (CS.legal_connection_delta st0 delta st1);
      assert (CS.sent_event_nonempty_seal_projection
        st0.CS.cs_model
        conn_ev
        raw_sent);
      assert (CS.received_event_nonempty_decode_projection
        st0.CS.cs_model
        conn_ev
        B.empty);
      CSL.lemma_legal_connection_delta_sent_seal_replay_consistent
        st0
        delta
        st1;
      CSL.lemma_legal_connection_delta_received_decode_replay_consistent
        st0
        delta
        st1 )

let rec lemma_client_trace_reaches_preserves_connection_state_consistent
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
        CS.connection_state_consistent st0 /\
        SM.trace_reaches
          (ClientCP.client_system initial).WFSM.wfsm_state_machine
          st0
          trace
          st1)
      (ensures CS.connection_state_consistent st1)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    assert (ClientCP.client_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output)
    by (
      Tac.norm
        [delta_only
          [`%ClientCP.client_system;
           `%ClientCP.client_state_machine];
         iota; zeta; primops];
      Tac.smt ());
    lemma_client_step_connection_state_single_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_connection_state_consistent_step st0 tr.SM.tr_next_state;
    lemma_client_trace_reaches_preserves_connection_state_consistent
      initial
      tr.SM.tr_next_state
      rest
      st1

let rec lemma_server_trace_reaches_preserves_connection_state_consistent
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
        CS.connection_state_consistent st0 /\
        SM.trace_reaches
          (ServerCP.server_system initial).WFSM.wfsm_state_machine
          st0
          trace
          st1)
      (ensures CS.connection_state_consistent st1)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    assert (ServerCP.server_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output)
    by (
      Tac.norm
        [delta_only
          [`%ServerCP.server_system;
           `%ServerCP.server_state_machine];
         iota; zeta; primops];
      Tac.smt ());
    lemma_server_step_connection_state_single_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_connection_state_consistent_step st0 tr.SM.tr_next_state;
    lemma_server_trace_reaches_preserves_connection_state_consistent
      initial
      tr.SM.tr_next_state
      rest
      st1

let rec lemma_client_trace_reaches_preserves_connection_state_replay_consistent
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
        CS.connection_state_sent_seal_replay_consistent st0 /\
        CS.connection_state_received_decode_replay_consistent st0 /\
        SM.trace_reaches
          (ClientCP.client_system initial).WFSM.wfsm_state_machine
          st0
          trace
          st1)
      (ensures
        CS.connection_state_sent_seal_replay_consistent st1 /\
        CS.connection_state_received_decode_replay_consistent st1)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    assert (ClientCP.client_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output)
    by (
      Tac.norm
        [delta_only
          [`%ClientCP.client_system;
           `%ClientCP.client_state_machine];
         iota; zeta; primops];
      Tac.smt ());
    lemma_client_step_preserves_connection_state_replay_consistent
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_client_trace_reaches_preserves_connection_state_replay_consistent
      initial
      tr.SM.tr_next_state
      rest
      st1

let rec lemma_server_trace_reaches_preserves_connection_state_replay_consistent
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
        CS.connection_state_sent_seal_replay_consistent st0 /\
        CS.connection_state_received_decode_replay_consistent st0 /\
        SM.trace_reaches
          (ServerCP.server_system initial).WFSM.wfsm_state_machine
          st0
          trace
          st1)
      (ensures
        CS.connection_state_sent_seal_replay_consistent st1 /\
        CS.connection_state_received_decode_replay_consistent st1)
      (decreases trace)
=
  match trace with
  | [] -> ()
  | tr :: rest ->
    assert (ServerCP.server_step
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output)
    by (
      Tac.norm
        [delta_only
          [`%ServerCP.server_system;
           `%ServerCP.server_state_machine];
         iota; zeta; primops];
      Tac.smt ());
    lemma_server_step_preserves_connection_state_replay_consistent
      st0
      tr.SM.tr_event
      tr.SM.tr_next_state
      tr.SM.tr_output;
    lemma_server_trace_reaches_preserves_connection_state_replay_consistent
      initial
      tr.SM.tr_next_state
      rest
      st1

let lemma_valid_byte_trace_inverts_to_state_trace
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine
    state
    wire_message
    local_event
    local_output)
  (input_bytes:TCP.bytes)
  (st1:state)
  (output_bytes:TCP.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          system
          input_bytes
          st1
          output_bytes
          residual_input)
      (ensures
        exists trace.
          SM.trace_reaches
            system.WFSM.wfsm_state_machine
            system.WFSM.wfsm_state_machine.SM.sm_initial_state
            trace
            st1)
=
  eliminate exists
    (trace:list (SM.transition state wire_message local_event local_output)).
    SM.trace_reaches
      system.WFSM.wfsm_state_machine
      system.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      st1 /\
    (Common.WireFormat.parses_as
      system.WFSM.wfsm_wire_format
      input_bytes
      (WFSM.trace_input_messages trace)
      residual_input
     \/
     Seq.equal
       input_bytes
       (Seq.append
         (Common.WireFormat.serialize_all
           system.WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      output_bytes
      (Common.WireFormat.serialize_all
        system.WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
    exists trace'.
      SM.trace_reaches
        system.WFSM.wfsm_state_machine
        system.WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        st1
  with _.
  ( assert (exists trace'.
      SM.trace_reaches
        system.WFSM.wfsm_state_machine
        system.WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        st1) )

let lemma_client_valid_byte_trace_preserves_connection_state_consistent
  (client_initial:CS.connection_state)
  (client:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent client_initial /\
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          residual_input)
      (ensures CS.connection_state_consistent client)
=
  eliminate exists
    (trace:list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.client_local_event
        CTypes.local_output)).
    SM.trace_reaches
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      client /\
    (Common.WireFormat.parses_as
      (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
      client_received
      (WFSM.trace_input_messages trace)
      residual_input
     \/
     Seq.equal
       client_received
       (Seq.append
         (Common.WireFormat.serialize_all
           (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      client_sent
      (Common.WireFormat.serialize_all
        (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
    CS.connection_state_consistent client
  with _.
  ( assert ((ClientCP.client_system client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state ==
      client_initial);
    lemma_client_trace_reaches_preserves_connection_state_consistent
      client_initial
      client_initial
      trace
      client )

let lemma_server_valid_byte_trace_preserves_connection_state_consistent
  (server_initial:CS.connection_state)
  (server:CS.connection_state)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent server_initial /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          residual_input)
      (ensures CS.connection_state_consistent server)
=
  eliminate exists
    (trace:list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.server_local_event
        CTypes.local_output)).
    SM.trace_reaches
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      server /\
    (Common.WireFormat.parses_as
      (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
      server_received
      (WFSM.trace_input_messages trace)
      residual_input
     \/
     Seq.equal
       server_received
       (Seq.append
         (Common.WireFormat.serialize_all
           (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      server_sent
      (Common.WireFormat.serialize_all
        (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
    CS.connection_state_consistent server
  with _.
  ( assert ((ServerCP.server_system server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state ==
      server_initial);
    lemma_server_trace_reaches_preserves_connection_state_consistent
      server_initial
      server_initial
      trace
      server )

let lemma_client_valid_byte_trace_preserves_connection_state_replay_consistent
  (client_initial:CS.connection_state)
  (client:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_sent_seal_replay_consistent client_initial /\
        CS.connection_state_received_decode_replay_consistent client_initial /\
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          residual_input)
      (ensures
        CS.connection_state_sent_seal_replay_consistent client /\
        CS.connection_state_received_decode_replay_consistent client)
=
  eliminate exists
    (trace:list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.client_local_event
        CTypes.local_output)).
    SM.trace_reaches
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine
      (ClientCP.client_system client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      client /\
    (Common.WireFormat.parses_as
      (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
      client_received
      (WFSM.trace_input_messages trace)
      residual_input
     \/
     Seq.equal
       client_received
       (Seq.append
         (Common.WireFormat.serialize_all
           (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      client_sent
      (Common.WireFormat.serialize_all
        (ClientCP.client_system client_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
    CS.connection_state_sent_seal_replay_consistent client /\
    CS.connection_state_received_decode_replay_consistent client
  with _.
  ( assert ((ClientCP.client_system client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state ==
      client_initial);
    lemma_client_trace_reaches_preserves_connection_state_replay_consistent
      client_initial
      client_initial
      trace
      client )

let lemma_server_valid_byte_trace_preserves_connection_state_replay_consistent
  (server_initial:CS.connection_state)
  (server:CS.connection_state)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_sent_seal_replay_consistent server_initial /\
        CS.connection_state_received_decode_replay_consistent server_initial /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          residual_input)
      (ensures
        CS.connection_state_sent_seal_replay_consistent server /\
        CS.connection_state_received_decode_replay_consistent server)
=
  eliminate exists
    (trace:list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.server_local_event
        CTypes.local_output)).
    SM.trace_reaches
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine
      (ServerCP.server_system server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      server /\
    (Common.WireFormat.parses_as
      (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
      server_received
      (WFSM.trace_input_messages trace)
      residual_input
     \/
     Seq.equal
       server_received
       (Seq.append
         (Common.WireFormat.serialize_all
           (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      server_sent
      (Common.WireFormat.serialize_all
        (ServerCP.server_system server_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  returns
    CS.connection_state_sent_seal_replay_consistent server /\
    CS.connection_state_received_decode_replay_consistent server
  with _.
  ( assert ((ServerCP.server_system server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state ==
      server_initial);
    lemma_server_trace_reaches_preserves_connection_state_replay_consistent
      server_initial
      server_initial
      trace
      server )

let lemma_paired_successful_handshake_complete_event_log_shape_no_tail
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PTS.paired_successful_handshake_complete_event_log_shape client server)
      (ensures
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        FStar.List.Tot.length server.CS.cs_event_log == 15 /\
        CS.connection_state_no_key_update_trace client /\
        CS.connection_state_no_key_update_trace server)
=
  eliminate exists
    (ch:GCH.clientHello)
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    (cf:GFin.finished)
    (start:CS.handshake_start)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (client_shared:C.x25519_shared_secret)
    (server_material:CS.traffic_key_material)
    (client_material:CS.traffic_key_material)
    (client_hs_write_material:CS.traffic_key_material)
    (server_auth_skip:CS.local_event)
    (client_auth_skip:CS.local_event)
    (client_verify_skip:CS.local_event)
    (client_app_write_material:CS.traffic_key_material)
    (client_app_read_material:CS.traffic_key_material)
    (server_app_write_material:CS.traffic_key_material)
    (server_app_read_material:CS.traffic_key_material).
    PTS.paired_successful_handshake_complete_event_log_shape_inputs
      client
      server
      ch
      sh
      ee
      cert
      cv
      sf
      cf
      start
      selection
      server_shared
      client_shared
      server_material
      client_material
      client_hs_write_material
      server_auth_skip
      client_auth_skip
      client_verify_skip
      client_app_write_material
      client_app_read_material
      server_app_write_material
      server_app_read_material
  returns
    FStar.List.Tot.length client.CS.cs_event_log == 16 /\
    FStar.List.Tot.length server.CS.cs_event_log == 15 /\
    CS.connection_state_no_key_update_trace client /\
    CS.connection_state_no_key_update_trace server
  with _.
  ( let server_suffix =
      PWL.server_protected_handshake_contiguous_replay_events
        server_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        server_auth_skip
        (M.CertificateVerify cv)
        (M.Finished sf)
        server_app_write_material
        (M.Finished cf)
        [
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
    let client_suffix =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = client_hs_write_material;
        }) ::
      PWL.client_protected_handshake_contiguous_replay_events
        client_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        client_auth_skip
        (M.CertificateVerify cv)
        client_verify_skip
        (M.Finished sf)
        sf
        client_app_write_material
        client_app_read_material
        (M.Finished cf)
        [] in
    let server_prefix =
      PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh in
    let client_prefix =
      PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared in
    let server_events = FStar.List.Tot.append server_prefix server_suffix in
    let client_events = FStar.List.Tot.append client_prefix client_suffix in
    assert (client.CS.cs_event_log == client_events);
    assert (server.CS.cs_event_log == server_events);
    ListP.append_length client_prefix client_suffix;
    ListP.append_length server_prefix server_suffix;
    assert (FStar.List.Tot.length
      (PWSeg.client_cleartext_handshake_prefix_events
        start
        ch
        sh
        client_shared) == 4)
      by (
        Tac.norm
          [delta_only [`%PWSeg.client_cleartext_handshake_prefix_events]];
        Tac.trefl ());
    assert (FStar.List.Tot.length client_prefix == 4);
    assert (FStar.List.Tot.length
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh) == 5)
      by (
        Tac.norm
          [delta_only [`%PWSeg.server_cleartext_handshake_prefix_events]];
        Tac.trefl ());
    assert (FStar.List.Tot.length server_prefix == 5);
    assert (FStar.List.Tot.length
      (PWL.client_protected_handshake_contiguous_replay_events
        client_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        client_auth_skip
        (M.CertificateVerify cv)
        client_verify_skip
        (M.Finished sf)
        sf
        client_app_write_material
        client_app_read_material
        (M.Finished cf)
        []) == 11)
      by (
        Tac.norm
          [delta_only
            [`%PWL.client_protected_handshake_contiguous_replay_events;
             `%PWL.client_receive_server_encrypted_flight_replay_events;
             `%PWL.client_finished_replay_events]];
        Tac.trefl ());
    assert (FStar.List.Tot.length client_suffix == 12);
    assert (FStar.List.Tot.length
      (PWL.server_protected_handshake_contiguous_replay_events
        server_material
        (M.EncryptedExtensions ee)
        (M.Certificate cert)
        server_auth_skip
        (M.CertificateVerify cv)
        (M.Finished sf)
        server_app_write_material
        (M.Finished cf)
        [
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
        ]) == 10)
      by (
        Tac.norm
          [delta_only
            [`%PWL.server_protected_handshake_contiguous_replay_events;
             `%PWL.server_encrypted_flight_replay_events;
             `%PWL.server_receive_client_finished_replay_events]];
        Tac.trefl ());
    assert (FStar.List.Tot.length server_suffix == 10);
    assert (FStar.List.Tot.length client_events == 16);
    assert (FStar.List.Tot.length server_events == 15);
    assert (CS.conn_events_no_key_update
      (FStar.List.Tot.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start
          ch
          sh
          client_shared)
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = client_hs_write_material;
          }) ::
        PWL.client_protected_handshake_contiguous_replay_events
          client_material
          (M.EncryptedExtensions ee)
          (M.Certificate cert)
          client_auth_skip
          (M.CertificateVerify cv)
          client_verify_skip
          (M.Finished sf)
          sf
          client_app_write_material
          client_app_read_material
          (M.Finished cf)
          [])) == true)
      by (
        Tac.norm
          [delta_only
            [`%PWSeg.client_cleartext_handshake_prefix_events;
             `%PWL.client_protected_handshake_contiguous_replay_events;
             `%PWL.client_receive_server_encrypted_flight_replay_events;
             `%PWL.client_finished_replay_events;
             `%CS.conn_events_no_key_update;
             `%CS.conn_event_is_key_update]];
        Tac.trefl ());
    assert (CS.conn_events_no_key_update client_events == true);
    assert (CS.conn_events_no_key_update
      (FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (PWL.server_protected_handshake_contiguous_replay_events
          server_material
          (M.EncryptedExtensions ee)
          (M.Certificate cert)
          server_auth_skip
          (M.CertificateVerify cv)
          (M.Finished sf)
          server_app_write_material
          (M.Finished cf)
          [
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
          ])) == true)
      by (
        Tac.norm
          [delta_only
            [`%PWSeg.server_cleartext_handshake_prefix_events;
             `%PWL.server_protected_handshake_contiguous_replay_events;
             `%PWL.server_encrypted_flight_replay_events;
             `%PWL.server_receive_client_finished_replay_events;
             `%CS.conn_events_no_key_update;
             `%CS.conn_event_is_key_update]];
        Tac.trefl ());
    assert (CS.conn_events_no_key_update server_events == true);
    assert (CS.conn_events_no_key_update client.CS.cs_event_log == true);
    assert (CS.conn_events_no_key_update server.CS.cs_event_log == true) )

let lemma_paired_successful_handshake_complete_state_trace_no_tail
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PTS.paired_successful_handshake_complete_state_trace client server)
      (ensures
        paired_no_tail_application_ready_boundary client server /\
        CS.connection_state_no_key_update_trace client /\
        CS.connection_state_no_key_update_trace server)
=
  lemma_paired_successful_handshake_complete_event_log_shape_no_tail
    client
    server

let lemma_client_server_application_record_material_agrees_from_no_tail_state_trace_with_paired_handshake_event_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_no_tail_state_trace_with_paired_handshake_event_trace
          client
          server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  Pairing.lemma_client_server_application_record_material_agrees_from_paired_handshake_event_trace
    client
    server

let lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_paired_handshake_event_trace
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
        paired_valid_byte_traces_at_no_tail_boundary_with_paired_handshake_event_trace
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_client_server_application_record_material_agrees_from_no_tail_state_trace_with_paired_handshake_event_trace
    client
    server

let lemma_successful_handshake_complete_state_trace_from_no_tail_event_log_shape
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_no_tail_application_ready_boundary client server /\
        CS.paired_wire_logs client server /\
        Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server /\
        PTS.paired_successful_handshake_complete_event_log_shape client server)
      (ensures
        PTS.paired_successful_handshake_complete_state_trace client server)
=
  ()

let lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
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
        paired_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_successful_handshake_complete_state_trace_from_no_tail_event_log_shape
    client
    server;
  PTS.lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_state_trace
    client
    server

let lemma_client_server_application_record_material_agrees_from_no_tail_valid_byte_traces
  (client_initial server_initial: CS.connection_state)
  (client server: CS.connection_state)
  (client_received client_sent server_received server_sent: B.bytes)
  : Lemma
      (requires
        paired_supported_no_tail_valid_byte_traces
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CS.supported_profile_client_server_key_material_agrees client server /\
               CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
               CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server)
=
  lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent

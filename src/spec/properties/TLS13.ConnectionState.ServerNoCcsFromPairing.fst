module TLS13.ConnectionState.ServerNoCcsFromPairing

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module T = TLS13.Types
module CW = TLS13.Spec.Endpoint.Wire
module WF = Common.WireFormat
module SM = Common.StateMachine
module WFSM = Common.WireFormatStateMachine
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module EAPI = TLS13.Spec.Endpoint.API
module CTy = TLS13.Impl.CanonicalTypes
module WStep = TLS13.System.WireStep
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module SCShape = TLS13.ConnectionState.ServerCanonicalShape
module CliOut = TLS13.ConnectionState.ClientNoCcsOutputs
module SrvIn = TLS13.ConnectionState.ServerNoCcsInputs
module L = FStar.List.Tot

open FStar.List.Tot

(* Trace type abbreviations. *)
let client_trace_t =
  list (SM.transition CS.connection_state CW.wire_message
          CTy.client_local_event EAPI.local_output)
let server_trace_t =
  list (SM.transition CS.connection_state CW.wire_message
          CTy.server_local_event EAPI.local_output)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"
let lemma_no_received_ccs_from_pairing
  (client server : CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial client.CS.cs_model.CS.model_config) client /\
        WStep.server_reachable (CS.initial server.CS.cs_model.CS.model_config) server /\
        Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received /\
        Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        SCShape.log_has_no_received_ccs server.CS.cs_event_log)
=
  let ccfg = client.CS.cs_model.CS.model_config in
  let scfg = server.CS.cs_model.CS.model_config in
  let client_initial : EC.client_initial_state = CS.initial ccfg in
  let server_initial : ES.server_initial_state = CS.initial scfg in
  // STEP 1: reachability => byte-level valid_byte_trace for both endpoints.
  WStep.lemma_client_valid_byte_trace_of_reachable ccfg client;
  WStep.lemma_server_valid_byte_trace_of_reachable scfg server;
  // STEP 2: invert to serialized traces.
  PNTWL.lemma_client_valid_byte_trace_inverts_to_serialized_trace
    client_initial
    client.CS.cs_wire_log.CL.raw_received
    client
    client.CS.cs_wire_log.CL.raw_sent;
  PNTWL.lemma_server_valid_byte_trace_inverts_to_serialized_trace
    server_initial
    server.CS.cs_wire_log.CL.raw_received
    server
    server.CS.cs_wire_log.CL.raw_sent;
  eliminate exists (client_trace:client_trace_t).
    SM.trace_reaches
      (EC.client_state_machine #CTy.client_local_event client_initial)
      client_initial client_trace client /\
    Seq.equal client.CS.cs_wire_log.CL.raw_received
      (WF.serialize_all CW.tls_record_wire_format
        (WFSM.trace_input_messages client_trace)) /\
    Seq.equal client.CS.cs_wire_log.CL.raw_sent
      (WF.serialize_all CW.tls_record_wire_format
        (SM.trace_wire_outputs client_trace))
  with
  (
    eliminate exists (server_trace:server_trace_t).
      SM.trace_reaches
        (ES.server_state_machine #CTy.server_local_event server_initial)
        server_initial server_trace server /\
      Seq.equal server.CS.cs_wire_log.CL.raw_received
        (WF.serialize_all CW.tls_record_wire_format
          (WFSM.trace_input_messages server_trace)) /\
      Seq.equal server.CS.cs_wire_log.CL.raw_sent
        (WF.serialize_all CW.tls_record_wire_format
          (SM.trace_wire_outputs server_trace))
    with
    (
      // STEP 3: byte_pairing at TlsQuiet gives client-sent == server-received.
      assert (Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received);
      // hence the two serialize_all agree.
      assert (Seq.equal
        (WF.serialize_all CW.tls_record_wire_format
          (SM.trace_wire_outputs client_trace))
        (WF.serialize_all CW.tls_record_wire_format
          (WFSM.trace_input_messages server_trace)));
      // STEP 4: injectivity => the message lists coincide.
      PNTWL.lemma_wire_serialize_all_injective
        (SM.trace_wire_outputs client_trace)
        (WFSM.trace_input_messages server_trace);
      assert (SM.trace_wire_outputs client_trace ==
              WFSM.trace_input_messages server_trace);
      // STEP 5: the client never emits a CCS-content record.
      CliOut.lemma_client_trace_outputs_ccs_free
        client_initial client_initial client client_trace;
      assert (forall (wm:CW.wire_message).
        L.memP wm (WFSM.trace_input_messages server_trace) ==>
        wm.CW.wm_content_type <> T.Change_cipher_spec);
      // server_initial starts with an empty event log.
      assert (server_initial.CS.cs_event_log == []);
      assert (SCShape.log_has_no_received_ccs server_initial.CS.cs_event_log);
      // STEP 6: a CCS-content-free input trace never logs a received CCS.
      SrvIn.lemma_server_no_ccs_event_from_ccs_free_inputs
        server_initial server_initial server server_trace
    )
  )
#pop-options

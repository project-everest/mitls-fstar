module TLS13.Impl.Client.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Class.Duplicable

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CP = TLS13.Impl.Client.CanonicalProtocol
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.Spec.StateMachine.Log
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Drain
module DS = TLS13.Impl.Client.Driver.State
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel

let message_of_bytes (bytes:B.bytes) : B.bytes = bytes

let send_succeeded (status:DS.driver_workflow_status) : bool =
  match status with
  | DS.DriverWorkflowOk -> true
  | _ -> false

let lemma_channel_state_valid
  (d:DS.client_driver)
  (wire_received:B.bytes)
  (wire_sent:B.bytes)
  (pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  (st:CS.connection_state)
  : Lemma
      (requires
        Common.WireFormatStateMachine.valid_byte_trace
          (CP.client_protocol_implementation.CPI.pi_system
            (DS.client_driver_canonical d))
          st.CS.cs_wire_log.CL.raw_received
          st
          st.CS.cs_wire_log.CL.raw_sent
          Seq.empty /\
        Seq.equal
          wire_received
          (B.append st.CS.cs_wire_log.CL.raw_received pending) /\
        Seq.equal wire_sent st.CS.cs_wire_log.CL.raw_sent /\
        app_log == TChannel.application_log st)
      (ensures
        CI.channel_state_valid
          CP.client_protocol_implementation
          DS.client_driver_canonical
          TChannel.application_log
          d
          wire_received
          wire_sent
          pending
          app_log)
=
  Seq.lemma_eq_elim wire_sent st.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim
    wire_received
    (B.append st.CS.cs_wire_log.CL.raw_received pending);
  assert (exists state consumed_received.
    Seq.equal
      wire_received
      (Seq.append consumed_received pending) /\
    Common.WireFormatStateMachine.valid_byte_trace
      (CP.client_protocol_implementation.CPI.pi_system
        (DS.client_driver_canonical d))
      consumed_received
      state
      wire_sent
      Seq.empty /\
    app_log == TChannel.application_log state)

let lemma_channel_snapshot_ahead
  (d:DS.client_driver)
  (old_received:B.bytes)
  (old_sent:B.bytes)
  (old_log:CI.application_log B.bytes)
  (new_received:B.bytes)
  (new_sent:B.bytes)
  (new_log:CI.application_log B.bytes)
  (old_st:CS.connection_state)
  (new_st:CS.connection_state)
  : Lemma
      (requires
        CPI.state_ahead
          (CP.client_protocol_implementation.CPI.pi_system
            (DS.client_driver_canonical d))
          old_st
          new_st /\
        CPI.histories_ahead
          old_received
          old_sent
          new_received
          new_sent /\
        CI.application_log_extends old_log new_log /\
        old_log == TChannel.application_log old_st /\
        new_log == TChannel.application_log new_st)
      (ensures
        CI.channel_snapshot_ahead
          CP.client_protocol_implementation
          DS.client_driver_canonical
          TChannel.application_log
          d
          old_received
          old_sent
          old_log
          new_received
          new_sent
          new_log)
=
  assert (exists old_state new_state.
    old_log == TChannel.application_log old_state /\
    new_log == TChannel.application_log new_state /\
    CPI.state_ahead
      (CP.client_protocol_implementation.CPI.pi_system
        (DS.client_driver_canonical d))
      old_state
      new_state)

let lemma_local_send_application_log
  (st0 st1:CS.connection_state)
  (resp:CT.client_response)
  (payload:B.bytes)
  (network_out app_out:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0
          st1
          resp
          CT.LocalSendApplicationData
          payload
          network_out
          app_out)
      (ensures
        TChannel.application_log st1 ==
          (if resp.CT.status == CT.StepOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  assert (CT.local_event_step_correct
    st0
    st1
    resp
    CT.LocalSendApplicationData
    payload
    network_out
    app_out);
  assert (CT.legal_handled_local_response
    st0
    st1
    resp
    CT.LocalSendApplicationData
    payload
    network_out
    app_out);
  if resp.CT.status == CT.StepOk then (
    assert (exists ev raw_sent raw_received.
      CT.legal_local_response
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        ev
        raw_sent
        raw_received
        network_out
        app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            ev
            raw_sent
            raw_received
            network_out
            app_out) in
    CT.lemma_legal_response_for_event_app_log_delta
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CSL.conn_event_app_sent_delta ev == [payload]);
    assert (CSL.conn_event_app_received_delta ev == []);
    assert (TChannel.application_log st1 ==
      CI.append_sent (TChannel.application_log st0) payload)
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    CT.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    CT.lemma_legal_response_for_event_app_log_delta
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (TChannel.application_log st1 == TChannel.application_log st0)
  )

let lemma_driver_send_application_log
  (st0 st1:CS.connection_state)
  (status:DS.driver_workflow_status)
  (payload sent0 sent1:B.bytes)
  : Lemma
      (requires
        DS.client_driver_send_correct
          st0 st1 status payload sent0 sent1)
      (ensures
        TChannel.application_log st1 ==
          (if status == DS.DriverWorkflowOk
           then CI.append_sent (TChannel.application_log st0) payload
           else TChannel.application_log st0))
=
  if status == DS.DriverWorkflowPayloadTooLarge then ()
  else (
    assert (exists resp.
      DS.client_driver_local_write_correct
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        sent0
        sent1 /\
      DS.client_driver_send_status_correct status resp);
    let resp =
      ID.indefinite_description_ghost
        CT.client_response
        (fun resp ->
          DS.client_driver_local_write_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            sent0
            sent1 /\
          DS.client_driver_send_status_correct status resp) in
    assert (exists network_out app_out.
      CT.local_event_end_to_end_correct
        st0
        st1
        resp
        CT.LocalSendApplicationData
        payload
        network_out
        app_out /\
      Seq.equal
        sent1
        (B.append sent0 (CT.response_network_out resp network_out)));
    let network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun network_out -> exists app_out.
          CT.local_event_end_to_end_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            network_out
            app_out /\
          Seq.equal
            sent1
            (B.append sent0 (CT.response_network_out resp network_out))) in
    let app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun app_out ->
          CT.local_event_end_to_end_correct
            st0
            st1
            resp
            CT.LocalSendApplicationData
            payload
            network_out
            app_out /\
          Seq.equal
            sent1
            (B.append sent0 (CT.response_network_out resp network_out))) in
    lemma_local_send_application_log
      st0 st1 resp payload network_out app_out
  )

let lemma_legal_response_observable_receive_log
  (st0 st1:CS.connection_state)
  (resp:CT.client_response)
  (ev:CS.conn_event)
  (raw_sent raw_received network_out app_out:B.bytes)
  : Lemma
      (requires
        CT.legal_response_for_event
          st0 st1 resp ev raw_sent raw_received network_out app_out /\
        CSL.conn_event_app_sent_delta ev == [])
      (ensures
        (let output = CT.response_app_out resp app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output)))
=
  CT.lemma_legal_response_for_event_app_log_delta
    st0 st1 resp ev raw_sent raw_received network_out app_out;
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData _ ->
       assert False
     | CL.Received, M.TlsApplicationData bytes ->
       assert (Seq.equal (CT.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _, _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])
  | CS.ConnProtectedHandshake _ ->
    TChannel.lemma_observable_received_append
      st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
      []
  (* A cleartext buffering step delivers no application data. *)
  | CS.ConnCleartextHandshake _ ->
    TChannel.lemma_observable_received_append
      st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
      []
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalDeliverApplicationData bytes ->
       assert (Seq.equal (CT.response_app_out resp app_out) bytes);
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [bytes]
     | _ ->
       TChannel.lemma_observable_received_append
         st0.CS.cs_model.CS.model_application.CS.app_log.CL.app_received
         [])

let lemma_non_application_local_event_deltas
  (st:CS.connection_state)
  (kind:CT.local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : Lemma
      (requires
        CT.local_event_kind_matches st kind payload ev /\
        kind <> CT.LocalDeliverApplicationData /\
        kind <> CT.LocalSendApplicationData)
      (ensures
        CSL.conn_event_app_sent_delta ev == [] /\
        CSL.conn_event_app_received_delta ev == [])
=
  match kind, ev with
  | CT.LocalDeliverApplicationData, _ -> assert False
  | CT.LocalSendApplicationData, _ -> assert False
  | _, _ -> ()

#push-options "--z3rlimit 50"
let lemma_network_response_app_out_length
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        D.drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        B.length (CT.response_app_out buffer_resp.CT.response app_out) ==
          SZ.v buffer_resp.CT.response.CT.app_out_len)
=
  let st_mid =
    D.drained_network_middle
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out in
  let st1 = st_mid in
  let resp = buffer_resp.CT.response in
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp network_input
    old_network_out network_out old_app_out app_out);
  if CT.response_stuttered
       st0 st1 resp old_network_out network_out old_app_out app_out
  then (
    Seq.lemma_len_slice app_out 0 0
  ) else (
    assert (CT.some_legal_response st0 st1 resp network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_response_for_event
            st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_response_for_event
            st0 st1 resp ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_response_for_event
            st0 st1 resp ev raw_sent raw_received network_out app_out) in
    // Name the witness's defining property before projecting [response_wf] out
    // of it.  Without this step Z3 has to rediscover it underneath the whole
    // connection-state invariant, which is exactly the search that gets more
    // expensive whenever that invariant grows.
    assert (CT.legal_response_for_event
      st0 st1 resp ev raw_sent raw_received network_out app_out);
    CT.lemma_legal_response_for_event_wf
      st0 st1 resp ev raw_sent raw_received network_out app_out;
    assert (CT.response_wf resp network_out app_out);
    Seq.lemma_len_slice app_out 0 (SZ.v resp.CT.app_out_len)
  )

let lemma_receive_observation_app_out_length
  (st0 st1:CS.connection_state)
  (obs:DS.client_receive_observation)
  (app_out:B.bytes)
  : Lemma
      (requires
        DS.client_receive_observation_network_correct st0 st1 obs app_out)
      (ensures
        obs.DS.client_receive_observed_status == DS.DriverWorkflowOk ==>
        B.length
          (CT.response_app_out
            obs.DS.client_receive_observed_response.CT.response
            app_out) ==
          SZ.v
            obs.DS.client_receive_observed_response.CT.response.CT.app_out_len)
=
  if obs.DS.client_receive_observed_status == DS.DriverWorkflowOk then (
    assert (exists st_network st_before input old_network_out network_out old_app_out observed_app_out.
      D.drained_network_bytes_end_to_end_correct
        st_before
        st_network
        obs.DS.client_receive_observed_response
        input
        old_network_out
        network_out
        old_app_out
        observed_app_out /\
      st_network == st1 /\
      Seq.equal observed_app_out app_out);
    let st_before =
      ID.indefinite_description_ghost
        CS.connection_state
        (fun st_before -> exists st_network input old_network_out network_out old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    let input =
      ID.indefinite_description_ghost
        B.bytes
        (fun input -> exists st_network old_network_out network_out old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    let old_network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun old_network_out -> exists st_network network_out old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    let network_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun network_out -> exists st_network old_app_out observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    let old_app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun old_app_out -> exists st_network observed_app_out.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    let observed_app_out =
      ID.indefinite_description_ghost
        B.bytes
        (fun observed_app_out -> exists st_network.
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    assert (exists st_network.
      D.drained_network_bytes_end_to_end_correct
        st_before
        st_network
        obs.DS.client_receive_observed_response
        input
        old_network_out
        network_out
        old_app_out
        observed_app_out /\
      st_network == st1 /\
      Seq.equal observed_app_out app_out);
    let st_network =
      ID.indefinite_description_ghost
        CS.connection_state
        (fun st_network ->
          D.drained_network_bytes_end_to_end_correct
            st_before
            st_network
            obs.DS.client_receive_observed_response
            input
            old_network_out
            network_out
            old_app_out
            observed_app_out /\
          st_network == st1 /\
          Seq.equal observed_app_out app_out) in
    lemma_network_response_app_out_length
      st_before
      st_network
      obs.DS.client_receive_observed_response
      input
      old_network_out
      network_out
      old_app_out
      observed_app_out
  )

let lemma_receive_local_application_log
  (st0 st1:CS.connection_state)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        CT.local_event_end_to_end_correct
          st0 st1 resp kind payload network_out app_out /\
        kind <> CT.LocalDeliverApplicationData /\
        kind <> CT.LocalSendApplicationData)
      (ensures
        TChannel.application_log st1 == TChannel.application_log st0)
=
  assert (CT.legal_handled_local_response
    st0 st1 resp kind payload network_out app_out);
  if resp.CT.status == CT.StepOk then (
    assert (exists ev raw_sent raw_received.
      CT.legal_local_response
        st0 st1 resp kind payload ev raw_sent raw_received network_out app_out);
    let ev =
      ID.indefinite_description_ghost
        CS.conn_event
        (fun ev -> exists raw_sent raw_received.
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_sent =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_sent -> exists raw_received.
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          CT.legal_local_response
            st0 st1 resp kind payload ev raw_sent raw_received network_out app_out) in
    assert (CT.local_event_kind_matches st0 kind payload ev);
    assert (CT.response_app_out_matches_event resp ev app_out);
    lemma_non_application_local_event_deltas st0 kind payload ev;
    assert (CSL.conn_event_app_sent_delta ev == []);
    assert (B.length (CT.response_app_out resp app_out) == 0);
    lemma_legal_response_observable_receive_log
      st0 st1 resp ev raw_sent raw_received network_out app_out
  ) else if CT.unexpected_message_response st0 st1 resp network_out app_out then (
    assert (B.length (CT.response_app_out resp app_out) == 0);
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out
  ) else (
    assert (CT.bad_finished_response st0 st1 resp network_out app_out);
    assert (B.length (CT.response_app_out resp app_out) == 0);
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_bad_finished_error))
      B.empty
      B.empty
      network_out
      app_out
  )

let lemma_optional_receive_local_application_log
  (st0 st1:CS.connection_state)
  (processed:bool)
  (resp:CT.client_response)
  (kind:CT.local_event_kind)
  (payload network_out app_out:B.bytes)
  : Lemma
      (requires
        (processed ==>
          CT.local_event_end_to_end_correct
            st0 st1 resp kind payload network_out app_out /\
          kind <> CT.LocalDeliverApplicationData /\
          kind <> CT.LocalSendApplicationData) /\
        (processed == false ==> st1 == st0))
      (ensures
        TChannel.application_log st1 == TChannel.application_log st0)
=
  if processed then
    lemma_receive_local_application_log
      st0 st1 resp kind payload network_out app_out
  else
    assert (st1 == st0)

(** ---------------------------------------------------------------------- *)
(** Drain steps are application-invisible                                   *)
(** ---------------------------------------------------------------------- *)

/// A drain step carries a [ConnProtectedHandshake] event with no application
/// bytes, so it leaves the channel's application log untouched.  This is the
/// property that lets a drained receive call keep the channel specification it
/// had before the drain was introduced.
let lemma_drain_step_application_log (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drain_step st0 st1)
      (ensures TChannel.application_log st1 == TChannel.application_log st0)
=
  let (resp, step) = D.drain_step_witness st0 st1 in
  assert (B.length (CT.response_app_out resp B.empty) == 0);
  lemma_legal_response_observable_receive_log
    st0 st1 resp (CS.ConnProtectedHandshake step)
    B.empty B.empty B.empty B.empty

#push-options "--fuel 2 --ifuel 2"
let rec lemma_drain_chain_application_log (n:nat) (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drain_chain n st0 st1)
      (ensures TChannel.application_log st1 == TChannel.application_log st0)
      (decreases n)
=
  if n = 0
  then ()
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/ (exists st'. D.drain_step st0 st' /\ D.drain_chain m st' st1)
    with ()
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> D.drain_step st0 st' /\ D.drain_chain m st' st1) in
       lemma_drain_step_application_log st0 st';
       lemma_drain_chain_application_log m st' st1)
#pop-options

let lemma_drained_application_log (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drained st0 st1)
      (ensures TChannel.application_log st1 == TChannel.application_log st0)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> D.drain_chain n st0 st1) in
  lemma_drain_chain_application_log n st0 st1

let lemma_network_bytes_application_log_undrained
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        CT.coalesced_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        (let output = CT.response_app_out buffer_resp.CT.response app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output)))
=
  let resp = buffer_resp.CT.response in
  if not (CT.network_bytes_end_to_end_correct
            st0 st1 buffer_resp network_input
            old_network_out network_out old_app_out app_out)
  then (
    // Head weak step (protected or cleartext buffering): the event carries no
    // application bytes.
    let ev =
      CP.lemma_client_coalesced_head_step
        st0 st1 buffer_resp network_input
        old_network_out network_out old_app_out app_out in
    let raw_received =
      CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len in
    lemma_legal_response_observable_receive_log
      st0 st1 resp
      ev
      B.empty raw_received network_out app_out
  ) else (
  assert (CT.network_bytes_step_correct
    st0 st1 buffer_resp network_input
    old_network_out network_out old_app_out app_out);
  if CT.response_stuttered
       st0 st1 resp old_network_out network_out old_app_out app_out
  then
    assert (st1 == st0)
  else if resp.CT.status == CT.DecodeError then (
    assert (CT.decode_error_response st0 st1 resp network_out app_out);
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out
  ) else if
      resp.CT.status == CT.IllegalTransition &&
      buffer_resp.CT.consumed_len = 0sz
  then (
    assert (CT.unexpected_message_response st0 st1 resp network_out app_out);
    lemma_legal_response_observable_receive_log
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
      B.empty
      B.empty
      network_out
      app_out
  ) else (
    let raw_received =
      CT.network_consumed_prefix network_input buffer_resp.CT.consumed_len in
    assert (CT.raw_record_parse_success raw_received);
    if buffer_resp.CT.consumed_len = 0sz then (
      CT.lemma_raw_record_parse_success_nonempty raw_received;
      assert (SZ.v buffer_resp.CT.consumed_len == 0);
      assert (raw_received == Seq.slice network_input 0 0);
      Seq.lemma_len_slice network_input 0 0;
      assert (B.length raw_received == 0);
      assert False
    );
    assert (CT.network_bytes_decoded_message_projection
      st0 st1 buffer_resp network_input network_out app_out);
    assert (exists content_type fragment msg.
      CT.network_input_message_projection
        st0 content_type fragment msg raw_received /\
      CT.decoded_message_event_projection
        st0 st1 resp msg raw_received network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg -> exists content_type fragment.
          CT.network_input_message_projection
            st0 content_type fragment msg raw_received /\
          CT.decoded_message_event_projection
            st0 st1 resp msg raw_received network_out app_out) in
    assert (CT.decoded_message_event_projection
      st0 st1 resp msg raw_received network_out app_out);
    if CT.legal_received_tls_response
         st0 st1 resp msg raw_received network_out app_out
    then
      lemma_legal_response_observable_receive_log
        st0
        st1
        resp
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = msg;
        })
        B.empty
        raw_received
        network_out
        app_out
    else (
      assert (CT.unexpected_message_response st0 st1 resp network_out app_out);
      lemma_legal_response_observable_receive_log
        st0
        st1
        resp
        (CS.ConnLocalEvent (CS.LocalFail CT.tls_unexpected_message_error))
        B.empty
        B.empty
        network_out
        app_out
    )
  )
  )
#pop-options

/// The drained form.  The drain adds no application bytes, so the channel's
/// application log after the whole call is the one the undrained step already
/// characterised.
let lemma_network_bytes_application_log
  (st0 st1:CS.connection_state)
  (buffer_resp:CT.client_buffer_response)
  (network_input old_network_out network_out old_app_out app_out:B.bytes)
  : Lemma
      (requires
        D.drained_network_bytes_end_to_end_correct
          st0 st1 buffer_resp network_input
          old_network_out network_out old_app_out app_out)
      (ensures
        (let output = CT.response_app_out buffer_resp.CT.response app_out in
         TChannel.application_log st1 ==
           (if B.length output == 0
            then TChannel.application_log st0
            else CI.append_received (TChannel.application_log st0) output)))
=
  let st_mid =
    D.drained_network_middle
      st0 st1 buffer_resp network_input
      old_network_out network_out old_app_out app_out in
  lemma_network_bytes_application_log_undrained
    st0 st_mid buffer_resp network_input
    old_network_out network_out old_app_out app_out;
  lemma_drained_application_log st_mid st1



ghost fn open_channel_invariant
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    exists* st.
      DS.client_driver_connected
        d
        st
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent) **
      pure (
        (Ghost.reveal app_log) == TChannel.application_log st /\
        CT.connection_control_not_failed st /\
        Seq.equal
          (Ghost.reveal wire_received)
          (B.append st.CS.cs_wire_log.CL.raw_received (Ghost.reveal pending)) /\
        Seq.equal (Ghost.reveal wire_sent) st.CS.cs_wire_log.CL.raw_sent)
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len. _;
  unfold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  unfold (CP.client_invariant
    (DS.client_driver_canonical d)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
    st);
  fold (DS.client_driver_canonical_progress d st);
  rewrite
    (DS.client_driver_canonical_progress d st)
    as
    (DS.buffered_driver_canonical_progress
      (DS.client_buffered_driver d channel)
      st);
  fold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    st
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal wire_received)
    committed
    (Ghost.reveal wire_sent));
  fold (DS.client_driver_connected_indexed
    d
    st
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    channel
    model
    committed
    buffered_len);
  fold (DS.client_driver_connected
    d st (Ghost.reveal wire_received) (Ghost.reveal wire_sent))
}

ghost fn open_io_channel
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns ch:IO.channel
  ensures
    IO.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.client_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len. _;
  unfold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  let ch = Common.BufferedTCP.open_io_channel channel;
  fold (DS.client_channel_io_frame_indexed
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_io_frame
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  ch
}

ghost fn close_io_channel
  (d:DS.client_driver)
  (ch:IO.channel)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    IO.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.client_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
{
  unfold (DS.client_channel_io_frame
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len.
    assert (DS.client_channel_io_frame_indexed
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
      st
      channel
      model
      committed
      buffered_len);
  unfold (DS.client_channel_io_frame_indexed
    d
    ch
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  Common.BufferedTCP.close_io_channel channel ch;
  fold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

ghost fn pack_connected_channel_invariant
  (d:DS.client_driver)
  (st:Ghost.erased CS.connection_state)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (CT.connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* pending.
      DS.client_channel_inv
        d
        (Ghost.reveal received)
        (Ghost.reveal sent)
        pending
        (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.client_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with channel model committed buffered_len. _;
  unfold (DS.client_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    channel
    model
    committed
    buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st)
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal received)
    committed
    (Ghost.reveal sent));
  let consumed =
    DS.choose_wire_logs_match_witness
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Common.BufferedTCP.pending model)
      buffered_len;
  assert (pure (
    Seq.equal
      (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
      (Ghost.reveal consumed)));
  Seq.lemma_eq_elim
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed);
  assert (pure (
    Seq.equal
      (Ghost.reveal received)
      (B.append
        (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
        (Common.BufferedTCP.pending model))));
  unfold (DS.buffered_driver_canonical_progress
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st));
  fold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  assert (pure (
    DS.client_driver_wire_logs_match_witness
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      committed
      (Common.BufferedTCP.pending model)
      buffered_len /\
    SZ.v buffered_len ==
      B.length (Common.BufferedTCP.pending model)));
  fold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Common.BufferedTCP.pending model)
    (TChannel.application_log (Ghost.reveal st))
    (Ghost.reveal st)
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_inv
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Common.BufferedTCP.pending model)
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_connected_channel_terminal
  (d:DS.client_driver)
  (st:Ghost.erased CS.connection_state)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent)
  ensures
    DS.client_channel_terminal
      d
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (TChannel.application_log (Ghost.reveal st))
{
  unfold (DS.client_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent));
  with channel model committed buffered_len. _;
  unfold (DS.client_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    channel
    model
    committed
    buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st)
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal received)
    committed
    (Ghost.reveal sent));
  unfold (DS.buffered_driver_canonical_progress
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st));
  fold (CP.client_invariant
    (DS.client_driver_canonical d)
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_received
    (Ghost.reveal st).CS.cs_wire_log.CL.raw_sent
    (Ghost.reveal st));
  assert (pure (
    DS.client_driver_wire_logs_match_witness
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent)
      committed
      (Common.BufferedTCP.pending model)
      buffered_len /\
    SZ.v buffered_len ==
      B.length (Common.BufferedTCP.pending model)));
  fold (DS.client_channel_terminal_indexed
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st))
    (Ghost.reveal st)
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_terminal
    d
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (TChannel.application_log (Ghost.reveal st)))
}

ghost fn pack_connected_channel
  (d:DS.client_driver)
  (st:Ghost.erased CS.connection_state)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (CT.connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* wire_received wire_sent pending app_log.
      DS.client_channel_inv d wire_received wire_sent pending app_log
{
  pack_connected_channel_invariant
    d st received sent
}

ghost fn channel_invariant_valid
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    pure (
      CI.channel_state_valid
        CP.client_protocol_implementation
        DS.client_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
        (Ghost.reveal pending)
        (Ghost.reveal app_log))
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len. _;
  unfold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  CP.client_invariant_valid
    (DS.client_driver_canonical d)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide st);
  lemma_channel_state_valid
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st;
  fold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

ghost fn pack_channel_snapshot
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  requires
    CP.client_snapshot
      (DS.client_driver_canonical d)
      st.CS.cs_wire_log.CL.raw_received
      st.CS.cs_wire_log.CL.raw_sent
      st **
    MR.snapshot
      d.DS.client_driver_tcp_history
      (DS.wire_history (Ghost.reveal wire_received) (Ghost.reveal wire_sent)) **
    pure ((Ghost.reveal app_log) == TChannel.application_log st)
  ensures
    DS.client_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  fold (DS.client_channel_snapshot
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log))
}

ghost fn take_channel_snapshot
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.client_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log) **
    DS.client_channel_snapshot
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
{
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len. _;
  unfold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  CP.take_client_snapshot
    (DS.client_driver_canonical d)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide st);
  MR.take_snapshot
    d.DS.client_driver_tcp_history
    (DS.wire_history (Ghost.reveal wire_received) (Ghost.reveal wire_sent));
  pack_channel_snapshot
    d
    wire_received
    wire_sent
    app_log
    (Ghost.hide st);
  fold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_inv
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal pending)
    (Ghost.reveal app_log))
}

ghost fn recall_channel_snapshot
  (d:DS.client_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  (new_pending:Ghost.erased B.bytes)
  (new_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_pending)
      (Ghost.reveal new_log)
  ensures
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_channel_inv
      d
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
      (Ghost.reveal new_pending)
      (Ghost.reveal new_log) **
    pure (
      CI.channel_snapshot_ahead
        CP.client_protocol_implementation
        DS.client_driver_canonical
        TChannel.application_log
        d
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal old_log)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent)
        (Ghost.reveal new_log))
{
  unfold (DS.client_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st. _;
  dup (MR.snapshot
    d.DS.client_driver_tcp_history
    (DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent))) ();
  unfold (CP.client_snapshot
    (DS.client_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  assert (pure (CSL.connection_state_app_log_consistent old_st));
  fold (CP.client_snapshot
    (DS.client_driver_canonical d)
    old_st.CS.cs_wire_log.CL.raw_received
    old_st.CS.cs_wire_log.CL.raw_sent
    old_st);
  unfold (DS.client_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log));
  with new_st channel model committed buffered_len. _;
  unfold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log)
    new_st
    channel
    model
    committed
    buffered_len);
  unfold (CP.client_invariant
    (DS.client_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  assert (pure (CSL.connection_state_app_log_consistent new_st));
  fold (CP.client_invariant
    (DS.client_driver_canonical d)
    new_st.CS.cs_wire_log.CL.raw_received
    new_st.CS.cs_wire_log.CL.raw_sent
    new_st);
  CP.recall_client_snapshot
    (DS.client_driver_canonical d)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide old_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide old_st)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_received)
    (Ghost.hide new_st.CS.cs_wire_log.CL.raw_sent)
    (Ghost.hide new_st);
  MR.recall_snapshot
    d.DS.client_driver_tcp_history
    #1.0R
    #(DS.wire_history (Ghost.reveal new_received) (Ghost.reveal new_sent))
    #(DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent));
  CI.lemma_io_history_preorder_extends
    (DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent))
    (DS.wire_history (Ghost.reveal new_received) (Ghost.reveal new_sent));
  assert (pure (CPI.histories_ahead
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)));
  TChannel.lemma_application_log_extends_from_event_logs old_st new_st;
  lemma_channel_snapshot_ahead
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_log)
    old_st
    new_st;
  pack_channel_snapshot
    d
    old_received
    old_sent
    old_log
    (Ghost.hide old_st);
  fold (DS.client_channel_inv_indexed
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log)
    new_st
    channel
    model
    committed
    buffered_len);
  fold (DS.client_channel_inv
    d
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    (Ghost.reveal new_pending)
    (Ghost.reveal new_log))
}

ghost fn recall_tcp_history
  (d:DS.client_driver)
  (old_received:Ghost.erased B.bytes)
  (old_sent:Ghost.erased B.bytes)
  (old_log:Ghost.erased (CI.application_log B.bytes))
  (st:Ghost.erased CS.connection_state)
  (new_received:Ghost.erased B.bytes)
  (new_sent:Ghost.erased B.bytes)
  requires
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent)
  ensures
    DS.client_channel_snapshot
      d
      (Ghost.reveal old_received)
      (Ghost.reveal old_sent)
      (Ghost.reveal old_log) **
    DS.client_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal new_received)
      (Ghost.reveal new_sent) **
    pure (
      CPI.histories_ahead
        (Ghost.reveal old_received)
        (Ghost.reveal old_sent)
        (Ghost.reveal new_received)
        (Ghost.reveal new_sent))
{
  unfold (DS.client_channel_snapshot
    d
    (Ghost.reveal old_received)
    (Ghost.reveal old_sent)
    (Ghost.reveal old_log));
  with old_st. _;
  dup (MR.snapshot
    d.DS.client_driver_tcp_history
    (DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent))) ();
  unfold (DS.client_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent));
  with channel model committed buffered_len. _;
  unfold (DS.client_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    channel
    model
    committed
    buffered_len);
  unfold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st)
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal new_received)
    committed
    (Ghost.reveal new_sent));
  MR.recall_snapshot
    d.DS.client_driver_tcp_history
    #1.0R
    #(DS.wire_history (Ghost.reveal new_received) (Ghost.reveal new_sent))
    #(DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent));
  CI.lemma_io_history_preorder_extends
    (DS.wire_history (Ghost.reveal old_received) (Ghost.reveal old_sent))
    (DS.wire_history (Ghost.reveal new_received) (Ghost.reveal new_sent));
  fold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    (Ghost.reveal st)
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal new_received)
    committed
    (Ghost.reveal new_sent));
  fold (DS.client_driver_connected_indexed
    d
    (Ghost.reveal st)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent)
    channel
    model
    committed
    buffered_len);
  fold (DS.client_driver_connected
    d
    (Ghost.reveal st)
    (Ghost.reveal new_received)
    (Ghost.reveal new_sent));
  pack_channel_snapshot
    d
    old_received
    old_sent
    old_log
    (Ghost.hide old_st)
}

(* Re-open a hard-failed (terminal) channel as a [client_driver_connected]
   bundle so the ordinary abort/cleanup path can consume it. Unlike
   [open_channel_invariant] this makes no claim about [connection_control_not_failed]
   or the pending decomposition, so it applies to StepFailed/Closed states whose
   control may be failed; [client_driver_connected] does not require a live
   connection, only that the physical transport is still owned. *)
ghost fn open_terminal
  (d:DS.client_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.client_channel_terminal
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st.
      DS.client_driver_connected
        d
        st
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)
{
  unfold (DS.client_channel_terminal
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log));
  with st channel model committed buffered_len. _;
  unfold (DS.client_channel_terminal_indexed
    d
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    (Ghost.reveal app_log)
    st
    channel
    model
    committed
    buffered_len);
  unfold (CP.client_invariant
    (DS.client_driver_canonical d)
    st.CS.cs_wire_log.CL.raw_received
    st.CS.cs_wire_log.CL.raw_sent
    st);
  fold (DS.client_driver_canonical_progress d st);
  rewrite
    (DS.client_driver_canonical_progress d st)
    as
    (DS.buffered_driver_canonical_progress
      (DS.client_buffered_driver d channel)
      st);
  fold (DS.buffered_driver_indexed
    (DS.client_buffered_driver d channel)
    st
    (Common.BufferedTCP.pending model)
    buffered_len
    model
    (Ghost.reveal wire_received)
    committed
    (Ghost.reveal wire_sent));
  fold (DS.client_driver_connected_indexed
    d
    st
    (Ghost.reveal wire_received)
    (Ghost.reveal wire_sent)
    channel
    model
    committed
    buffered_len);
  fold (DS.client_driver_connected
    d st (Ghost.reveal wire_received) (Ghost.reveal wire_sent))
}

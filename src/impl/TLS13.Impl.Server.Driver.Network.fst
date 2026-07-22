module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BT = Common.BufferedTCP.Internal
module BS = Common.BufferedStream
module CI = Common.ChannelImplementation
module A = Pulse.Lib.Array
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ID = FStar.IndefiniteDescription
module IO = Common.TCP
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module NO = TLS13.Impl.Server.Driver.NetworkOrdered
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module SP = TLS13.Impl.Server.CanonicalProtocol
module SZ = FStar.SizeT
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module U8 = FStar.UInt8
module Box = Pulse.Lib.Box

#push-options "--using_facts_from '*'"
module V = Pulse.Lib.Vec

open TLS13.Impl.Server.Driver.State

noextract
let server_buffer_read_decision
  (resp:ST.server_buffer_response)
  =
  if resp.ST.response.ST.status == ST.NeedMoreInput
  then (BS.NeedMore <: BS.classification unit unit)
  else (BS.Reject () <: BS.classification unit unit)

let lemma_control_snapshot_client_hello_received
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 1uy /\
        snapshot.CR.snapshot_handshake_stage_tag == 13uy)
      (ensures
        st.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived)
=
  assert_norm (U8.v 1uy == 1);
  assert_norm (U8.v 13uy == 13);
  assert (U8.v snapshot.CR.snapshot_control_tag == 1);
  assert (U8.v snapshot.CR.snapshot_handshake_stage_tag == 13);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlHandshaking stage ->
    match stage with
    | CS.HsClientHelloReceived -> ()
    | _ -> assert False
  | _ -> assert False

let lemma_server_driver_network_process_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes)))
      (ensures server_driver_network_process_correct
        st0 st1 resp sent sent')
=
  FStar.Classical.exists_intro
    (fun app_out_bytes' ->
      ST.server_network_bytes_end_to_end_correct
        st0 st1 resp input network_out_bytes app_out_bytes' /\
      ST.server_network_consumed_input_projection
        st0 st1 resp input network_out_bytes app_out_bytes' /\
      Seq.equal
        sent'
        (B.append
          sent
          (ST.response_network_out resp.ST.response network_out_bytes)))
    app_out_bytes;
  FStar.Classical.exists_intro
    (fun network_out_bytes' ->
      exists app_out_bytes'.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes' app_out_bytes' /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes' app_out_bytes' /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes')))
    network_out_bytes;
  FStar.Classical.exists_intro
    (fun input' ->
      exists network_out_bytes' app_out_bytes'.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input' network_out_bytes' app_out_bytes' /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input' network_out_bytes' app_out_bytes' /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes')))
    input

let lemma_server_driver_network_process_correct_for_app_out_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0
          st1
          resp
          input
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes)))
      (ensures server_driver_network_process_correct_for_app_out
        st0 st1 resp sent sent' app_out_bytes)
=
  FStar.Classical.exists_intro
    (fun network_out_bytes' ->
      ST.server_network_bytes_end_to_end_correct
        st0 st1 resp input network_out_bytes' app_out_bytes /\
      ST.server_network_consumed_input_projection
        st0 st1 resp input network_out_bytes' app_out_bytes /\
      Seq.equal
        sent'
        (B.append
          sent
          (ST.response_network_out resp.ST.response network_out_bytes')))
    network_out_bytes;
  FStar.Classical.exists_intro
    (fun input' ->
      exists network_out_bytes'.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input' network_out_bytes' app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input' network_out_bytes' app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes')))
    input

let lemma_server_driver_network_process_need_more_stutter
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        server_driver_network_process_correct st0 st1 resp sent sent' /\
        resp.ST.response.ST.status == ST.NeedMoreInput)
      (ensures
        st1 == st0 /\
        Seq.equal sent' sent)
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out_bytes app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  assert (ST.server_network_consumed_input_projection
    st0 st1 resp input network_out_bytes app_out_bytes);
  assert (st1 == st0);
  assert (resp.ST.response.ST.network_out_len == 0sz);
  Seq.lemma_len_slice network_out_bytes 0 0;
  Seq.lemma_eq_intro B.empty (ST.response_network_out resp.ST.response network_out_bytes);
  Seq.lemma_eq_elim
    (ST.response_network_out resp.ST.response network_out_bytes)
    B.empty;
  Seq.append_empty_r sent;
  assert (Seq.equal
    sent'
    (B.append sent (ST.response_network_out resp.ST.response network_out_bytes)));
  assert (Seq.equal sent' sent)

let lemma_server_driver_network_process_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires server_driver_network_process_correct st0 st1 resp sent sent')
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out_bytes app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  assert (ST.server_network_consumed_input_projection
    st0 st1 resp input network_out_bytes app_out_bytes);
  ST.lemma_server_network_bytes_preserves_config
    st0
    st1
    resp
    input
    network_out_bytes
    app_out_bytes

let lemma_server_driver_supported_profile_selection_same_config_and_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        server_driver_supported_profile_selection st0 credential_identity /\
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config /\
        st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
          st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection /\
        server_driver_selection_present_when_required st1)
      (ensures
        server_driver_supported_profile_selection st1 credential_identity)
=
  ()

let lemma_legal_response_for_event_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.legal_response_for_event
          st0
          st1
          resp
          ev
          raw_sent
          raw_received
          network_out
          app_out /\
        server_driver_supported_profile_selection st0 credential_identity /\
        (match ev with
         | CS.ConnNetworkEvent msg -> msg.CL.message_direction == CL.Received
         | CS.ConnLocalEvent (CS.LocalFail _) -> True
         | _ -> False))
      (ensures
        server_driver_supported_profile_selection st1 credential_identity)
=
  assert (CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1);
  assert (CS.step_model st0.CS.cs_model ev == Some st1.CS.cs_model);
  CSL.lemma_step_model_preserves_config st0.CS.cs_model ev st1.CS.cs_model;
  assert (
    st1.CS.cs_model.CS.model_config ==
      st0.CS.cs_model.CS.model_config);
  match ev with
  | CS.ConnLocalEvent (CS.LocalFail _) ->
    assert (
      st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    assert (server_driver_selection_present_when_required st1)
  | CS.ConnNetworkEvent msg ->
    assert (msg.CL.message_direction == CL.Received);
    assert (
      st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
        st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
    (match msg.CL.message_value with
     | M.TlsHandshake hs ->
       (match hs with
        | M.ClientHello _ ->
          assert (server_driver_selection_present_when_required st1)
        | M.Finished _ ->
          assert (server_driver_selection_present_when_required st1)
        | _ ->
          assert (server_driver_selection_present_when_required st1))
     | M.TlsApplicationData _ ->
       assert (server_driver_selection_present_when_required st1)
     | M.TlsAlert _ ->
       assert (server_driver_selection_present_when_required st1)
     | M.TlsChangeCipherSpec ->
       assert (server_driver_selection_present_when_required st1)
     | M.TlsIgnoredPostHandshake _ ->
       assert (server_driver_selection_present_when_required st1)
     | M.TlsKeyUpdate _ ->
       assert (server_driver_selection_present_when_required st1))
  | _ ->
    assert False;
  assert (
    st1.CS.cs_model.CS.model_handshake.CS.hs_server_selection ==
      st0.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  assert (server_driver_selection_present_when_required st1);
  lemma_server_driver_supported_profile_selection_same_config_and_selection
    st0
    st1
    credential_identity

let lemma_legal_network_response_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.legal_network_response
          st0
          st1
          resp
          msg
          raw_received
          network_out
          app_out /\
        server_driver_supported_profile_selection st0 credential_identity)
      (ensures
        server_driver_supported_profile_selection st1 credential_identity)
=
  assert (ST.legal_response_for_event
    st0
    st1
    resp
    (ST.received_message_event msg)
    B.empty
    raw_received
    network_out
    app_out);
  lemma_legal_response_for_event_preserves_supported_profile_selection
    st0
    st1
    resp
    (ST.received_message_event msg)
    B.empty
    raw_received
    network_out
    app_out
    credential_identity

let lemma_server_driver_network_process_correct_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        server_driver_network_process_correct st0 st1 resp sent sent' /\
        server_driver_supported_profile_selection st0 credential_identity)
      (ensures
        server_driver_supported_profile_selection st1 credential_identity)
=
  let input =
    ID.indefinite_description_ghost
      B.bytes
      (fun input -> exists network_out_bytes app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let network_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun network_out_bytes -> exists app_out_bytes.
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  let app_out_bytes =
    ID.indefinite_description_ghost
      B.bytes
      (fun app_out_bytes ->
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes))) in
  assert (ST.server_network_consumed_input_projection
    st0 st1 resp input network_out_bytes app_out_bytes);
  lemma_server_driver_network_process_correct_preserves_config
    st0
    st1
    resp
    sent
    sent';
  match resp.response.status with
  | ST.NeedMoreInput ->
    assert (st1 == st0)
  | ST.IllegalTransition ->
    assert (st1 == st0)
  | ST.OutputBufferTooSmall ->
    assert False
  | ST.DecodeError ->
    assert (ST.decode_error_response
      st0
      st1
      resp.ST.response
      network_out_bytes
      app_out_bytes);
    lemma_legal_response_for_event_preserves_supported_profile_selection
      st0
      st1
      resp.ST.response
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out_bytes
      app_out_bytes
      credential_identity
  | ST.ConnectionFailed ->
    assert (ST.server_network_connection_failed_consumed_prefix
      st0 st1 resp input network_out_bytes app_out_bytes);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix resp input) /\
          ST.legal_network_response
            st0
            st1
            resp.ST.response
            (M.TlsAlert alert)
            raw_received
            network_out_bytes
            app_out_bytes) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix resp input) /\
          ST.legal_network_response
            st0
            st1
            resp.ST.response
            (M.TlsAlert alert)
            raw_received
            network_out_bytes
            app_out_bytes) in
    assert (ST.legal_network_response
      st0
      st1
      resp.ST.response
      (M.TlsAlert alert)
      raw_received
      network_out_bytes
      app_out_bytes);
    lemma_legal_network_response_preserves_supported_profile_selection
      st0
      st1
      resp.ST.response
      (M.TlsAlert alert)
      raw_received
      network_out_bytes
      app_out_bytes
      credential_identity
  | ST.StepOk ->
    assert (ST.server_network_step_ok_received_decode_projection
      st0 st1 resp input network_out_bytes app_out_bytes);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal
            st0
            msg
            (ST.server_network_consumed_prefix resp input) /\
          ST.server_decoded_message_event_projection
            st0
            st1
            resp.ST.response
            msg
            (ST.server_network_consumed_prefix resp input)
            network_out_bytes
            app_out_bytes /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0
               (ST.server_network_consumed_prefix resp input)
               msg)) in
    assert (ST.server_decoded_message_event_projection
      st0
      st1
      resp.ST.response
      msg
      (ST.server_network_consumed_prefix resp input)
      network_out_bytes
      app_out_bytes);
    if ST.legal_network_response
      st0
      st1
      resp.ST.response
      msg
      (ST.server_network_consumed_prefix resp input)
      network_out_bytes
      app_out_bytes
    then
      lemma_legal_network_response_preserves_supported_profile_selection
        st0
        st1
        resp.ST.response
        msg
        (ST.server_network_consumed_prefix resp input)
        network_out_bytes
        app_out_bytes
        credential_identity
    else (
      assert (ST.unexpected_message_response
        st0
        st1
        resp.ST.response
        network_out_bytes
        app_out_bytes);
      assert (resp.ST.response.ST.status == ST.IllegalTransition);
      assert False
    )

let lemma_slice_append_full
  (s:B.bytes)
  (n:nat)
  : Lemma
      (requires n <= B.length s)
      (ensures Seq.equal
        (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s)))
        s)
=
  Seq.lemma_len_slice s 0 n;
  Seq.lemma_len_slice s n (B.length s);
  Seq.lemma_len_append (Seq.slice s 0 n) (Seq.slice s n (B.length s));
  assert (B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) ==
    B.length s);
  assert (forall (i:nat). i < B.length (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) ==>
    Seq.index (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) i ==
    Seq.index s i);
  Seq.lemma_eq_intro (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s))) s

let lemma_server_network_wire_accounting
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (old_consumed:B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        logged_received_bytes_accounted
          st0.CS.cs_wire_log.CL.raw_received
          old_consumed)
      (ensures
        SZ.v buffer_resp.ST.response.ST.network_out_len <= B.length network_out /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out buffer_resp.ST.response network_out)) /\
        logged_received_bytes_accounted
          st1.CS.cs_wire_log.CL.raw_received
          (B.append old_consumed
            (ST.server_network_consumed_prefix buffer_resp input)))
=
  let resp = buffer_resp.ST.response in
  match resp.ST.status with
  | ST.NeedMoreInput ->
    assert (st1 == st0);
    assert (buffer_resp.ST.consumed_len == 0sz);
    assert (resp.ST.network_out_len == 0sz);
    assert (SZ.v buffer_resp.ST.consumed_len <= B.length input);
    assert (ST.server_network_consumed_prefix buffer_resp input ==
      Seq.slice input 0 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (ST.response_network_out resp network_out);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.lemma_len_slice input 0 0;
    Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
    Seq.lemma_eq_elim
      (ST.server_network_consumed_prefix buffer_resp input)
      B.empty;
    assert (Seq.equal B.empty (ST.server_network_consumed_prefix buffer_resp input));
    Seq.append_empty_r old_consumed;
    assert (Seq.equal
      (B.append old_consumed (ST.server_network_consumed_prefix buffer_resp input))
      old_consumed)
  | ST.IllegalTransition ->
    assert (st1 == st0);
    assert (buffer_resp.ST.consumed_len == 0sz);
    assert (resp.ST.network_out_len == 0sz);
    assert (SZ.v buffer_resp.ST.consumed_len <= B.length input);
    assert (ST.server_network_consumed_prefix buffer_resp input ==
      Seq.slice input 0 0);
    Seq.lemma_len_slice network_out 0 0;
    Seq.lemma_eq_intro B.empty (ST.response_network_out resp network_out);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_sent;
    Seq.lemma_len_slice input 0 0;
    Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
    Seq.lemma_eq_elim
      (ST.server_network_consumed_prefix buffer_resp input)
      B.empty;
    assert (Seq.equal B.empty (ST.server_network_consumed_prefix buffer_resp input));
    Seq.append_empty_r old_consumed;
    assert (Seq.equal
      (B.append old_consumed (ST.server_network_consumed_prefix buffer_resp input))
      old_consumed)
  | ST.DecodeError ->
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      B.empty
      (ST.server_network_consumed_prefix buffer_resp input)
  | ST.OutputBufferTooSmall ->
    assert False
  | ST.StepOk ->
    assert (ST.server_network_step_ok_received_decode_projection
      st0 st1 buffer_resp input network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal
            st0
            msg
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.server_decoded_message_event_projection
            st0
            st1
            resp
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0
               (ST.server_network_consumed_prefix buffer_resp input)
               msg)) in
    assert (ST.server_decoded_message_event_projection
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out);
    if ST.legal_network_response
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out then (
      assert (ST.legal_response_for_event
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out);
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      lemma_legal_response_network_out_len
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
      Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
      lemma_logged_received_bytes_accounted_append_delta
        st0.CS.cs_wire_log.CL.raw_received
        old_consumed
        (ST.server_network_consumed_prefix buffer_resp input)
        (ST.server_network_consumed_prefix buffer_resp input)
    ) else (
      assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
      assert (resp.ST.status == ST.IllegalTransition);
      assert False
    )
  | ST.ConnectionFailed ->
    assert (ST.server_network_connection_failed_consumed_prefix
      st0 st1 buffer_resp input network_out app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input));
    assert (ST.legal_network_response
      st0
      st1
      resp
      (M.TlsAlert alert)
      raw_received
      network_out
      app_out);
    assert (ST.legal_response_for_event
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out;
    lemma_legal_response_network_out_len
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      raw_received
      network_out
      app_out;
    assert (Seq.equal (ST.response_network_out resp network_out) B.empty);
    Seq.lemma_eq_elim (ST.response_network_out resp network_out) B.empty;
    Seq.lemma_eq_elim raw_received (ST.server_network_consumed_prefix buffer_resp input);
    lemma_logged_received_bytes_accounted_append_delta
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      raw_received
      (ST.server_network_consumed_prefix buffer_resp input)

let lemma_server_network_zero_consumed_raw_received_unchanged
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        buffer_resp.ST.consumed_len == 0sz)
      (ensures
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_received
          st0.CS.cs_wire_log.CL.raw_received)
=
  let resp = buffer_resp.ST.response in
  assert (ST.server_network_consumed_prefix buffer_resp input ==
    Seq.slice input 0 0);
  Seq.lemma_len_slice input 0 0;
  Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
  assert (Seq.equal (ST.server_network_consumed_prefix buffer_resp input) B.empty);
  match resp.ST.status with
  | ST.NeedMoreInput ->
    assert (st1 == st0)
  | ST.IllegalTransition ->
    assert (st1 == st0)
  | ST.DecodeError ->
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
  | ST.OutputBufferTooSmall ->
    assert False
  | ST.StepOk ->
    assert (ST.server_network_step_ok_received_decode_projection
      st0 st1 buffer_resp input network_out app_out);
    assert (exists msg.
      CT.received_tls_raw_delta_legal
        st0
        msg
        (ST.server_network_consumed_prefix buffer_resp input) /\
      ST.server_decoded_message_event_projection
        st0
        st1
        resp
        msg
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out /\
      (if CS.network_message_is_cleartext CL.Received msg
       then True
       else
         ST.server_protected_record_decode_correct
           st0
           (ST.server_network_consumed_prefix buffer_resp input)
           msg));
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal
            st0
            msg
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.server_decoded_message_event_projection
            st0
            st1
            resp
            msg
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0
               (ST.server_network_consumed_prefix buffer_resp input)
               msg)) in
    assert (ST.server_decoded_message_event_projection
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out);
    if ST.legal_network_response
      st0
      st1
      resp
      msg
      (ST.server_network_consumed_prefix buffer_resp input)
      network_out
      app_out then (
      assert (ST.legal_response_for_event
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out);
      Seq.lemma_eq_elim (ST.server_network_consumed_prefix buffer_resp input) B.empty;
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        B.empty
        network_out
        app_out;
      Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
    ) else (
      assert (ST.unexpected_message_response st0 st1 resp network_out app_out);
      assert (resp.ST.status == ST.IllegalTransition);
      assert False
    )
  | ST.ConnectionFailed ->
    assert (ST.server_network_connection_failed_consumed_prefix
      st0 st1 buffer_resp input network_out app_out);
    let alert =
      ID.indefinite_description_ghost
        T.alert_description
        (fun alert -> exists raw_received.
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    let raw_received =
      ID.indefinite_description_ghost
        B.bytes
        (fun raw_received ->
          st1 ==
            CM.received_alert_failure_state
              st0
              alert
              raw_received /\
          Seq.equal
            raw_received
            (ST.server_network_consumed_prefix buffer_resp input) /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (Seq.equal raw_received (ST.server_network_consumed_prefix buffer_resp input));
    Seq.lemma_eq_elim raw_received (ST.server_network_consumed_prefix buffer_resp input);
    Seq.lemma_eq_elim (ST.server_network_consumed_prefix buffer_resp input) B.empty;
    assert (ST.legal_network_response
      st0
      st1
      resp
      (M.TlsAlert alert)
      B.empty
      network_out
      app_out);
    assert (ST.legal_response_for_event
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      B.empty
      network_out
      app_out);
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (ST.received_message_event (M.TlsAlert alert))
      B.empty
      B.empty
      network_out
      app_out;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received

let lemma_server_network_logged_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (old_consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match_witness
          st0
          received
          sent
          old_consumed
          buffered
          buffered_len /\
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out)
      (ensures
        ST.server_connection_control_not_failed st1 ==>
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            (B.append old_consumed
              (ST.server_network_consumed_prefix buffer_resp input)))
=
  if ST.server_connection_control_not_failed st1 then (
    ST.lemma_server_network_bytes_end_to_end_nonfailed_previous
      st0
      st1
      buffer_resp
      input
      network_out
      app_out;
    assert (ST.server_connection_control_not_failed st0);
    assert (Seq.equal st0.CS.cs_wire_log.CL.raw_received old_consumed);
    ST.lemma_server_network_bytes_end_to_end_nonfailed_received_prefix_accepted
      st0
      st1
      buffer_resp
      input
      network_out
      app_out;
    if buffer_resp.ST.consumed_len == 0sz then (
      lemma_server_network_zero_consumed_raw_received_unchanged
        st0
        st1
        buffer_resp
        input
        network_out
        app_out;
      assert (Seq.equal
        st1.CS.cs_wire_log.CL.raw_received
        st0.CS.cs_wire_log.CL.raw_received);
      Seq.lemma_eq_elim st0.CS.cs_wire_log.CL.raw_received old_consumed;
      assert (ST.server_network_consumed_prefix buffer_resp input ==
        Seq.slice input 0 0);
      Seq.lemma_len_slice input 0 0;
      Seq.lemma_eq_intro (ST.server_network_consumed_prefix buffer_resp input) B.empty;
      Seq.lemma_eq_elim (ST.server_network_consumed_prefix buffer_resp input) B.empty;
      Seq.append_empty_r old_consumed
    ) else (
      assert (exists msg.
        ST.legal_network_response
          st0
          st1
          buffer_resp.ST.response
          msg
          (ST.server_network_consumed_prefix buffer_resp input)
          network_out
          app_out);
      let msg =
        ID.indefinite_description_ghost
          M.tls_message
          (fun msg ->
            ST.legal_network_response
              st0
              st1
              buffer_resp.ST.response
              msg
              (ST.server_network_consumed_prefix buffer_resp input)
              network_out
              app_out) in
      assert (ST.legal_response_for_event
        st0
        st1
        buffer_resp.ST.response
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out);
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        buffer_resp.ST.response
        (ST.received_message_event msg)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      Seq.lemma_eq_elim st0.CS.cs_wire_log.CL.raw_received old_consumed
    )
  )

#push-options "--split_queries always --using_facts_from '* -TLS13.Impl.Server.Driver.NetworkOrdered'"

fn process_buffered_network_bytes_compact_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 sent' app_out_bytes.
          server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
            app_out_bytes **
          pure (server_driver_network_process_correct
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent' /\
            server_driver_network_process_correct_for_app_out
             'st0
             st1
             resp
             (Ghost.reveal 'sent)
             sent'
             app_out_bytes)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));
  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  let current_len = Box.(!d.server_driver_buffered_len);
  assert (pure (current_len == buffered_len));

  V.to_array_pts_to d.server_driver_raw;
  V.to_array_pts_to d.server_driver_network_out;
  V.to_array_pts_to d.server_driver_app_out;
  A.pts_to_len (V.vec_to_array d.server_driver_raw);
  assert (pure (A.length (V.vec_to_array d.server_driver_raw) ==
    SZ.v driver_rx_capacity));
  A.to_mask (V.vec_to_array d.server_driver_raw);
  with raw_mask.
    assert (A.pts_to_mask
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      raw_mask
      (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v driver_rx_capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index raw i)));
  let raw_prefix_array =
    A.sub
      (V.vec_to_array d.server_driver_raw)
      #1.0R
      #(fun _ -> True)
      0sz
      (SZ.v current_len);
  with raw_prefix_mask.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask (fun _ -> True));
  assert (pure (SZ.v current_len <= Seq.length raw_mask));
  Seq.lemma_len_slice raw_mask 0 (SZ.v current_len);
  assert (pure (Seq.length raw_prefix_mask == SZ.v current_len));
  NO.lemma_slice_mask_matches_bytes
    raw_mask
    raw
    (SZ.v current_len);
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Seq.index raw_prefix_mask i == Some (Seq.index raw i)));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask ==>
    Some? (Seq.index raw_prefix_mask i)));
  A.from_mask raw_prefix_array;
  with raw_prefix.
    assert (pts_to raw_prefix_array raw_prefix);
  assert (pure (B.length raw_prefix == SZ.v current_len));
  assert (pure (SZ.v current_len == SZ.v buffered_len));
  assert (pure (forall (i:nat). i < B.length raw_prefix ==>
    Seq.index raw_prefix i == Seq.index raw i));
  assert (pure (SZ.v current_len <= B.length raw));
  NO.lemma_equal_prefix_of_indexes
    raw_prefix
    raw
    (SZ.v current_len);
  assert (pure (Seq.equal raw_prefix
    (Seq.slice raw 0 (SZ.v current_len))));
  Seq.lemma_eq_elim raw_prefix (Seq.slice raw 0 (SZ.v current_len));
  Seq.lemma_eq_elim buffered (Seq.slice raw 0 (SZ.v buffered_len));
  assert (pure (Seq.slice raw 0 (SZ.v current_len) == Seq.slice raw 0 (SZ.v buffered_len)));
  assert (pure (Seq.equal buffered (Seq.slice raw 0 (SZ.v current_len))));
  assert (pure (Seq.equal raw_prefix buffered));

  let buffer_resp =
    S.process_network_bytes
      d.server_driver_server
      raw_prefix_array
      current_len
      (V.vec_to_array d.server_driver_network_out)
      driver_network_out_capacity
      (V.vec_to_array d.server_driver_app_out)
      driver_app_out_capacity;
  with st1 network_out_bytes app_out_bytes.
    assert (S.connection_exactly d.server_driver_server st1 **
            pts_to raw_prefix_array raw_prefix **
            pts_to (V.vec_to_array d.server_driver_network_out) network_out_bytes **
            pts_to (V.vec_to_array d.server_driver_app_out) app_out_bytes);
  assert (pure (B.length network_out_bytes == SZ.v driver_network_out_capacity));
  assert (pure (B.length app_out_bytes == SZ.v driver_app_out_capacity));
  assert (pure (ST.server_network_bytes_end_to_end_correct
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes));
  assert (pure (ST.server_network_consumed_input_projection
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= B.length raw_prefix));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= SZ.v current_len));
  assert (pure (SZ.v buffer_resp.ST.consumed_len <= SZ.v buffered_len));
  assert (pure (CPI.buffers_wf
    raw_prefix
    current_len
    network_out
    driver_network_out_capacity));
  SP.lemma_server_network_event_progress
    (Ghost.reveal d.server_driver_initial)
    'st0
    st1
    buffer_resp
    raw_prefix
    current_len
    network_out
    network_out_bytes
    driver_network_out_capacity
    app_out_bytes;
  advance_server_driver_canonical_progress
    d 'st0 st1;

  A.to_mask raw_prefix_array;
  with raw_prefix_mask_after.
    assert (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Some? (Seq.index raw_prefix_mask_after i)));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Seq.index raw_prefix_mask_after i == Some (Seq.index raw_prefix i)));
  assert (pure (Seq.length raw_prefix_mask_after == SZ.v current_len));
  assert (pure (SZ.v current_len <= B.length raw));
  NO.lemma_prefix_mask_matches_bytes
    raw_prefix
    raw
    raw_prefix_mask_after
    (SZ.v current_len);
  rewrite
    (A.pts_to_mask raw_prefix_array #1.0R raw_prefix_mask_after (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub (V.vec_to_array d.server_driver_raw) 0 (SZ.v current_len))
      #1.0R
      raw_prefix_mask_after
      (fun _ -> True));
  A.return_sub
    (V.vec_to_array d.server_driver_raw)
    #1.0R
    #raw_mask
    #raw_prefix_mask_after
    #(fun k -> True /\ ~(0 <= k /\ k < SZ.v current_len))
    #(fun _ -> True)
    #0
    #(SZ.v current_len);
  with raw_joined_mask.
    assert (A.pts_to_mask (V.vec_to_array d.server_driver_raw) #1.0R raw_joined_mask
      (fun k ->
        (True /\ ~(0 <= k /\ k < SZ.v current_len)) \/
        (0 <= k /\ k < SZ.v current_len /\ True)));
  assert (pure (Seq.length raw_joined_mask == Seq.length raw_mask));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    ((True /\ ~(0 <= i /\ i < SZ.v current_len)) \/
     (0 <= i /\ i < SZ.v current_len /\ True))));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i ==
      (if 0 <= i && i < SZ.v current_len
       then Seq.index raw_prefix_mask_after (i - 0)
       else Seq.index raw_mask i)));
  assert (pure (B.length raw == SZ.v driver_rx_capacity));
  assert (pure (Seq.length raw_mask == B.length raw));
  assert (pure (Seq.length raw_prefix_mask_after == SZ.v current_len));
  assert (pure (SZ.v current_len <= B.length raw));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index raw i)));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Seq.index raw_prefix_mask_after i == Some (Seq.index raw i)));
  assert (pure (Seq.equal raw_prefix
    (Seq.slice raw 0 (SZ.v current_len))));
  assert (pure (forall (i:nat). i < Seq.length raw_prefix_mask_after ==>
    Seq.index raw_prefix_mask_after i == Some (Seq.index raw_prefix i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Seq.index raw_joined_mask i == Some (Seq.index raw i)));
  assert (pure (forall (i:nat). i < Seq.length raw_joined_mask ==>
    Some? (Seq.index raw_joined_mask i)));
  A.from_mask (V.vec_to_array d.server_driver_raw);
  with raw_bytes.
    assert (pts_to (V.vec_to_array d.server_driver_raw) raw_bytes);
  assert (pure (B.length raw_bytes == SZ.v driver_rx_capacity));
  assert (pure (B.length raw == SZ.v driver_rx_capacity));
  assert (pure (forall (i:nat). i < B.length raw_bytes ==>
    Seq.index raw_bytes i == Seq.index raw i));
  Seq.lemma_eq_intro raw_bytes raw;
  assert (pure (Seq.equal raw_bytes raw));

  let old_consumed =
    choose_server_driver_wire_logs_consumed
      'st0
      (Ghost.reveal 'received)
      (Ghost.reveal 'sent)
      buffered
      buffered_len;
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));
  let consumed_prefix =
    Ghost.hide (ST.server_network_consumed_prefix buffer_resp raw_prefix);
  let new_buffered =
    Ghost.hide (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len));
  Ghost.reveal_hide (Seq.slice buffered
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len));
  assert (pure ((Ghost.reveal new_buffered) ==
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  assert (pure (Seq.equal
    (Ghost.reveal new_buffered)
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  Seq.lemma_eq_elim
    (Ghost.reveal new_buffered)
    (Seq.slice buffered
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len));
  Seq.lemma_len_slice
    buffered
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len);
  assert (pure (B.length (Ghost.reveal new_buffered) ==
    SZ.v buffered_len - SZ.v buffer_resp.ST.consumed_len));
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice raw_prefix 0 (SZ.v buffer_resp.ST.consumed_len))));
  Seq.lemma_eq_elim raw_prefix buffered;
  assert (pure (Seq.equal (Ghost.reveal consumed_prefix)
    (Seq.slice buffered 0 (SZ.v buffer_resp.ST.consumed_len))));
  lemma_slice_append_full
    buffered
    (SZ.v buffer_resp.ST.consumed_len);
  assert (pure (Seq.equal
    (B.append (Ghost.reveal consumed_prefix) (Ghost.reveal new_buffered))
    buffered));
  lemma_server_network_wire_accounting
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal old_consumed);
  assert (pure (SZ.v buffer_resp.ST.response.ST.network_out_len <=
    B.length network_out_bytes));
  Seq.append_assoc
    (Ghost.reveal old_consumed)
    (Ghost.reveal consumed_prefix)
    (Ghost.reveal new_buffered);
  assert (pure (Seq.equal
    (B.append
      (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
      (Ghost.reveal new_buffered))
    (Ghost.reveal 'received)));

  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let written =
    IO.write
      concrete_ch
      (V.vec_to_array d.server_driver_network_out)
      buffer_resp.ST.response.ST.network_out_len;
  assert (pure (written == buffer_resp.ST.response.ST.network_out_len));
  rewrite (IO.is_channel
             concrete_ch
             (Ghost.reveal 'received)
             (B.append
               (Ghost.reveal 'sent)
               (if SZ.v written <= B.length network_out_bytes
                then Seq.slice network_out_bytes 0 (SZ.v written)
                else B.empty))) as
    (IO.is_channel
      ch
      (Ghost.reveal 'received)
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)));
  assert (pure (SZ.v written <= B.length network_out_bytes));
  Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
  assert (pure (Seq.equal
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty)
    (ST.response_network_out buffer_resp.ST.response network_out_bytes)));
  assert (pure (Seq.equal
    st1.CS.cs_wire_log.CL.raw_sent
    (B.append
      'st0.CS.cs_wire_log.CL.raw_sent
      (ST.response_network_out buffer_resp.ST.response network_out_bytes))));
  assert (pure (Seq.equal (Ghost.reveal 'sent) 'st0.CS.cs_wire_log.CL.raw_sent));
  Seq.lemma_eq_elim (Ghost.reveal 'sent) 'st0.CS.cs_wire_log.CL.raw_sent;

  let compact_len =
    BT.compact_buffer_suffix
      (V.vec_to_array d.server_driver_raw)
      driver_rx_capacity
      current_len
      buffer_resp.ST.consumed_len;
  with compacted_raw.
    assert (pts_to (V.vec_to_array d.server_driver_raw) compacted_raw);
  assert (pure (SZ.v compact_len ==
    SZ.v buffered_len - SZ.v buffer_resp.ST.consumed_len));
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v compact_len));
  assert (pure (B.length compacted_raw == SZ.v driver_rx_capacity));
  assert (pure (Seq.equal
    (Seq.slice compacted_raw 0 (SZ.v compact_len))
    (Seq.slice raw_bytes
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  NO.lemma_equal_slice_of_prefix
    buffered
    raw
    (SZ.v buffer_resp.ST.consumed_len)
    (SZ.v buffered_len);
  assert (pure (Seq.equal
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))
    (Seq.slice raw
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))));
  Seq.lemma_eq_elim
    (Seq.slice buffered
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len))
    (Seq.slice raw
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len));
  Seq.lemma_eq_elim raw_bytes raw;
  Seq.lemma_eq_elim
    (Seq.slice compacted_raw 0 (SZ.v compact_len))
    (Seq.slice raw_bytes
      (SZ.v buffer_resp.ST.consumed_len)
      (SZ.v buffered_len));
  assert (pure (Seq.equal
    (Ghost.reveal new_buffered)
    (Seq.slice compacted_raw 0 (SZ.v compact_len))));

  Box.(d.server_driver_buffered_len := compact_len);
  V.to_vec_pts_to d.server_driver_raw;
  V.to_vec_pts_to d.server_driver_network_out;
  V.to_vec_pts_to d.server_driver_app_out;
  fold (server_driver_buffers_with_app_out
    d
    (Ghost.reveal new_buffered)
    compact_len
    app_out_bytes);
  assert (pure (logged_received_bytes_accounted
    st1.CS.cs_wire_log.CL.raw_received
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))));
  lemma_server_network_logged_received_exact_when_nonfailed
    'st0
    st1
    buffer_resp
    buffered
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len;
  assert (pure (ST.server_connection_control_not_failed st1 ==>
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append (Ghost.reveal old_consumed)
        (ST.server_network_consumed_prefix buffer_resp buffered))));
  Seq.lemma_eq_elim
    (Ghost.reveal consumed_prefix)
    (ST.server_network_consumed_prefix buffer_resp buffered);
  assert (pure (Seq.equal
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    st1.CS.cs_wire_log.CL.raw_sent));
  assert (pure (
    B.length (Ghost.reveal new_buffered) == SZ.v compact_len));
  assert (pure (Seq.equal
    (B.append
      (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
      (Ghost.reveal new_buffered))
    (Ghost.reveal 'received)));
  assert (pure (logged_received_bytes_accounted
    st1.CS.cs_wire_log.CL.raw_received
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))));
  assert (pure (ST.server_connection_control_not_failed st1 ==>
    Seq.equal
      st1.CS.cs_wire_log.CL.raw_received
      (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))));
  Seq.lemma_eq_elim
    (B.append
      (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
      (Ghost.reveal new_buffered))
    (Ghost.reveal 'received);
  assert (pure (server_driver_wire_logs_match_witness
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix))
    (Ghost.reveal new_buffered)
    compact_len));
  FStar.Classical.exists_intro
    (fun consumed ->
      server_driver_wire_logs_match_witness
        st1
        (Ghost.reveal 'received)
        (B.append
          (Ghost.reveal 'sent)
          (if SZ.v written <= B.length network_out_bytes
           then Seq.slice network_out_bytes 0 (SZ.v written)
           else B.empty))
        consumed
        (Ghost.reveal new_buffered)
        compact_len)
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal consumed_prefix));
  assert (pure (server_driver_wire_logs_match
    st1
    (Ghost.reveal 'received)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal new_buffered)
    compact_len));
  lemma_server_driver_network_process_correct_intro
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  lemma_server_driver_network_process_correct_preserves_config
    'st0
    st1
    buffer_resp
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  assert (pure (server_driver_config_matches_credentials
    st1
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  lemma_server_driver_network_process_correct_preserves_supported_profile_selection
    'st0
    st1
    buffer_resp
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    (Ghost.reveal 'credential_identity);
  assert (pure (server_driver_supported_profile_selection
    st1
    (Ghost.reveal 'credential_identity)));
  CPI.lemma_bytes_extends_refl (Ghost.reveal 'received);
  CPI.lemma_bytes_extends_append
    (Ghost.reveal 'sent)
    (if SZ.v written <= B.length network_out_bytes
     then Seq.slice network_out_bytes 0 (SZ.v written)
     else B.empty);
  advance_server_driver_io_history
    d
    'received
    'sent
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  fold (server_driver_connected_with_app_out
    d
    st1
    'certificate_chain
    'credential_identity
    'received
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty))
    app_out_bytes);
  lemma_server_driver_network_process_correct_intro
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  lemma_server_driver_network_process_correct_for_app_out_intro
    'st0
    st1
    buffer_resp
    raw_prefix
    network_out_bytes
    app_out_bytes
    (Ghost.reveal 'sent)
    (B.append
      (Ghost.reveal 'sent)
      (if SZ.v written <= B.length network_out_bytes
       then Seq.slice network_out_bytes 0 (SZ.v written)
       else B.empty));
  FStar.Classical.exists_intro
    (fun app_out_bytes' ->
      server_driver_network_process_correct_for_app_out
        'st0
        st1
        buffer_resp
        (Ghost.reveal 'sent)
        (B.append
          (Ghost.reveal 'sent)
          (if SZ.v written <= B.length network_out_bytes
           then Seq.slice network_out_bytes 0 (SZ.v written)
           else B.empty))
        app_out_bytes')
    app_out_bytes;
  assert (pure (
    server_driver_network_process_correct
      'st0
      st1
      buffer_resp
      (Ghost.reveal 'sent)
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty)) /\
    server_driver_network_process_correct_for_app_out
      'st0
      st1
      buffer_resp
      (Ghost.reveal 'sent)
      (B.append
        (Ghost.reveal 'sent)
        (if SZ.v written <= B.length network_out_bytes
         then Seq.slice network_out_bytes 0 (SZ.v written)
         else B.empty))
      app_out_bytes));
  buffer_resp
}

#pop-options

inline_for_extraction
private fn read_and_process_network_once
  (d:server_driver)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 received' sent' app_out_bytes.
          server_driver_connected_with_app_out
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out_bytes **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent' /\
           server_driver_network_process_correct_for_app_out
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent'
            app_out_bytes)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  assert (pure (ST.server_end_to_end_invariant 'st0));
  assert (pure (server_driver_wire_logs_match
    'st0
    'received
    'sent
    buffered
    buffered_len));
  unfold (server_driver_buffers d buffered buffered_len);
  with empty_payload raw network_out material cv_input signature app_out.
    assert (
      Box.pts_to d.server_driver_buffered_len buffered_len **
      V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
      V.pts_to d.server_driver_raw #1.0R raw **
      V.pts_to d.server_driver_network_out #1.0R network_out **
      V.pts_to d.server_driver_material_payload #1.0R material **
      V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
      V.pts_to d.server_driver_signature #1.0R signature **
      V.pts_to d.server_driver_app_out #1.0R app_out);
  let current_len = Box.(!d.server_driver_buffered_len);
  assert (pure (current_len == buffered_len));
  assert (pure (SZ.v current_len <= SZ.v driver_rx_capacity));

  if (current_len = driver_rx_capacity) {
    fold (server_driver_buffers d buffered buffered_len);
    fold (server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent);
    process_buffered_network_bytes_compact_once d
  } else {
  assert (pure (SZ.v current_len < SZ.v driver_rx_capacity));
  let old_consumed =
    choose_server_driver_wire_logs_consumed
      'st0
      (Ghost.reveal 'received)
      (Ghost.reveal 'sent)
      buffered
      buffered_len;
  assert (pure (server_driver_wire_logs_match_witness
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    buffered
    buffered_len));

  V.to_array_pts_to d.server_driver_raw;
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  let read_result =
    BT.read_append
      concrete_ch
      (V.vec_to_array d.server_driver_raw)
      driver_rx_capacity
      current_len;
  with raw_after_read read_chunk.
    assert (IO.is_channel
              concrete_ch
              (B.append (Ghost.reveal 'received) read_chunk)
              (Ghost.reveal 'sent) **
            pts_to (V.vec_to_array d.server_driver_raw) raw_after_read);
  let read_len = read_result.BT.ra_read;
  let total_len = read_result.BT.ra_total;
  rewrite (IO.is_channel
              concrete_ch
              (B.append (Ghost.reveal 'received) read_chunk)
              (Ghost.reveal 'sent)) as
    (IO.is_channel
      ch
      (B.append (Ghost.reveal 'received) read_chunk)
      (Ghost.reveal 'sent));
  assert (pure (B.length read_chunk == SZ.v read_len));
  assert (pure (SZ.v read_len <=
    SZ.v driver_rx_capacity - SZ.v current_len));
  assert (pure (SZ.v current_len + SZ.v read_len <= SZ.v driver_rx_capacity));
  assert (pure (SZ.v total_len == SZ.v current_len + SZ.v read_len));
  assert (pure (SZ.v total_len <= SZ.v driver_rx_capacity));
  assert (pure (SZ.v total_len == SZ.v buffered_len + SZ.v read_len));

  let new_buffered =
    Ghost.hide (B.append buffered read_chunk);
  Seq.lemma_len_append buffered read_chunk;
  assert (pure (B.length (Ghost.reveal new_buffered) == SZ.v total_len));
  Seq.append_assoc (Ghost.reveal old_consumed) buffered read_chunk;
  assert (pure (Seq.equal
    (B.append
      (B.append (Ghost.reveal old_consumed) buffered)
      read_chunk)
    (B.append (Ghost.reveal 'received) read_chunk)));
  assert (pure (Seq.equal
    (B.append (Ghost.reveal old_consumed) (Ghost.reveal new_buffered))
    (B.append (Ghost.reveal 'received) read_chunk)));
  assert_spinoff (server_driver_wire_logs_match_witness
    'st0
    (B.append (Ghost.reveal 'received) read_chunk)
    (Ghost.reveal 'sent)
    (Ghost.reveal old_consumed)
    (Ghost.reveal new_buffered)
    total_len);
  assert (pure (server_driver_wire_logs_match
    'st0
    (B.append (Ghost.reveal 'received) read_chunk)
    (Ghost.reveal 'sent)
    (Ghost.reveal new_buffered)
    total_len));

  assert (pure (B.length raw_after_read == SZ.v driver_rx_capacity));
  assert (pure (Seq.equal buffered (Seq.slice raw 0 (SZ.v current_len))));
  assert (pure (Seq.equal
    (Seq.slice raw_after_read 0 (SZ.v total_len))
    (B.append (Seq.slice raw 0 (SZ.v current_len)) read_chunk)));
  Seq.lemma_eq_elim buffered (Seq.slice raw 0 (SZ.v current_len));
  assert (pure (Seq.equal
    (B.append buffered read_chunk)
    (Seq.slice raw_after_read 0 (SZ.v total_len))));
  assert (pure (Seq.equal (Ghost.reveal new_buffered)
    (Seq.slice raw_after_read 0 (SZ.v total_len))));

  Box.(d.server_driver_buffered_len := total_len);
  V.to_vec_pts_to d.server_driver_raw;
  fold (server_driver_buffers d (Ghost.reveal new_buffered) total_len);
  CPI.lemma_bytes_extends_append (Ghost.reveal 'received) read_chunk;
  CPI.lemma_bytes_extends_refl (Ghost.reveal 'sent);
  advance_server_driver_io_history
    d
    'received
    'sent
    (B.append (Ghost.reveal 'received) read_chunk)
    'sent;
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    (B.append (Ghost.reveal 'received) read_chunk)
    'sent);
  let resp = process_buffered_network_bytes_compact_once d;
  resp
  }
}

fn process_buffered_or_read_network_once
  (d:server_driver)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 received' sent' app_out_bytes.
          server_driver_connected_with_app_out
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out_bytes **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent' /\
           server_driver_network_process_correct_for_app_out
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent'
            app_out_bytes)
{
  let buffered_step = process_buffered_network_bytes_compact_once d;
  with st1 sent' buffered_app_out.
    assert (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent'
      buffered_app_out **
    pure (server_driver_network_process_correct
      'st0
      st1
      buffered_step
      (Ghost.reveal 'sent)
      sent' /\
    server_driver_network_process_correct_for_app_out
      'st0
      st1
      buffered_step
      (Ghost.reveal 'sent)
      sent'
      buffered_app_out));
  let need_more =
    buffered_step.ST.response.ST.status = ST.NeedMoreInput;
  if need_more {
    lemma_server_driver_network_process_need_more_stutter
      'st0
      st1
      buffered_step
      (Ghost.reveal 'sent)
      sent';
    assert (pure (st1 == 'st0));
    assert (pure (Seq.equal sent' (Ghost.reveal 'sent)));
    Seq.lemma_eq_elim sent' (Ghost.reveal 'sent);
    rewrite (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent'
      buffered_app_out) as
      (server_driver_connected_with_app_out
        d
        st1
        'certificate_chain
        'credential_identity
        'received
        (Ghost.reveal 'sent)
        buffered_app_out);
    assert (pure (
      server_buffer_read_decision buffered_step == BS.NeedMore));
    unfold (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      (Ghost.reveal 'sent)
      buffered_app_out);
    with ch buffered buffered_len.
      assert (
        Box.pts_to d.server_driver_channel (Some ch) **
        IO.is_channel ch 'received 'sent **
        server_driver_buffers_with_app_out
          d buffered buffered_len buffered_app_out);
    unfold (server_driver_buffers_with_app_out
      d buffered buffered_len buffered_app_out);
    with empty_payload raw network_out material cv_input signature local_app_out.
      assert (
        Box.pts_to d.server_driver_buffered_len buffered_len **
        V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
        V.pts_to d.server_driver_raw #1.0R raw **
        V.pts_to d.server_driver_network_out #1.0R network_out **
        V.pts_to d.server_driver_material_payload #1.0R material **
        V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
        V.pts_to d.server_driver_signature #1.0R signature **
        V.pts_to d.server_driver_app_out #1.0R buffered_app_out **
        V.pts_to d.server_driver_local_app_out #1.0R local_app_out);
    let current_len = Box.(!d.server_driver_buffered_len);
    fold (server_driver_buffers_with_app_out
      d buffered buffered_len buffered_app_out);
    fold (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      (Ghost.reveal 'sent)
      buffered_app_out);
    if (current_len = driver_rx_capacity) {
      buffered_step
    } else {
      forget_server_driver_connected_app_out d;
      let read_step =
        read_and_process_network_once d;
      read_step
    }
  } else {
    buffered_step
  }
}

fn server_driver_control_snapshot
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns snapshot:CR.control_snapshot
  ensures server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
          pure (CR.control_snapshot_matches snapshot 'st0)
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  rewrite (S.connection_exactly d.server_driver_server 'st0)
    as (CR.connection_exactly d.server_driver_server 'st0);
  let snapshot = CQ.get_control_snapshot d.server_driver_server;
  rewrite (CR.connection_exactly d.server_driver_server 'st0)
    as (S.connection_exactly d.server_driver_server 'st0);
  fold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  snapshot
}

fn rec read_process_network_until_ready
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_network_loop_result
  ensures exists* st1 received' sent' app_out_bytes.
          server_driver_connected_with_app_out
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out_bytes **
          pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config /\
            (result.server_driver_network_loop_exhausted == true ==>
              st1 == 'st0 /\
              Seq.equal sent' (Ghost.reveal 'sent)) /\
            (result.server_driver_network_loop_exhausted == false ==>
            result.server_driver_network_loop_last.ST.response.ST.status <>
              ST.NeedMoreInput /\
            server_driver_network_process_correct
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent' /\
            server_driver_network_process_correct_for_app_out
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent'
              app_out_bytes))
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    ST.response = no_op_resp;
    ST.consumed_len = 0sz;
  };
  if (fuel = 0sz) {
    expose_server_driver_connected_app_out d;
    assert (pure ('st0.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config));
    {
      server_driver_network_loop_last = no_op_buffer_resp;
      server_driver_network_loop_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step = process_buffered_or_read_network_once d;
    with st1 received' sent' step_app_out.
      assert (server_driver_connected_with_app_out
        d
        st1
        'certificate_chain
        'credential_identity
        received'
        sent'
        step_app_out **
      pure (server_driver_network_process_correct
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent' /\
        server_driver_network_process_correct_for_app_out
          'st0
          st1
          step
          (Ghost.reveal 'sent)
          sent'
          step_app_out));
    let need_more = step.ST.response.ST.status = ST.NeedMoreInput;
    if need_more {
      lemma_server_driver_network_process_need_more_stutter
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent';
      assert (pure (st1 == 'st0));
      assert (pure (Seq.equal sent' (Ghost.reveal 'sent)));
      Seq.lemma_eq_elim sent' (Ghost.reveal 'sent);
      let next_fuel = SZ.sub fuel 1sz;
      assert (pure (SZ.v next_fuel < SZ.v fuel));
      forget_server_driver_connected_app_out d;
      let result = read_process_network_until_ready d next_fuel;
      with st2 received2 sent2 result_app_out.
        assert (server_driver_connected_with_app_out
          d
          st2
          'certificate_chain
          'credential_identity
          received2
          sent2
          result_app_out **
        pure (st2.CS.cs_model.CS.model_config ==
          st1.CS.cs_model.CS.model_config /\
        (result.server_driver_network_loop_exhausted == true ==>
          st2 == st1 /\
          Seq.equal sent2 sent') /\
        (result.server_driver_network_loop_exhausted == false ==>
          result.server_driver_network_loop_last.ST.response.ST.status <>
            ST.NeedMoreInput /\
          server_driver_network_process_correct
            st1
            st2
              result.server_driver_network_loop_last
              sent'
              sent2 /\
              server_driver_network_process_correct_for_app_out
                st1
                st2
                result.server_driver_network_loop_last
                sent'
                sent2
                result_app_out)));
      assert (pure (st2.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (result.server_driver_network_loop_exhausted == true ==>
        st2 == 'st0 /\
        Seq.equal sent2 (Ghost.reveal 'sent)));
      assert (pure (result.server_driver_network_loop_exhausted == false ==>
        server_driver_network_process_correct
            'st0
            st2
            result.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent2 /\
        server_driver_network_process_correct_for_app_out
            'st0
            st2
            result.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent2
            result_app_out));
      result
    } else {
      assert (pure (step.ST.response.ST.status <> ST.NeedMoreInput));
      assert (pure (server_driver_network_process_correct
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent'));
      lemma_server_driver_network_process_correct_preserves_config
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent';
      assert (pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
      assert (pure (server_driver_network_process_correct_for_app_out
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent'
        step_app_out));
      {
        server_driver_network_loop_last = step;
        server_driver_network_loop_exhausted = false;
      }
    }

  }
}

fn rec read_until_client_hello_received
  (d:server_driver)
  (fuel:SZ.t)
  requires server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_client_hello_wait_result
  ensures exists* st1 received' sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pure (st1.CS.cs_model.CS.model_config ==
             'st0.CS.cs_model.CS.model_config /\
           (result.server_driver_client_hello_wait_ready == true ==>
            st1.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config))
  decreases (SZ.v fuel)
{
  let no_op_resp = {
    ST.network_out_len = 0sz;
    ST.app_out_len = 0sz;
    ST.status = ST.NeedMoreInput;
  };
  let no_op_buffer_resp = {
    ST.response = no_op_resp;
    ST.consumed_len = 0sz;
  };
  let snapshot = server_driver_control_snapshot d;
  assert (pure (CR.control_snapshot_matches snapshot 'st0));
  let client_hello_received =
    (snapshot.CR.snapshot_control_tag = 1uy) &&
    (snapshot.CR.snapshot_handshake_stage_tag = 13uy);
  if client_hello_received {
    assert (pure (snapshot.CR.snapshot_control_tag == 1uy));
    assert (pure (snapshot.CR.snapshot_handshake_stage_tag == 13uy));
    assert_norm (Tags.handshake_stage_tag_matches 13uy CS.HsClientHelloReceived);
    lemma_control_snapshot_client_hello_received snapshot 'st0;
    assert (pure (
      'st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientHelloReceived));
    assert (pure (
      'st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
    {
      server_driver_client_hello_wait_last = no_op_buffer_resp;
      server_driver_client_hello_wait_ready = true;
      server_driver_client_hello_wait_exhausted = false;
    }
  } else if (fuel = 0sz) {
    assert (pure (
      'st0.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config));
    {
      server_driver_client_hello_wait_last = no_op_buffer_resp;
      server_driver_client_hello_wait_ready = false;
      server_driver_client_hello_wait_exhausted = true;
    }
  } else {
    assert (pure (0 < SZ.v fuel));
    let step = process_buffered_or_read_network_once d;
    with st1 received' sent' step_app_out.
      assert (server_driver_connected_with_app_out
        d
        st1
        'certificate_chain
        'credential_identity
        received'
        sent'
        step_app_out **
      pure (server_driver_network_process_correct
        'st0
        st1
        step
        (Ghost.reveal 'sent)
        sent'));
    lemma_server_driver_network_process_correct_preserves_config
      'st0
      st1
      step
      (Ghost.reveal 'sent)
      sent';
    forget_server_driver_connected_app_out d;
    let snapshot_after = server_driver_control_snapshot d;
    assert (pure (CR.control_snapshot_matches snapshot_after st1));
    let client_hello_received_after =
      (snapshot_after.CR.snapshot_control_tag = 1uy) &&
      (snapshot_after.CR.snapshot_handshake_stage_tag = 13uy);
    if client_hello_received_after {
      assert (pure (snapshot_after.CR.snapshot_control_tag == 1uy));
      assert (pure (snapshot_after.CR.snapshot_handshake_stage_tag == 13uy));
      assert_norm (Tags.handshake_stage_tag_matches 13uy CS.HsClientHelloReceived);
      lemma_control_snapshot_client_hello_received snapshot_after st1;
      assert (pure (
        st1.CS.cs_model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived));
      assert (pure (
        st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      {
        server_driver_client_hello_wait_last = step;
        server_driver_client_hello_wait_ready = true;
        server_driver_client_hello_wait_exhausted = false;
      }
    } else {
      let need_more = step.ST.response.ST.status = ST.NeedMoreInput;
      if need_more {
        let next_fuel = SZ.sub fuel 1sz;
        assert (pure (SZ.v next_fuel < SZ.v fuel));
        let result = read_until_client_hello_received d next_fuel;
        with st2 received2 sent2.
          assert (server_driver_connected
            d
            st2
            'certificate_chain
            'credential_identity
            received2
            sent2 **
          pure (st2.CS.cs_model.CS.model_config ==
            st1.CS.cs_model.CS.model_config /\
          (result.server_driver_client_hello_wait_ready == true ==>
            st2.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st2.CS.cs_model.CS.model_config ==
              st1.CS.cs_model.CS.model_config)));
        assert (pure (st2.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
        assert (pure (result.server_driver_client_hello_wait_ready == true ==>
          st2.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        result
      } else {
        assert (pure (
          st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
        {
          server_driver_client_hello_wait_last = step;
          server_driver_client_hello_wait_ready = false;
          server_driver_client_hello_wait_exhausted = false;
        }
      }

    }
  }
}

#pop-options

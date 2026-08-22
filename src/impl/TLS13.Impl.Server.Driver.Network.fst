module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

#push-options "--using_facts_from '*'"

open TLS13.Impl.Server.Driver.State


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

#push-options "--z3rlimit 100"
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

#pop-options
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
         (* G3: a cleartext handshake BUFFERING step touches only the pending
            reassembly buffer, so it leaves the config and the server's
            credential selection exactly as they were. *)
         | CS.ConnCleartextHandshake _ -> True
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
  | CS.ConnCleartextHandshake _ ->
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
    (* G3: a StepOk either delivered a message or buffered a cleartext
       handshake fragment; only the first reading supports the message
       witness below, and the second preserves the selection outright. *)
    if (exists step.
          ST.cleartext_handshake_step_correct
            st0
            st1
            resp.ST.response
            step
            (ST.server_network_consumed_prefix resp input)
            network_out_bytes
            app_out_bytes)
    then (
      let step =
        ID.indefinite_description_ghost
          CS.cleartext_handshake_step
          (fun step ->
            ST.cleartext_handshake_step_correct
              st0
              st1
              resp.ST.response
              step
              (ST.server_network_consumed_prefix resp input)
              network_out_bytes
              app_out_bytes) in
      lemma_legal_response_for_event_preserves_supported_profile_selection
        st0
        st1
        resp.ST.response
        (CS.ConnCleartextHandshake step)
        B.empty
        (ST.server_network_consumed_prefix resp input)
        network_out_bytes
        app_out_bytes
        credential_identity
    ) else (
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal_unbuffered
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
    ))

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
    (* G3: a buffering StepOk consumes the record and writes nothing, so the
       wire accounting is the same as a delivering one -- only the event that
       justifies it differs. *)
    if (exists step.
          ST.cleartext_handshake_step_correct
            st0
            st1
            resp
            step
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out)
    then (
      let step =
        ID.indefinite_description_ghost
          CS.cleartext_handshake_step
          (fun step ->
            ST.cleartext_handshake_step_correct
              st0
              st1
              resp
              step
              (ST.server_network_consumed_prefix buffer_resp input)
              network_out
              app_out) in
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (CS.ConnCleartextHandshake step)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      lemma_legal_response_network_out_len
        st0
        st1
        resp
        (CS.ConnCleartextHandshake step)
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
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal_unbuffered
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
    ))
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
    (* G3: the buffering reading of a StepOk.  It cannot actually occur with a
       zero consumed length -- a buffering step consumes exactly one record --
       but the projection alone does not say so, and the conclusion holds for
       it regardless: the delta's received bytes are the (empty) consumed
       prefix. *)
    if (exists step.
          ST.cleartext_handshake_step_correct
            st0
            st1
            resp
            step
            (ST.server_network_consumed_prefix buffer_resp input)
            network_out
            app_out)
    then (
      let step =
        ID.indefinite_description_ghost
          CS.cleartext_handshake_step
          (fun step ->
            ST.cleartext_handshake_step_correct
              st0
              st1
              resp
              step
              (ST.server_network_consumed_prefix buffer_resp input)
              network_out
              app_out) in
      Seq.lemma_eq_elim (ST.server_network_consumed_prefix buffer_resp input) B.empty;
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (CS.ConnCleartextHandshake step)
        B.empty
        B.empty
        network_out
        app_out;
      Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received
    ) else (
    assert (exists msg.
      CT.received_tls_raw_delta_legal_unbuffered
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
          CT.received_tls_raw_delta_legal_unbuffered
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
    ))
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
    ) else if (exists step.
                 ST.cleartext_handshake_step_correct
                   st0
                   st1
                   buffer_resp.ST.response
                   step
                   (ST.server_network_consumed_prefix buffer_resp input)
                   network_out
                   app_out)
    then (
      (* G3: the buffering reading of an accepted prefix.  It carries the same
         [legal_response_for_event] as a delivering step, so the wire-length
         accounting below is word-for-word the message case's. *)
      let step =
        ID.indefinite_description_ghost
          CS.cleartext_handshake_step
          (fun step ->
            ST.cleartext_handshake_step_correct
              st0
              st1
              buffer_resp.ST.response
              step
              (ST.server_network_consumed_prefix buffer_resp input)
              network_out
              app_out) in
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        buffer_resp.ST.response
        (CS.ConnCleartextHandshake step)
        B.empty
        (ST.server_network_consumed_prefix buffer_resp input)
        network_out
        app_out;
      Seq.lemma_eq_elim st0.CS.cs_wire_log.CL.raw_received old_consumed
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

#pop-options

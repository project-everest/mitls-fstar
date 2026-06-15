module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types
module U8 = FStar.UInt8

open TLS13.Impl.Server.Driver.State

let pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == pending_after_consumed buffered_len consumed_len));
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'raw_bytes) 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes)
        (SZ.v consumed_len)
        (SZ.v buffered_len))));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity /\
              (forall (k:nat). k < SZ.v (R.read i) ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)) /\
              (forall (k:nat). SZ.v (R.read i) <= k /\ k < SZ.v buffered_len ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) k))
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (b == Seq.index (Ghost.reveal 'raw_bytes)
        (SZ.v vi + SZ.v consumed_len)));
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (forall (k:nat). k < SZ.v vi + 1 ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) k));
      assert (pure (SZ.v vi + 1 <= SZ.v new_len));
      SZ.fits_lte (SZ.v vi + 1) (SZ.v new_len);
      let next_i = vi `SZ.add` 1sz;
      R.write i next_i;
    };
    with raw_done.
      assert (pts_to raw raw_done);
    assert (pure (B.length raw_done == SZ.v raw_capacity));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index raw_done k ==
      Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
    Seq.lemma_len_slice raw_done 0 (SZ.v new_len);
    Seq.lemma_len_slice (Ghost.reveal 'raw_bytes)
      (SZ.v consumed_len)
      (SZ.v buffered_len);
    assert (pure (forall (k:nat). k < B.length (Seq.slice raw_done 0 (SZ.v new_len)) ==>
      Seq.index (Seq.slice raw_done 0 (SZ.v new_len)) k ==
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k));
    Seq.lemma_eq_intro
      (Seq.slice raw_done 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len));
    new_len
  }
}

noextract
let server_driver_network_process_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists input network_out_bytes app_out_bytes.
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
      (ST.response_network_out resp.ST.response network_out_bytes))

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

module TLS13.Impl.Server.Driver.NetworkOrdered

#set-options "--split_queries always"

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

open TLS13.Impl.Server.Driver.State

let lemma_slice_mask_matches_bytes
  (mask:Seq.seq (option FStar.UInt8.t))
  (bytes:B.bytes)
  (hi:nat{hi <= Seq.length mask})
  : Lemma
      (requires
        Seq.length mask == B.length bytes /\
        (forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index bytes i)))
      (ensures
        forall (i:nat). i < Seq.length (Seq.slice mask 0 hi) ==>
          Seq.index (Seq.slice mask 0 hi) i ==
            Some (Seq.index bytes i))
=
  Seq.lemma_len_slice mask 0 hi;
  let index_proof
    (i:nat{i < Seq.length (Seq.slice mask 0 hi)})
    : Lemma
        (Seq.index (Seq.slice mask 0 hi) i ==
          Some (Seq.index bytes i))
  =
    Seq.lemma_index_slice mask 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length (Seq.slice mask 0 hi)})
    #(fun i ->
      Seq.index (Seq.slice mask 0 hi) i ==
        Some (Seq.index bytes i))
    index_proof

let lemma_mask_slice_is_some
  (mask:Seq.seq (option FStar.UInt8.t))
  (lo hi:nat{lo <= hi /\ hi <= Seq.length mask})
  : Lemma
      (requires
        forall (i:nat). i < Seq.length mask ==>
          Some? (Seq.index mask i))
      (ensures
        forall (i:nat). i < Seq.length (Seq.slice mask lo hi) ==>
          Some? (Seq.index (Seq.slice mask lo hi) i))
=
  Seq.lemma_len_slice mask lo hi;
  let index_proof
    (i:nat{i < Seq.length (Seq.slice mask lo hi)})
    : Lemma (Some? (Seq.index (Seq.slice mask lo hi) i))
  =
    Seq.lemma_index_slice mask lo hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length (Seq.slice mask lo hi)})
    #(fun i -> Some? (Seq.index (Seq.slice mask lo hi) i))
    index_proof

let lemma_prefix_mask_matches_bytes
  (prefix:B.bytes)
  (bytes:B.bytes)
  (mask:Seq.seq (option FStar.UInt8.t))
  (hi:nat{hi <= B.length bytes})
  : Lemma
      (requires
        B.length prefix == hi /\
        Seq.length mask == hi /\
        Seq.equal prefix (Seq.slice bytes 0 hi) /\
        (forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index prefix i)))
      (ensures
        forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index bytes i))
=
  Seq.lemma_eq_elim prefix (Seq.slice bytes 0 hi);
  let index_proof
    (i:nat{i < Seq.length mask})
    : Lemma
        (Seq.index mask i == Some (Seq.index bytes i))
  =
    Seq.lemma_index_slice bytes 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length mask})
    #(fun i ->
      Seq.index mask i == Some (Seq.index bytes i))
    index_proof

let lemma_equal_prefix_of_indexes
  (prefix:B.bytes)
  (bytes:B.bytes)
  (hi:nat{hi <= B.length bytes})
  : Lemma
      (requires
        B.length prefix == hi /\
        (forall (i:nat). i < hi ==>
          Seq.index prefix i == Seq.index bytes i))
      (ensures Seq.equal prefix (Seq.slice bytes 0 hi))
=
  Seq.lemma_len_slice bytes 0 hi;
  let index_proof
    (i:nat{i < B.length (Seq.slice bytes 0 hi)})
    : Lemma
        (Seq.index prefix i == Seq.index (Seq.slice bytes 0 hi) i)
  =
    Seq.lemma_index_slice bytes 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < B.length (Seq.slice bytes 0 hi)})
    #(fun i ->
      Seq.index prefix i == Seq.index (Seq.slice bytes 0 hi) i)
    index_proof;
  Seq.lemma_eq_intro prefix (Seq.slice bytes 0 hi)

let lemma_mask_values_at_offset
  (bytes:B.bytes)
  (mask:Seq.seq (option FStar.UInt8.t))
  (offset count:nat)
  : Lemma
      (requires
        offset + count <= B.length bytes /\
        Seq.length mask == B.length bytes /\
        (forall (i:nat). i < B.length bytes ==>
          Some (Seq.index bytes i) == Seq.index mask i))
      (ensures
        forall (i:nat). i < count ==>
          Some (Seq.index bytes (offset + i)) ==
            Seq.index mask (offset + i))
=
  let index_proof
    (i:nat{i < count})
    : Lemma
        (Some (Seq.index bytes (offset + i)) ==
          Seq.index mask (offset + i))
  =
    assert (offset + i < B.length bytes)
  in
  FStar.Classical.forall_intro
    #(i:nat{i < count})
    #(fun i ->
      Some (Seq.index bytes (offset + i)) ==
        Seq.index mask (offset + i))
    index_proof

let joined_mask_matches
  (base replacement joined:Seq.seq (option FStar.UInt8.t))
  (offset upper:nat)
  : prop =
  offset <= upper /\
  upper <= Seq.length joined /\
  Seq.length base == Seq.length joined /\
  upper - offset <= Seq.length replacement /\
  (forall (i:nat). i < Seq.length joined ==>
    Seq.index joined i ==
      (if offset <= i && i < upper
       then Seq.index replacement (i - offset)
       else Seq.index base i))

let lemma_joined_mask_matches_at_offset
  (base replacement joined:Seq.seq (option FStar.UInt8.t))
  (offset upper count:nat)
  : Lemma
      (requires
        joined_mask_matches base replacement joined offset upper /\
        offset + count <= upper /\
        count <= Seq.length replacement)
      (ensures
        forall (i:nat). i < count ==>
          Seq.index joined (offset + i) == Seq.index replacement i)
=
  let index_proof
    (i:nat{i < count})
    : Lemma
        (Seq.index joined (offset + i) == Seq.index replacement i)
  =
    assert (offset <= offset + i);
    assert (offset + i < upper);
    assert ((offset + i) - offset == i)
  in
  FStar.Classical.forall_intro
    #(i:nat{i < count})
    #(fun i ->
      Seq.index joined (offset + i) == Seq.index replacement i)
    index_proof

let lemma_joined_mask_matches_before_offset
  (base replacement joined:Seq.seq (option FStar.UInt8.t))
  (offset upper:nat)
  : Lemma
      (requires joined_mask_matches base replacement joined offset upper)
      (ensures
        forall (i:nat). i < offset ==>
          Seq.index joined i == Seq.index base i)
=
  let index_proof
    (i:nat{i < offset})
    : Lemma (Seq.index joined i == Seq.index base i)
  =
    assert (i < upper);
    assert (~(offset <= i))
  in
  FStar.Classical.forall_intro
    #(i:nat{i < offset})
    #(fun i -> Seq.index joined i == Seq.index base i)
    index_proof

let lemma_joined_mask_matches_is_some
  (base replacement joined:Seq.seq (option FStar.UInt8.t))
  (offset upper:nat)
  : Lemma
      (requires
        joined_mask_matches base replacement joined offset upper /\
        (forall (i:nat). i < Seq.length base ==>
          Some? (Seq.index base i)) /\
        (forall (i:nat). i < Seq.length replacement ==>
          Some? (Seq.index replacement i)))
      (ensures
        forall (i:nat). i < Seq.length joined ==>
          Some? (Seq.index joined i))
=
  let index_proof
    (i:nat{i < Seq.length joined})
    : Lemma (Some? (Seq.index joined i))
  =
    if offset <= i && i < upper then (
      assert (i - offset < upper - offset);
      assert (i - offset < Seq.length replacement)
    ) else (
      assert (i < Seq.length base)
    )
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length joined})
    #(fun i -> Some? (Seq.index joined i))
    index_proof

let lemma_equal_bytes_from_masks_before_offset
  (bytes old_bytes:B.bytes)
  (base joined:Seq.seq (option FStar.UInt8.t))
  (offset:nat)
  : Lemma
      (requires
        offset <= B.length bytes /\
        offset <= B.length old_bytes /\
        offset <= Seq.length base /\
        offset <= Seq.length joined /\
        B.length bytes <= Seq.length joined /\
        Seq.length base <= B.length old_bytes /\
        (forall (i:nat). i < B.length bytes ==>
          Some (Seq.index bytes i) == Seq.index joined i) /\
        (forall (i:nat). i < offset ==>
          Seq.index joined i == Seq.index base i) /\
        (forall (i:nat). i < Seq.length base ==>
          Seq.index base i == Some (Seq.index old_bytes i)))
      (ensures
        forall (i:nat). i < offset ==>
          Seq.index bytes i == Seq.index old_bytes i)
=
  let index_proof
    (i:nat{i < offset})
    : Lemma (Seq.index bytes i == Seq.index old_bytes i)
  =
    assert (i < B.length bytes);
    assert (i < B.length old_bytes);
    assert (i < Seq.length base);
    assert (i < Seq.length joined)
  in
  FStar.Classical.forall_intro
    #(i:nat{i < offset})
    #(fun i -> Seq.index bytes i == Seq.index old_bytes i)
    index_proof

let lemma_equal_slice_of_prefix
  (prefix:B.bytes)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat{
    lo <= hi /\
    hi <= B.length prefix /\
    hi <= B.length bytes
  })
  : Lemma
      (requires Seq.equal prefix (Seq.slice bytes 0 hi))
      (ensures
        Seq.equal
          (Seq.slice prefix lo hi)
          (Seq.slice bytes lo hi))
=
  Seq.lemma_eq_elim prefix (Seq.slice bytes 0 hi);
  FStar.Seq.Properties.slice_slice bytes 0 hi lo hi

let lemma_logged_received_ordered
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (old_consumed:B.bytes)
  : Lemma
      (requires
        CI.ordered_subsequence
          st0.CS.cs_wire_log.CL.raw_received
          old_consumed /\
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out)
      (ensures
        CI.ordered_subsequence
          st1.CS.cs_wire_log.CL.raw_received
          (B.append old_consumed
            (ST.server_network_consumed_prefix buffer_resp input)))
=
  let consumed_prefix =
    ST.server_network_consumed_prefix buffer_resp input in
  let resp = buffer_resp.ST.response in
  match resp.ST.status with
  | ST.NeedMoreInput ->
    assert (st1 == st0);
    CI.lemma_ordered_subsequence_append_right
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      consumed_prefix
  | ST.IllegalTransition ->
    assert (st1 == st0);
    CI.lemma_ordered_subsequence_append_right
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      consumed_prefix
  | ST.DecodeError ->
    assert (ST.decode_error_response st0 st1 resp network_out app_out);
    assert (buffer_resp.ST.consumed_len == 0sz);
    assert (consumed_prefix == Seq.slice input 0 0);
    Seq.lemma_len_slice input 0 0;
    Seq.lemma_eq_intro consumed_prefix B.empty;
    lemma_legal_response_for_event_wire_lengths
      st0
      st1
      resp
      (CS.ConnLocalEvent (CS.LocalFail CM.tls_decode_error))
      B.empty
      B.empty
      network_out
      app_out;
    CI.lemma_ordered_subsequence_append_right
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      consumed_prefix;
    Seq.append_empty_r st0.CS.cs_wire_log.CL.raw_received;
    Seq.lemma_eq_elim
      st1.CS.cs_wire_log.CL.raw_received
      st0.CS.cs_wire_log.CL.raw_received
  | ST.OutputBufferTooSmall ->
    assert False
  | ST.StepOk ->
    assert (ST.server_network_step_ok_received_decode_projection
      st0 st1 buffer_resp input network_out app_out);
    let msg =
      ID.indefinite_description_ghost
        M.tls_message
        (fun msg ->
          CT.received_tls_raw_delta_legal st0 msg consumed_prefix /\
          ST.server_decoded_message_event_projection
            st0 st1 resp msg consumed_prefix network_out app_out /\
          (if CS.network_message_is_cleartext CL.Received msg
           then True
           else
             ST.server_protected_record_decode_correct
               st0 consumed_prefix msg)) in
    assert (ST.server_decoded_message_event_projection
      st0 st1 resp msg consumed_prefix network_out app_out);
    if ST.legal_network_response
      st0 st1 resp msg consumed_prefix network_out app_out then (
      assert (ST.legal_response_for_event
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        consumed_prefix
        network_out
        app_out);
      lemma_legal_response_for_event_wire_lengths
        st0
        st1
        resp
        (ST.received_message_event msg)
        B.empty
        consumed_prefix
        network_out
        app_out;
      CI.lemma_ordered_subsequence_append_both
        st0.CS.cs_wire_log.CL.raw_received
        old_consumed
        consumed_prefix;
      Seq.lemma_eq_elim
        st1.CS.cs_wire_log.CL.raw_received
        (B.append st0.CS.cs_wire_log.CL.raw_received consumed_prefix)
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
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal raw_received consumed_prefix /\
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
            CM.received_alert_failure_state st0 alert raw_received /\
          Seq.equal raw_received consumed_prefix /\
          ST.legal_network_response
            st0
            st1
            resp
            (M.TlsAlert alert)
            raw_received
            network_out
            app_out) in
    assert (Seq.equal raw_received consumed_prefix);
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
    Seq.lemma_eq_elim raw_received consumed_prefix;
    CI.lemma_ordered_subsequence_append_both
      st0.CS.cs_wire_log.CL.raw_received
      old_consumed
      consumed_prefix;
    Seq.lemma_eq_elim
      st1.CS.cs_wire_log.CL.raw_received
      (B.append st0.CS.cs_wire_log.CL.raw_received consumed_prefix)

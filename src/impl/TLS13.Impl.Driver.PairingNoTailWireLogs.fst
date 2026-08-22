module TLS13.Impl.Driver.PairingNoTailWireLogs

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CW = TLS13.Spec.Endpoint.Wire
module CTypes = TLS13.Impl.CanonicalTypes
module EAPI = TLS13.Spec.Endpoint.API
module L = FStar.List.Tot
module RVD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SM = Common.StateMachine
module TCP = Common.TCP
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module W = TLS13.Wire.Spec
module WU = TLS13.Wire.Spec.Reveal.Util

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
    with
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

let lemma_wire_parse_empty_none ()
  : Lemma (CW.wire_parse Seq.empty == None)
=
  match W.parse_record_wire Seq.empty with
  | None -> ()
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_wire_some_consumed_positive
      Seq.empty
      content_type
      fragment
      consumed;
    assert False

let lemma_wire_parse_serialize_prefix
  (msg:CW.wire_message)
  (tail:B.bytes)
  : Lemma
      (ensures
        exists parsed.
          CW.wire_parse (B.append (CW.wire_serialize msg) tail) ==
            Some (parsed, tail) /\
          parsed == msg)
=
  assert (CW.wire_serialize msg == msg.CW.wm_raw);
  assert (W.parse_record_wire msg.CW.wm_raw ==
    Some (msg.CW.wm_content_type, msg.CW.wm_fragment, B.length msg.CW.wm_raw));
  let full = B.append msg.CW.wm_raw tail in
  Seq.lemma_len_append msg.CW.wm_raw tail;
  WU.lemma_slice_append_left msg.CW.wm_raw tail;
  Seq.lemma_eq_elim
    (Seq.slice full 0 (B.length msg.CW.wm_raw))
    msg.CW.wm_raw;
  RVD.lemma_parse_record_wire_from_prefix
    full
    msg.CW.wm_content_type
    msg.CW.wm_fragment
    (B.length msg.CW.wm_raw);
  assert (W.parse_record_wire full ==
    Some (msg.CW.wm_content_type, msg.CW.wm_fragment, B.length msg.CW.wm_raw));
  CL.lemma_raw_slice_append_suffix msg.CW.wm_raw tail;
  assert (CL.raw_slice full (B.length msg.CW.wm_raw) (B.length full) ==
    Seq.slice full (B.length msg.CW.wm_raw) (B.length full));
  Seq.lemma_eq_elim
    tail
    (Seq.slice full (B.length msg.CW.wm_raw) (B.length full));
  match CW.wire_parse full with
  | None ->
    assert False
  | Some (parsed, rest) ->
    assert (rest == tail);
    assert (parsed.CW.wm_raw == msg.CW.wm_raw);
    assert (parsed.CW.wm_content_type == msg.CW.wm_content_type);
    assert (parsed.CW.wm_fragment == msg.CW.wm_fragment);
    assert (parsed == msg);
    assert (exists parsed'.
      CW.wire_parse (B.append (CW.wire_serialize msg) tail) ==
        Some (parsed', tail) /\
      parsed' == msg)

let rec lemma_wire_parse_serialize_with_tail_inverse
  (msgs:list CW.wire_message)
  (tail:B.bytes)
  : Lemma
      (ensures
        WF.parses_as
          CW.tls_record_wire_format
          (WF.serialize_with_tail CW.tls_record_wire_format msgs tail)
          msgs
          tail)
      (decreases msgs)
=
  match msgs with
  | [] ->
    assert (Seq.equal tail tail)
  | msg :: rest ->
    lemma_wire_parse_serialize_prefix
      msg
      (WF.serialize_with_tail CW.tls_record_wire_format rest tail);
    lemma_wire_parse_serialize_with_tail_inverse rest tail;
    assert (exists parsed_msg bytes_after_msg.
      CW.wire_parse
        (WF.serialize_with_tail CW.tls_record_wire_format (msg :: rest) tail) ==
        Some (parsed_msg, bytes_after_msg) /\
      parsed_msg == msg /\
      WF.parses_as
        CW.tls_record_wire_format
        bytes_after_msg
        rest
        tail)

let lemma_wire_parse_serialize_all_inverse
  (msgs:list CW.wire_message)
  : Lemma
      (ensures
        WF.parses_as
          CW.tls_record_wire_format
          (WF.serialize_all CW.tls_record_wire_format msgs)
          msgs
          Seq.empty)
=
  lemma_wire_parse_serialize_with_tail_inverse msgs Seq.empty

let rec lemma_wire_parses_as_unique_empty_residual
  (bytes:B.bytes)
  (left:list CW.wire_message)
  (right:list CW.wire_message)
  : Lemma
      (requires
        WF.parses_as CW.tls_record_wire_format bytes left Seq.empty /\
        WF.parses_as CW.tls_record_wire_format bytes right Seq.empty)
      (ensures left == right)
      (decreases left)
=
  match left, right with
  | [], [] -> ()
  | [], r_hd :: r_tl ->
    assert (Seq.equal bytes Seq.empty);
    Seq.lemma_eq_elim bytes Seq.empty;
    lemma_wire_parse_empty_none ();
    eliminate exists (parsed_msg:CW.wire_message) (bytes_after_msg:B.bytes).
      CW.wire_parse bytes == Some (parsed_msg, bytes_after_msg) /\
      parsed_msg == r_hd /\
      WF.parses_as
        CW.tls_record_wire_format
        bytes_after_msg
        r_tl
        Seq.empty
    with
    (
      assert False
    )
  | l_hd :: l_tl, [] ->
    assert (Seq.equal bytes Seq.empty);
    Seq.lemma_eq_elim bytes Seq.empty;
    lemma_wire_parse_empty_none ();
    eliminate exists (parsed_msg:CW.wire_message) (bytes_after_msg:B.bytes).
      CW.wire_parse bytes == Some (parsed_msg, bytes_after_msg) /\
      parsed_msg == l_hd /\
      WF.parses_as
        CW.tls_record_wire_format
        bytes_after_msg
        l_tl
        Seq.empty
    with
    (
      assert False
    )
  | l_hd :: l_tl, r_hd :: r_tl ->
    eliminate exists (left_msg:CW.wire_message) (left_after:B.bytes).
      CW.wire_parse bytes == Some (left_msg, left_after) /\
      left_msg == l_hd /\
      WF.parses_as
        CW.tls_record_wire_format
        left_after
        l_tl
        Seq.empty
    with
    (
      eliminate exists (right_msg:CW.wire_message) (right_after:B.bytes).
        CW.wire_parse bytes == Some (right_msg, right_after) /\
        right_msg == r_hd /\
        WF.parses_as
          CW.tls_record_wire_format
          right_after
          r_tl
          Seq.empty
      with
      (
        assert (left_msg == right_msg);
        assert (left_after == right_after);
        assert (l_hd == r_hd);
        lemma_wire_parses_as_unique_empty_residual
          left_after
          l_tl
          r_tl;
        assert (l_tl == r_tl)
      )
    )

let lemma_wire_serialize_all_injective
  (left:list CW.wire_message)
  (right:list CW.wire_message)
  : Lemma
      (requires
        Seq.equal
          (WF.serialize_all CW.tls_record_wire_format left)
          (WF.serialize_all CW.tls_record_wire_format right))
      (ensures left == right)
=
  lemma_wire_parse_serialize_all_inverse left;
  lemma_wire_parse_serialize_all_inverse right;
  Seq.lemma_eq_elim
    (WF.serialize_all CW.tls_record_wire_format left)
    (WF.serialize_all CW.tls_record_wire_format right);
  lemma_wire_parses_as_unique_empty_residual
    (WF.serialize_all CW.tls_record_wire_format left)
    left
    right

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

(* Appending a residual tail to the full serialization of [msgs] yields exactly
   the serialization of [msgs] with that tail.  Combined with the parse/serialize
   inverse for the strong-prefix TLS record format, this bridges the DATAGRAM
   (serialize-equality) disjunct of [WFSM.valid_byte_trace] back to the STREAM
   (parses_as) disjunct that the strong-prefix consumers rely on. *)
let rec lemma_wire_serialize_all_append_tail
  (msgs:list CW.wire_message)
  (tail:TCP.bytes)
  : Lemma
      (ensures
        Seq.equal
          (Seq.append
            (WF.serialize_all CW.tls_record_wire_format msgs)
            tail)
          (WF.serialize_with_tail CW.tls_record_wire_format msgs tail))
      (decreases msgs)
=
  match msgs with
  | [] ->
    Seq.append_empty_l tail
  | msg :: rest ->
    lemma_wire_serialize_all_append_tail rest tail;
    Seq.append_assoc
      (CW.wire_serialize msg)
      (WF.serialize_all CW.tls_record_wire_format rest)
      tail

let lemma_client_step_wire_log_delta
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTypes.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 ev st1 out)
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
    eliminate exists (conn_ev:CS.conn_event).
      (EC.client_wire_received_event st0 wire conn_ev /\
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
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
    with
    (
      assert (WFSM.event_input_messages ev == [wire]);
      Seq.append_empty_r (CW.wire_serialize wire)
    )
  | SM.LocalEvent local ->
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      CTypes.client_local_event_matches st0 local conn_ev /\
      EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        }
        st1
    with
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
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 ev st1 out)
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
    (* Generalised with [server_step]: a wire record may be attributed to a
       cleartext buffering step as well as to a delivered message, and the
       wire-log conclusion is the same either way. *)
    eliminate exists conn_ev.
      (ES.server_wire_received_event conn_ev /\
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
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
    with
    (
      assert (WFSM.event_input_messages ev == [wire]);
      Seq.append_empty_r (CW.wire_serialize wire)
    )
  | SM.LocalEvent local ->
    eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
      CTypes.server_local_event_matches local conn_ev /\
      ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
      ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
      CS.legal_connection_delta
        st0
        {
          CS.delta_event = conn_ev;
          CS.delta_raw_sent = raw_sent;
          CS.delta_raw_received = B.empty;
        }
        st1
    with
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
  (initial:EC.client_initial_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.client_local_event
      EAPI.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (EC.client_state_machine #CTypes.client_local_event initial)
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
    assert (EC.client_step
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
  (initial:ES.server_initial_state)
  (st0:CS.connection_state)
  (trace:list
    (SM.transition
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      EAPI.local_output))
  (st1:CS.connection_state)
  : Lemma
      (requires
        SM.trace_reaches
          (ES.server_state_machine #CTypes.server_local_event initial)
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
    assert (ES.server_step
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

(* Bridge lemma: [WFSM.valid_byte_trace] was WEAKENED on its input side to a
   disjunction (STREAM [parses_as] OR DATAGRAM [serialize-equality]) to also serve
   datagram transports.  The TLS client binds the strong-prefix
   [CW.tls_record_wire_format], for which the DATAGRAM disjunct implies the STREAM
   disjunct.  This lemma re-derives, via an SMTPat, the pre-weakening STRONG
   existential (with a bare [parses_as]) that the strong-prefix consumers below
   [eliminate] unchanged. *)
let lemma_client_valid_byte_trace_strong_parse
  (client_initial:EC.client_initial_state)
  (client_received:B.bytes)
  (client:CS.connection_state)
  (client_sent:B.bytes)
  (residual:TCP.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (EC.client_system #CTypes.client_local_event client_initial)
          client_received
          client
          client_sent
          residual)
      (ensures
        exists (trace:list (SM.transition
                              CS.connection_state
                              CW.wire_message
                              CTypes.client_local_event
                              EAPI.local_output)).
          SM.trace_reaches
            (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine
            (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
            trace
            client /\
          WF.parses_as
            (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
            client_received
            (WFSM.trace_input_messages trace)
            residual /\
          Seq.equal
            client_sent
            (WF.serialize_all
              (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
              (SM.trace_wire_outputs trace)))
      [SMTPat
        (WFSM.valid_byte_trace
          (EC.client_system #CTypes.client_local_event client_initial)
          client_received
          client
          client_sent
          residual)]
=
  assert ((EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format ==
    CW.tls_record_wire_format);
  eliminate exists trace.
    SM.trace_reaches
      (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine
      (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      client /\
    (WF.parses_as
       (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
       client_received
       (WFSM.trace_input_messages trace)
       residual
     \/
     Seq.equal
       client_received
       (Seq.append
         (WF.serialize_all
           (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual)) /\
    Seq.equal
      client_sent
      (WF.serialize_all
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  with
  (
    introduce
      Seq.equal
        client_received
        (Seq.append
          (WF.serialize_all
            (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
            (WFSM.trace_input_messages trace))
          residual)
      ==>
      WF.parses_as
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
        client_received
        (WFSM.trace_input_messages trace)
        residual
    with
    (
      lemma_wire_serialize_all_append_tail
        (WFSM.trace_input_messages trace)
        residual;
      Seq.lemma_eq_elim
        (Seq.append
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.trace_input_messages trace))
          residual)
        (WF.serialize_with_tail
          CW.tls_record_wire_format
          (WFSM.trace_input_messages trace)
          residual);
      Seq.lemma_eq_elim
        client_received
        (Seq.append
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.trace_input_messages trace))
          residual);
      lemma_wire_parse_serialize_with_tail_inverse
        (WFSM.trace_input_messages trace)
        residual;
      assert (WF.parses_as
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
        client_received
        (WFSM.trace_input_messages trace)
        residual)
    );
    assert (exists (trace':list (SM.transition
                                  CS.connection_state
                                  CW.wire_message
                                  CTypes.client_local_event
                                  EAPI.local_output)).
      SM.trace_reaches
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        client /\
      WF.parses_as
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
        client_received
        (WFSM.trace_input_messages trace')
        residual /\
      Seq.equal
        client_sent
        (WF.serialize_all
          (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_server_valid_byte_trace_strong_parse
  (server_initial:ES.server_initial_state)
  (server_received:B.bytes)
  (server:CS.connection_state)
  (server_sent:B.bytes)
  (residual:TCP.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (ES.server_system #CTypes.server_local_event server_initial)
          server_received
          server
          server_sent
          residual)
      (ensures
        exists (trace:list (SM.transition
                              CS.connection_state
                              CW.wire_message
                              CTypes.server_local_event
                              EAPI.local_output)).
          SM.trace_reaches
            (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine
            (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
            trace
            server /\
          WF.parses_as
            (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
            server_received
            (WFSM.trace_input_messages trace)
            residual /\
          Seq.equal
            server_sent
            (WF.serialize_all
              (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
              (SM.trace_wire_outputs trace)))
      [SMTPat
        (WFSM.valid_byte_trace
          (ES.server_system #CTypes.server_local_event server_initial)
          server_received
          server
          server_sent
          residual)]
=
  assert ((ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format ==
    CW.tls_record_wire_format);
  eliminate exists trace.
    SM.trace_reaches
      (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine
      (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      server /\
    (WF.parses_as
       (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
       server_received
       (WFSM.trace_input_messages trace)
       residual
     \/
     Seq.equal
       server_received
       (Seq.append
         (WF.serialize_all
           (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
           (WFSM.trace_input_messages trace))
         residual)) /\
    Seq.equal
      server_sent
      (WF.serialize_all
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  with
  (
    introduce
      Seq.equal
        server_received
        (Seq.append
          (WF.serialize_all
            (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
            (WFSM.trace_input_messages trace))
          residual)
      ==>
      WF.parses_as
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
        server_received
        (WFSM.trace_input_messages trace)
        residual
    with
    (
      lemma_wire_serialize_all_append_tail
        (WFSM.trace_input_messages trace)
        residual;
      Seq.lemma_eq_elim
        (Seq.append
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.trace_input_messages trace))
          residual)
        (WF.serialize_with_tail
          CW.tls_record_wire_format
          (WFSM.trace_input_messages trace)
          residual);
      Seq.lemma_eq_elim
        server_received
        (Seq.append
          (WF.serialize_all
            CW.tls_record_wire_format
            (WFSM.trace_input_messages trace))
          residual);
      lemma_wire_parse_serialize_with_tail_inverse
        (WFSM.trace_input_messages trace)
        residual;
      assert (WF.parses_as
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
        server_received
        (WFSM.trace_input_messages trace)
        residual)
    );
    assert (exists (trace':list (SM.transition
                                  CS.connection_state
                                  CW.wire_message
                                  CTypes.server_local_event
                                  EAPI.local_output)).
      SM.trace_reaches
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
        trace'
        server /\
      WF.parses_as
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
        server_received
        (WFSM.trace_input_messages trace')
        residual /\
      Seq.equal
        server_sent
        (WF.serialize_all
          (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
          (SM.trace_wire_outputs trace')))
  )

let lemma_client_valid_byte_trace_inverts_to_serialized_trace
  (client_initial:EC.client_initial_state)
  (client_received:B.bytes)
  (client:CS.connection_state)
  (client_sent:B.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (EC.client_system #CTypes.client_local_event client_initial)
          client_received
          client
          client_sent
          Seq.empty)
      (ensures
        exists (trace:list
          (SM.transition
            CS.connection_state
            CW.wire_message
            CTypes.client_local_event
            EAPI.local_output)).
          SM.trace_reaches
            (EC.client_state_machine #CTypes.client_local_event client_initial)
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
      (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine
      (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      client /\
    WF.parses_as
      (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
      client_received
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      client_sent
      (WF.serialize_all
        (EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  with
  (
    lemma_wire_parses_as_serialize_all
      client_received
      (WFSM.trace_input_messages trace);
    assert ((EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    assert ((EC.client_system #CTypes.client_local_event client_initial).WFSM.wfsm_state_machine ==
      EC.client_state_machine #CTypes.client_local_event client_initial);
    assert ((EC.client_state_machine #CTypes.client_local_event client_initial).SM.sm_initial_state ==
      client_initial);
    assert (exists (trace':list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.client_local_event
        EAPI.local_output)).
      SM.trace_reaches
        (EC.client_state_machine #CTypes.client_local_event client_initial)
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
  (server_initial:ES.server_initial_state)
  (server_received:B.bytes)
  (server:CS.connection_state)
  (server_sent:B.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          (ES.server_system #CTypes.server_local_event server_initial)
          server_received
          server
          server_sent
          Seq.empty)
      (ensures
        exists (trace:list
          (SM.transition
            CS.connection_state
            CW.wire_message
            CTypes.server_local_event
            EAPI.local_output)).
          SM.trace_reaches
            (ES.server_state_machine #CTypes.server_local_event server_initial)
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
      (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine
      (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      server /\
    WF.parses_as
      (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
      server_received
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      server_sent
      (WF.serialize_all
        (ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format
        (SM.trace_wire_outputs trace))
  with
  (
    lemma_wire_parses_as_serialize_all
      server_received
      (WFSM.trace_input_messages trace);
    assert ((ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_wire_format ==
      CW.tls_record_wire_format);
    assert ((ES.server_system #CTypes.server_local_event server_initial).WFSM.wfsm_state_machine ==
      ES.server_state_machine #CTypes.server_local_event server_initial);
    assert ((ES.server_state_machine #CTypes.server_local_event server_initial).SM.sm_initial_state ==
      server_initial);
    assert (exists (trace':list
      (SM.transition
        CS.connection_state
        CW.wire_message
        CTypes.server_local_event
        EAPI.local_output)).
      SM.trace_reaches
        (ES.server_state_machine #CTypes.server_local_event server_initial)
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
  (client_initial:EC.client_initial_state)
  (client_received:B.bytes)
  (client:CS.connection_state)
  (client_sent:B.bytes)
  : Lemma
      (requires
        client_initial ==
          CS.initial client_initial.CS.cs_model.CS.model_config /\
        WFSM.valid_byte_trace
          (EC.client_system #CTypes.client_local_event client_initial)
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
      (EC.client_state_machine #CTypes.client_local_event client_initial)
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
  with
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
  (server_initial:ES.server_initial_state)
  (server_received:B.bytes)
  (server:CS.connection_state)
  (server_sent:B.bytes)
  : Lemma
      (requires
        server_initial ==
          CS.initial server_initial.CS.cs_model.CS.model_config /\
        WFSM.valid_byte_trace
          (ES.server_system #CTypes.server_local_event server_initial)
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
      (ES.server_state_machine #CTypes.server_local_event server_initial)
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
  with
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

module TLS13.Spec.StateMachine.Canonical

(**
  Clean public spec boundary for the canonical wire-level protocol step.

  [canonical_wire_step] is the pure TLS 1.3 semantic relation used at the
  Common.ProtocolImplementation boundary: a step from [st0] to [st1] labelled by
  a connection event [conn_ev] is canonical for the raw sent/received byte
  strings when it is a legal connection-state delta AND those bytes are exactly
  the seal (send) / decode (receive) projections of the event.  Both the client
  and server CanonicalProtocol implementations instantiate their
  Common.StateMachine step relation on top of this predicate, so the TLS
  semantic content lives here in spec rather than being duplicated in impl.

  This module is part of the core semantics. It defines the exact relation
  between semantic protected messages and their raw records, including
  multi-record application-data sends. Trace replay and invariant lemmas build
  on this relation from the properties layer.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RF = TLS13.Spec.StateMachine.RecordFraming
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

open TLS13.Spec.StateMachine

let record_header_aad (raw:B.bytes) : GTot B.bytes =
  if B.length raw >= 5
  then Seq.slice raw 0 5
  else B.empty

let application_data_record_header (fragment_len:nat) : GTot B.bytes =
  record_header_aad
    (W.serialize_record T.Application_data (Seq.create fragment_len 0uy))

let sent_tls_inner_plaintext_fragment (msg:M.tls_message) : GTot B.bytes =
  let (content_type, fragment) = W.serialize_tls_message msg in
  W.serialize_plaintext {
    M.content_type = content_type;
    M.fragment = fragment;
  }

let sent_single_protected_message_seal_from
  (write_state:R.direction_state)
  (msg:M.tls_message)
  (raw:B.bytes)
  : prop =
  exists ciphertext.
    W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
    R.seal
      write_state
      (record_header_aad raw)
      {
        R.content_type = T.Application_data;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext, R.next_seq write_state)

let sent_single_protected_message_seal
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : prop =
  sent_single_protected_message_seal_from model.model_record.record_write msg raw

let rec sent_application_data_records_seal_from
  (write_state:R.direction_state)
  (bytes:B.bytes)
  (raw:B.bytes)
  : Tot prop (decreases B.length bytes)
  =
  if B.length bytes <= RF.max_application_data_fragment_len then
    sent_single_protected_message_seal_from
      write_state
      (M.TlsApplicationData bytes)
      raw
  else
    let head =
      Seq.slice bytes 0 RF.max_application_data_fragment_len in
    let tail =
      Seq.slice
        bytes
        RF.max_application_data_fragment_len
        (B.length bytes) in
    exists raw_head raw_tail.
      Seq.equal raw (B.append raw_head raw_tail) /\
      sent_single_protected_message_seal_from
        write_state
        (M.TlsApplicationData head)
        raw_head /\
      sent_application_data_records_seal_from
        (R.next_seq write_state)
        tail
        raw_tail

let sent_application_data_records_seal
  (model:connection_model)
  (bytes:B.bytes)
  (raw:B.bytes)
  : prop =
  sent_application_data_records_seal_from
    model.model_record.record_write
    bytes
    raw

let sent_event_seal_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  : prop =
  match ev with
  | ConnNetworkEvent msg ->
    if msg.CL.message_direction == CL.Sent &&
       network_message_is_cleartext
         msg.CL.message_direction
         msg.CL.message_value == false
    then
      match msg.CL.message_value with
      | M.TlsApplicationData bytes ->
        sent_application_data_records_seal model bytes raw_sent
      | protected_msg ->
        sent_single_protected_message_seal model protected_msg raw_sent
    else True
  | ConnProtectedHandshake _ ->
    True
  | ConnLocalEvent _ ->
    True

let sent_event_nonempty_seal_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  : prop =
  B.length raw_sent == 0 \/
  sent_event_seal_projection model ev raw_sent

let received_record_opened
  (model:connection_model)
  (raw_received:B.bytes)
  (outer_fragment:B.bytes)
  (opened:B.bytes)
  : prop =
  exists read_state'.
    R.open_record
      model.model_record.record_read
      (record_header_aad raw_received)
      outer_fragment ==
      Some (opened, read_state')

let received_single_protected_message_decode
  (model:connection_model)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened plaintext.
    W.parse_record_wire raw_received ==
      Some (T.Application_data, outer_fragment, B.length raw_received) /\
    received_record_opened model raw_received outer_fragment opened /\
    W.parse_plaintext opened == Some plaintext /\
    W.parse_tls_message plaintext.M.content_type plaintext.M.fragment == Some msg

let received_protected_handshake_head_decode
  (model:connection_model)
  (step:protected_handshake_step)
  (raw_received:B.bytes)
  : prop =
  exists outer_fragment opened plaintext.
    W.parse_record_wire raw_received ==
      Some (T.Application_data, outer_fragment, B.length raw_received) /\
    received_record_opened model raw_received outer_fragment opened /\
    W.parse_plaintext opened == Some plaintext /\
    plaintext.M.content_type == T.Handshake /\
    Seq.equal plaintext.M.fragment step.protected_handshake_fragment /\
    step.protected_handshake_offset <=
      B.length step.protected_handshake_fragment /\
    W.parse_handshake
      (Seq.slice
        step.protected_handshake_fragment
        step.protected_handshake_offset
        (B.length step.protected_handshake_fragment)) ==
      Some
        (step.protected_handshake_message,
         step.protected_handshake_consumed)

let received_event_decode_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_received:B.bytes)
  : prop =
  match ev with
  | ConnNetworkEvent msg ->
    if msg.CL.message_direction == CL.Received &&
       network_message_is_cleartext
         msg.CL.message_direction
         msg.CL.message_value == false
    then received_single_protected_message_decode model msg.CL.message_value raw_received
    else True
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then received_protected_handshake_head_decode model step raw_received
    else True
  | ConnLocalEvent _ ->
    True

let received_event_nonempty_decode_projection
  (model:connection_model)
  (ev:conn_event)
  (raw_received:B.bytes)
  : prop =
  B.length raw_received == 0 \/
  received_event_decode_projection model ev raw_received

unfold
let canonical_wire_step
  (st0:connection_state)
  (st1:connection_state)
  (conn_ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : prop =
  legal_connection_delta
    st0
    {
      delta_event = conn_ev;
      delta_raw_sent = raw_sent;
      delta_raw_received = raw_received;
    }
    st1 /\
  sent_event_nonempty_seal_projection
    st0.cs_model
    conn_ev
    raw_sent /\
  received_event_nonempty_decode_projection
    st0.cs_model
    conn_ev
    raw_received

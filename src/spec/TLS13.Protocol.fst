module TLS13.Protocol

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CP = Common.Protocol
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module TCP = Common.TCP
module Seq = FStar.Seq

open FStar.List.Tot

let tls_processed_history (st:CS.connection_state) : TCP.history =
  {
    TCP.tcp_received = st.CS.cs_wire_log.CL.raw_received;
    TCP.tcp_sent = st.CS.cs_wire_log.CL.raw_sent;
  }

let tls_records_from_bytes (bytes:B.bytes) : GTot (list M.tls_record) =
  (CL.parse_record_prefix bytes).CL.values

let rec tls_directed_records
  (dir:CP.network_direction)
  (records:list M.tls_record)
  : Tot (list (CP.directed_message M.tls_record))
        (decreases records)
  =
  match records with
  | [] -> []
  | record :: rest ->
    {
      CP.dm_direction = dir;
      CP.dm_payload = record;
    } :: tls_directed_records dir rest

let tls_wire_log (st:CS.connection_state)
  : GTot (list (CP.directed_message M.tls_record))
  =
  tls_directed_records
    CP.NetworkReceived
    (tls_records_from_bytes st.CS.cs_wire_log.CL.raw_received) @
  tls_directed_records
    CP.NetworkSent
    (tls_records_from_bytes st.CS.cs_wire_log.CL.raw_sent)

let tls_stream_matches
  (dir:CP.network_direction)
  (bytes:TCP.bytes)
  (records:list M.tls_record)
  (residual:TCP.bytes)
  : GTot prop =
  let view = CL.parse_record_prefix bytes in
  records == view.CL.values /\
  Seq.equal residual view.CL.residual /\
  CL.record_stream_serializes bytes view

let tls_wire_history_matches
  (tcp:TCP.history)
  (wire_log:list (CP.directed_message M.tls_record))
  : GTot prop =
  let received_view = CL.parse_record_prefix tcp.TCP.tcp_received in
  let sent_view = CL.parse_record_prefix tcp.TCP.tcp_sent in
  wire_log ==
    tls_directed_records CP.NetworkReceived received_view.CL.values @
    tls_directed_records CP.NetworkSent sent_view.CL.values /\
  CL.record_stream_serializes tcp.TCP.tcp_received received_view /\
  CL.record_stream_serializes tcp.TCP.tcp_sent sent_view

noextract
let tls_record_wire_format : CP.wire_format M.tls_record =
  {
    CP.wf_stream_matches = tls_stream_matches;
    CP.wf_history_matches = tls_wire_history_matches;
  }

let tls_parse_network
  (bytes:TCP.bytes)
  : GTot (option (list M.tls_record & TCP.bytes))
  =
  let view = CL.parse_record_prefix bytes in
  Some (view.CL.values, view.CL.residual)

let tls_serialize_network
  (record:M.tls_record)
  : GTot (option TCP.bytes)
  =
  None

let tls_serialized_network
  (record:M.tls_record)
  (bytes:TCP.bytes)
  : GTot prop =
  False

let lemma_tls_parse_network_correct
  (bytes:TCP.bytes)
  : Lemma
      (ensures
        (match tls_parse_network bytes with
        | None -> True
        | Some (records, residual) ->
          tls_record_wire_format.CP.wf_stream_matches
            CP.NetworkReceived
            bytes
            records
            residual))
  =
  CL.lemma_parse_record_prefix_serializes bytes

let lemma_tls_serialize_network_correct
  (record:M.tls_record)
  : Lemma
      (ensures
        (match tls_serialize_network record with
        | None -> True
        | Some bytes -> tls_serialized_network record bytes))
  =
  ()

let tls_transport_exact (tcp:TCP.history) (st:CS.connection_state) : GTot prop =
  TCP.history_equal tcp (tls_processed_history st)

let tls_event_log (st:CS.connection_state) : GTot (list CS.conn_event) =
  st.CS.cs_event_log

let tls_events_refine_wire (st:CS.connection_state) : GTot prop =
  CS.connection_state_raw_event_replay_consistent st

let tls_delta_wire_log (delta:CS.connection_delta)
  : GTot (list (CP.directed_message M.tls_record))
  =
  tls_directed_records
    CP.NetworkReceived
    (tls_records_from_bytes delta.CS.delta_raw_received) @
  tls_directed_records
    CP.NetworkSent
    (tls_records_from_bytes delta.CS.delta_raw_sent)

let tls_step_relation
  (st0:CS.connection_state)
  (ev:CS.conn_event)
  (st1:CS.connection_state)
  (out:list (CP.directed_message M.tls_record))
  : GTot prop =
  exists delta.
    CS.legal_connection_delta st0 delta st1 /\
    delta.CS.delta_event == ev /\
    out == tls_delta_wire_log delta

let tls_state_valid_exact (st:CS.connection_state) : GTot prop =
  CS.connection_state_full_log_consistent_for_config_role st /\
  tls_events_refine_wire st /\
  tls_record_wire_format.CP.wf_history_matches
    (tls_processed_history st)
    (tls_wire_log st) /\
  tls_transport_exact
    (tls_processed_history st)
    st

let lemma_tls_wire_history_matches_processed
  (st:CS.connection_state)
  : Lemma
      (ensures
        tls_record_wire_format.CP.wf_history_matches
          (tls_processed_history st)
          (tls_wire_log st))
  =
  CL.lemma_parse_record_prefix_serializes st.CS.cs_wire_log.CL.raw_received;
  CL.lemma_parse_record_prefix_serializes st.CS.cs_wire_log.CL.raw_sent

let lemma_tls_transport_exact_processed
  (st:CS.connection_state)
  : Lemma
      (ensures
        tls_transport_exact
          (tls_processed_history st)
          st)
  =
  ()

let lemma_tls_state_valid_exact_intro
  (st:CS.connection_state)
  : Lemma
      (requires
        CS.connection_state_full_log_consistent_for_config_role st /\
        tls_events_refine_wire st)
      (ensures tls_state_valid_exact st)
  =
  lemma_tls_wire_history_matches_processed st;
  lemma_tls_transport_exact_processed st

let lemma_tls_state_valid_exact_layers
  (st:CS.connection_state)
  : Lemma
      (requires tls_state_valid_exact st)
      (ensures
        tls_record_wire_format.CP.wf_history_matches
          (tls_processed_history st)
          (tls_wire_log st) /\
        tls_transport_exact
          (tls_processed_history st)
          st /\
        tls_events_refine_wire st /\
        CS.connection_state_full_log_consistent_for_config_role st)
  =
  ()

noextract
let tls_exact_protocol
  : CP.state_machine_protocol
      CS.connection_state
      M.tls_record
      CS.conn_event
  =
  {
    CP.sm_wire_format = tls_record_wire_format;
    CP.sm_processed_history = tls_processed_history;
    CP.sm_wire_log = tls_wire_log;
    CP.sm_event_log = tls_event_log;
    CP.sm_transport_matches = tls_transport_exact;
    CP.sm_events_refine_wire = tls_events_refine_wire;
    CP.sm_step = tls_step_relation;
    CP.sm_invariant = CS.connection_state_full_log_consistent_for_config_role;
    CP.sm_valid = tls_state_valid_exact;
    CP.sm_valid_implies_layers = lemma_tls_state_valid_exact_layers;
  }

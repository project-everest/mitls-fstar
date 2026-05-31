module TLS13.ConnectionLog

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module L = FStar.List.Tot
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module T = TLS13.Types
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open FStar.List.Tot

type direction =
  | Sent
  | Received

type raw_io_log = {
  raw_sent: B.bytes;
  raw_received: B.bytes;
}

let empty_raw_io_log : raw_io_log =
  { raw_sent = B.empty; raw_received = B.empty }

let is_prefix (prefix:B.bytes) (full:B.bytes) : GTot bool =
  B.length prefix <= B.length full &&
  Seq.equal prefix (Seq.slice full 0 (B.length prefix))

let bytes_extends (old:B.bytes) (next:B.bytes) : prop =
  B.length old <= B.length next /\
  Seq.equal old (Seq.slice next 0 (B.length old))

let lemma_bytes_extends_refl (bytes:B.bytes)
  : Lemma (bytes_extends bytes bytes)
  =
  Seq.lemma_len_slice bytes 0 (B.length bytes);
  assert (forall (i:nat{i < B.length bytes}).
            Seq.index bytes i == Seq.index (Seq.slice bytes 0 (B.length bytes)) i);
  Seq.lemma_eq_intro bytes (Seq.slice bytes 0 (B.length bytes))

let lemma_bytes_extends_append (old:B.bytes) (delta:B.bytes)
  : Lemma (bytes_extends old (B.append old delta))
  =
  Seq.lemma_len_append old delta;
  Seq.lemma_len_slice (B.append old delta) 0 (B.length old);
  assert (forall (i:nat{i < B.length old}).
            Seq.index old i == Seq.index (Seq.slice (B.append old delta) 0 (B.length old)) i);
  Seq.lemma_eq_intro old (Seq.slice (B.append old delta) 0 (B.length old))

let raw_io_log_extends (old:raw_io_log) (next:raw_io_log) : prop =
  bytes_extends old.raw_sent next.raw_sent /\
  bytes_extends old.raw_received next.raw_received

let raw_io_log_same_sent (old:raw_io_log) (next:raw_io_log) : prop =
  old.raw_sent == next.raw_sent

let raw_io_log_same_received (old:raw_io_log) (next:raw_io_log) : prop =
  old.raw_received == next.raw_received

let raw_slice (bytes:B.bytes) (lo:nat) (hi:nat) : B.bytes =
  if lo <= hi && hi <= B.length bytes
  then Seq.slice bytes lo hi
  else B.empty

let lemma_raw_slice_append_suffix (prefix:B.bytes) (suffix:B.bytes)
  : Lemma
      (ensures Seq.equal suffix
        (raw_slice (B.append prefix suffix) (B.length prefix) (B.length (B.append prefix suffix))))
  =
  let full = B.append prefix suffix in
  Seq.lemma_len_append prefix suffix;
  assert (B.length full == B.length prefix + B.length suffix);
  assert (B.length prefix <= B.length full);
  assert (raw_slice full (B.length prefix) (B.length full) ==
          Seq.slice full (B.length prefix) (B.length full));
  SP.append_slices prefix suffix;
  assert (Seq.equal suffix
    (Seq.slice full (B.length prefix) (B.length prefix + B.length suffix)));
  assert (B.length prefix + B.length suffix == B.length full);
  assert (Seq.equal suffix (Seq.slice full (B.length prefix) (B.length full)))

let append_raw_sent (raw:raw_io_log) (bytes:B.bytes) : raw_io_log =
  { raw with raw_sent = B.append raw.raw_sent bytes }

let append_raw_received (raw:raw_io_log) (bytes:B.bytes) : raw_io_log =
  { raw with raw_received = B.append raw.raw_received bytes }

let append_raw_sent_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat) : raw_io_log =
  append_raw_sent raw (raw_slice bytes lo hi)

let append_raw_received_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat) : raw_io_log =
  append_raw_received raw (raw_slice bytes lo hi)

let lemma_raw_io_log_extends_refl (raw:raw_io_log)
  : Lemma (raw_io_log_extends raw raw)
  =
  lemma_bytes_extends_refl raw.raw_sent;
  lemma_bytes_extends_refl raw.raw_received

let lemma_raw_io_log_extends_sent (raw:raw_io_log) (bytes:B.bytes)
  : Lemma (raw_io_log_extends raw (append_raw_sent raw bytes))
  =
  lemma_bytes_extends_append raw.raw_sent bytes;
  lemma_bytes_extends_refl raw.raw_received

let lemma_raw_io_log_extends_received (raw:raw_io_log) (bytes:B.bytes)
  : Lemma (raw_io_log_extends raw (append_raw_received raw bytes))
  =
  lemma_bytes_extends_refl raw.raw_sent;
  lemma_bytes_extends_append raw.raw_received bytes

let lemma_raw_io_log_extends_sent_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat)
  : Lemma (raw_io_log_extends raw (append_raw_sent_slice raw bytes lo hi))
  =
  lemma_raw_io_log_extends_sent raw (raw_slice bytes lo hi)

let lemma_raw_io_log_extends_received_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat)
  : Lemma (raw_io_log_extends raw (append_raw_received_slice raw bytes lo hi))
  =
  lemma_raw_io_log_extends_received raw (raw_slice bytes lo hi)

let lemma_raw_io_log_same_received_sent_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat)
  : Lemma (raw_io_log_same_received raw (append_raw_sent_slice raw bytes lo hi))
  =
  ()

let lemma_raw_io_log_same_sent_received_slice (raw:raw_io_log) (bytes:B.bytes) (lo:nat) (hi:nat)
  : Lemma (raw_io_log_same_sent raw (append_raw_received_slice raw bytes lo hi))
  =
  ()

let lemma_bytes_extends_trans (old:B.bytes) (mid:B.bytes) (next:B.bytes)
  : Lemma
      (requires bytes_extends old mid /\ bytes_extends mid next)
      (ensures bytes_extends old next)
  =
  Seq.lemma_len_slice next 0 (B.length old);
  Seq.lemma_eq_elim old (Seq.slice mid 0 (B.length old));
  Seq.lemma_eq_elim mid (Seq.slice next 0 (B.length mid));
  assert (forall (i:nat{i < B.length old}).
            Seq.index old i == Seq.index (Seq.slice next 0 (B.length old)) i);
  Seq.lemma_eq_intro old (Seq.slice next 0 (B.length old))

let lemma_raw_io_log_extends_trans (old:raw_io_log) (mid:raw_io_log) (next:raw_io_log)
  : Lemma
      (requires raw_io_log_extends old mid /\ raw_io_log_extends mid next)
      (ensures raw_io_log_extends old next)
  =
  lemma_bytes_extends_trans old.raw_sent mid.raw_sent next.raw_sent;
  lemma_bytes_extends_trans old.raw_received mid.raw_received next.raw_received

let lemma_raw_io_log_same_sent_trans (old:raw_io_log) (mid:raw_io_log) (next:raw_io_log)
  : Lemma
      (requires raw_io_log_same_sent old mid /\ raw_io_log_same_sent mid next)
      (ensures raw_io_log_same_sent old next)
  =
  ()

let lemma_raw_io_log_same_received_trans (old:raw_io_log) (mid:raw_io_log) (next:raw_io_log)
  : Lemma
      (requires raw_io_log_same_received old mid /\ raw_io_log_same_received mid next)
      (ensures raw_io_log_same_received old next)
  =
  ()

type stream_view (a:Type0) = {
  values: list a;
  consumed: nat;
  residual: B.bytes;
}

let stream_view_shape (#a:Type0) (raw:B.bytes) (view:stream_view a) : prop =
  view.consumed <= B.length raw /\
  Seq.equal view.residual (Seq.slice raw view.consumed (B.length raw))

type tls_message =
  | TlsHandshake of H.handshake_msg
  | TlsApplicationData of B.bytes
  | TlsAlert of T.alert_description
  | TlsChangeCipherSpec

type tls_record = {
  record_outer_type: T.content_type;
  record_fragment: R.sealed_record;
}

let serialize_tls_record (record:tls_record) : GTot B.bytes =
  W.serialize_record record.record_outer_type record.record_fragment

let rec serialize_tls_records (records:list tls_record)
  : GTot B.bytes
        (decreases records)
  =
  match records with
  | [] -> B.empty
  | record :: rest -> B.append (serialize_tls_record record) (serialize_tls_records rest)

let record_stream_serializes
  (raw:B.bytes)
  (view:stream_view tls_record)
  : prop =
  view.consumed <= B.length raw /\
  view.consumed == B.length (serialize_tls_records view.values) /\
  Seq.equal (serialize_tls_records view.values) (Seq.slice raw 0 view.consumed) /\
  stream_view_shape raw view

let raw_record_stream_shapes
  (raw:raw_io_log)
  (sent:stream_view tls_record)
  (received:stream_view tls_record)
  : prop =
  record_stream_serializes raw.raw_sent sent /\
  record_stream_serializes raw.raw_received received

let empty_stream_view (#a:Type0) : stream_view a =
  { values = []; consumed = 0; residual = B.empty }

let raw_stream_view (#a:Type0) (raw:B.bytes) (values:list a) : stream_view a =
  { values = values; consumed = 0; residual = raw }

let lemma_raw_stream_view_shape (#a:Type0) (raw:B.bytes) (values:list a)
  : Lemma (stream_view_shape raw (raw_stream_view raw values))
  =
  lemma_bytes_extends_refl raw

let raw_record_stream_view (raw:B.bytes) : stream_view tls_record =
  raw_stream_view raw []

let lemma_raw_record_stream_view_shape (raw:B.bytes)
  : Lemma (stream_view_shape raw (raw_record_stream_view raw))
  =
  lemma_raw_stream_view_shape #tls_record raw []

let lemma_empty_serialized_records_slice (raw:B.bytes)
  : Lemma (Seq.equal (serialize_tls_records []) (Seq.slice raw 0 0))
  =
  Seq.lemma_len_slice raw 0 0;
  assert (B.length (serialize_tls_records []) == 0);
  assert (B.length (Seq.slice raw 0 0) == 0);
  assert (forall (i:nat{i < B.length (serialize_tls_records [])}).
            Seq.index (serialize_tls_records []) i == Seq.index (Seq.slice raw 0 0) i);
  Seq.lemma_eq_intro (serialize_tls_records []) (Seq.slice raw 0 0)

let lemma_record_stream_serializes_raw_view (raw:B.bytes)
  : Lemma (record_stream_serializes raw (raw_record_stream_view raw))
  =
  lemma_empty_serialized_records_slice raw;
  lemma_raw_stream_view_shape #tls_record raw []

let rec parse_record_prefix_fuel
  (fuel:nat)
  (input:B.bytes)
  : GTot (stream_view tls_record)
        (decreases fuel)
  =
  if fuel == 0 then raw_record_stream_view input
  else
    match W.parse_record input with
    | Some (content_type, fragment, consumed) ->
      if consumed == 0 || consumed > B.length input then raw_record_stream_view input
      else
        let rest = Seq.slice input consumed (B.length input) in
        let tail = parse_record_prefix_fuel (fuel - 1) rest in
        {
          values =
            { record_outer_type = content_type; record_fragment = fragment } ::
            tail.values;
          consumed = consumed + tail.consumed;
          residual = tail.residual;
        }
    | None -> raw_record_stream_view input

let parse_record_prefix (input:B.bytes) : GTot (stream_view tls_record) =
  parse_record_prefix_fuel (B.length input + 1) input

let rec lemma_parse_record_prefix_fuel_shape
  (fuel:nat)
  (input:B.bytes)
  : Lemma (ensures stream_view_shape input (parse_record_prefix_fuel fuel input))
          (decreases fuel)
  =
  if fuel == 0 then lemma_raw_record_stream_view_shape input
  else
    match W.parse_record input with
    | Some (_, _, consumed) ->
      if consumed == 0 || consumed > B.length input then
        lemma_raw_record_stream_view_shape input
      else
        let rest = Seq.slice input consumed (B.length input) in
        let tail = parse_record_prefix_fuel (fuel - 1) rest in
        lemma_parse_record_prefix_fuel_shape (fuel - 1) rest;
        Seq.lemma_len_slice input consumed (B.length input);
        assert (stream_view_shape rest tail);
        assert (tail.consumed <= B.length rest);
        assert (consumed + tail.consumed <= B.length input);
        Seq.lemma_eq_elim tail.residual (Seq.slice rest tail.consumed (B.length rest));
        SP.slice_slice input consumed (B.length input) tail.consumed (B.length rest);
        assert (consumed + B.length rest == B.length input);
        assert (tail.residual == Seq.slice input (consumed + tail.consumed) (B.length input));
        Seq.lemma_eq_refl tail.residual (Seq.slice input (consumed + tail.consumed) (B.length input))
    | None -> lemma_raw_record_stream_view_shape input

let lemma_parse_record_prefix_shape (input:B.bytes)
  : Lemma (stream_view_shape input (parse_record_prefix input))
  =
  lemma_parse_record_prefix_fuel_shape (B.length input + 1) input

let rec lemma_parse_record_prefix_fuel_serializes
  (fuel:nat)
  (input:B.bytes)
  : Lemma (ensures record_stream_serializes input (parse_record_prefix_fuel fuel input))
          (decreases fuel)
  =
  if fuel == 0 then lemma_record_stream_serializes_raw_view input
  else
    match W.parse_record input with
    | Some (content_type, fragment, consumed) ->
      if consumed == 0 || consumed > B.length input then
        lemma_record_stream_serializes_raw_view input
      else
        let rest = Seq.slice input consumed (B.length input) in
        let tail = parse_record_prefix_fuel (fuel - 1) rest in
        let record = { record_outer_type = content_type; record_fragment = fragment } in
        W.lemma_parse_record_serializes input;
        lemma_parse_record_prefix_fuel_serializes (fuel - 1) rest;
        Seq.lemma_len_slice input consumed (B.length input);
        assert (record_stream_serializes rest tail);
        assert (consumed == B.length (serialize_tls_record record));
        assert (tail.consumed == B.length (serialize_tls_records tail.values));
        assert (consumed + tail.consumed ==
                B.length (serialize_tls_records (record :: tail.values)));
        Seq.lemma_eq_elim (serialize_tls_record record) (Seq.slice input 0 consumed);
        Seq.lemma_eq_elim (serialize_tls_records tail.values) (Seq.slice rest 0 tail.consumed);
        SP.slice_slice input consumed (B.length input) 0 tail.consumed;
        assert (Seq.equal (serialize_tls_records tail.values)
                          (Seq.slice input consumed (consumed + tail.consumed)));
        Seq.lemma_split (Seq.slice input 0 (consumed + tail.consumed)) consumed;
        assert (Seq.equal (serialize_tls_records (record :: tail.values))
                          (Seq.slice input 0 (consumed + tail.consumed)));
        lemma_parse_record_prefix_fuel_shape fuel input
    | None -> lemma_record_stream_serializes_raw_view input

let lemma_parse_record_prefix_serializes (input:B.bytes)
  : Lemma (record_stream_serializes input (parse_record_prefix input))
  =
  lemma_parse_record_prefix_fuel_serializes (B.length input + 1) input

let record_prefix_parser_relation
  (raw:B.bytes)
  (view:stream_view tls_record)
  : prop =
  view == parse_record_prefix raw /\
  record_stream_serializes raw view

let raw_record_prefix_parsed
  (raw:raw_io_log)
  (sent:stream_view tls_record)
  (received:stream_view tls_record)
  : prop =
  record_prefix_parser_relation raw.raw_sent sent /\
  record_prefix_parser_relation raw.raw_received received

type directed_message (a:Type0) = {
  message_direction: direction;
  message_value: a;
}

type local_event =
  | LocalValidateCertificate of X.peer_identity
  | LocalFail of T.tls_error
  | LocalDeliverApplicationData of B.bytes

type host_event =
  | NetworkEvent of directed_message tls_message
  | LocalEvent of local_event

type app_log = {
  app_sent: list B.bytes;
  app_received: list B.bytes;
}

type client_operation =
  | OpStart of server_name:T.hostname
  | OpSendApplicationData of plaintext:B.bytes
  | OpReadApplicationData of max_len:nat
  | OpClose

type client_request = {
  operation: client_operation;
  network_in: B.bytes;
}

type client_status =
  | NeedNetworkInput
  | HandshakeComplete
  | ActionComplete
  | ApplicationDataReady
  | Closed
  | Failed of error:T.tls_error

type client_response = {
  network_out: B.bytes;
  app_out: B.bytes;
  // One entry per received-application-data or local-delivery host event
  // represented by this response, in order. app_out is their concatenation.
  app_received_delta: list B.bytes;
  status: client_status;
}

let empty_app_log : app_log =
  { app_sent = []; app_received = [] }

let append_app_sent (app:app_log) (bytes:B.bytes) : app_log =
  { app with app_sent = app.app_sent @ [bytes] }

let append_app_received (app:app_log) (bytes:B.bytes) : app_log =
  { app with app_received = app.app_received @ [bytes] }

let rec concat_bytes (chunks:list B.bytes) : Tot B.bytes (decreases chunks) =
  match chunks with
  | [] -> B.empty
  | chunk :: rest -> B.append chunk (concat_bytes rest)

let rec chunk_count (chunks:list B.bytes) : Tot nat (decreases chunks) =
  match chunks with
  | [] -> 0
  | _ :: rest -> 1 + chunk_count rest

let app_log_extends (old:app_log) (next:app_log) : prop =
  exists sent_delta received_delta.
    next.app_sent == old.app_sent @ sent_delta /\
    next.app_received == old.app_received @ received_delta

let lemma_app_log_extends_refl (app:app_log)
  : Lemma (app_log_extends app app)
  =
  L.append_l_nil app.app_sent;
  L.append_l_nil app.app_received;
  assert (app.app_sent == app.app_sent @ []);
  assert (app.app_received == app.app_received @ []);
  assert (exists sent_delta received_delta.
            app.app_sent == app.app_sent @ sent_delta /\
            app.app_received == app.app_received @ received_delta)

let lemma_app_log_extends_sent (app:app_log) (bytes:B.bytes)
  : Lemma (app_log_extends app (append_app_sent app bytes))
  =
  L.append_l_nil app.app_received;
  assert ((append_app_sent app bytes).app_sent == app.app_sent @ [bytes]);
  assert ((append_app_sent app bytes).app_received == app.app_received @ []);
  assert (exists sent_delta received_delta.
            (append_app_sent app bytes).app_sent == app.app_sent @ sent_delta /\
            (append_app_sent app bytes).app_received == app.app_received @ received_delta)

let lemma_app_log_extends_received (app:app_log) (bytes:B.bytes)
  : Lemma (app_log_extends app (append_app_received app bytes))
  =
  L.append_l_nil app.app_sent;
  assert ((append_app_received app bytes).app_sent == app.app_sent @ []);
  assert ((append_app_received app bytes).app_received == app.app_received @ [bytes]);
  assert (exists sent_delta received_delta.
            (append_app_received app bytes).app_sent == app.app_sent @ sent_delta /\
            (append_app_received app bytes).app_received == app.app_received @ received_delta)

let request_network_in (req:client_request) : B.bytes =
  req.network_in

let request_app_in (req:client_request) : B.bytes =
  match req.operation with
  | OpSendApplicationData plaintext -> plaintext
  | _ -> B.empty

let request_read_len (req:client_request) : nat =
  match req.operation with
  | OpReadApplicationData max_len -> max_len
  | _ -> 0

let response_shape (resp:client_response) : prop =
  Seq.equal resp.app_out (concat_bytes resp.app_received_delta)

let status_matches_phase (status:client_status) (phase:S.phase) : prop =
  match status with
  | NeedNetworkInput -> phase <> S.Closed /\ phase <> S.Failed
  | HandshakeComplete -> phase == S.ApplicationData
  | ActionComplete -> phase == S.ApplicationData
  | ApplicationDataReady -> phase == S.ApplicationData
  | Closed -> phase == S.Closing \/ phase == S.Closed
  | Failed _ -> phase == S.Failed

let step_raw_log
  (raw:raw_io_log)
  (req:client_request)
  (resp:client_response)
  : raw_io_log =
  {
    raw_sent = B.append raw.raw_sent resp.network_out;
    raw_received = B.append raw.raw_received (request_network_in req);
  }

let step_app_sent_delta (req:client_request) (resp:client_response) : list B.bytes =
  match req.operation, resp.status with
  | OpSendApplicationData plaintext, Failed _ -> []
  | OpSendApplicationData plaintext, _ -> [plaintext]
  | _, _ -> []

let step_app_received_delta (resp:client_response) : list B.bytes =
  resp.app_received_delta

let step_app_log (app:app_log) (req:client_request) (resp:client_response) : app_log =
  {
    app_sent = app.app_sent @ step_app_sent_delta req resp;
    app_received = app.app_received @ step_app_received_delta resp;
  }

let bytes_delta (old:B.bytes) (next:B.bytes) : B.bytes =
  if B.length old <= B.length next
  then Seq.slice next (B.length old) (B.length next)
  else B.empty

let raw_sent_delta (old:raw_io_log) (next:raw_io_log) : B.bytes =
  bytes_delta old.raw_sent next.raw_sent

let raw_received_delta (old:raw_io_log) (next:raw_io_log) : B.bytes =
  bytes_delta old.raw_received next.raw_received

let lemma_bytes_delta_refl (bytes:B.bytes)
  : Lemma (bytes_delta bytes bytes == B.empty)
  =
  Seq.lemma_len_slice bytes (B.length bytes) (B.length bytes);
  assert (B.length (Seq.slice bytes (B.length bytes) (B.length bytes)) == 0);
  assert (forall (i:nat{i < B.length B.empty}).
            Seq.index (Seq.slice bytes (B.length bytes) (B.length bytes)) i ==
            Seq.index B.empty i);
  Seq.lemma_eq_intro (Seq.slice bytes (B.length bytes) (B.length bytes)) B.empty

let lemma_raw_sent_delta_refl (raw:raw_io_log)
  : Lemma (raw_sent_delta raw raw == B.empty)
  =
  lemma_bytes_delta_refl raw.raw_sent

let lemma_raw_received_delta_refl (raw:raw_io_log)
  : Lemma (raw_received_delta raw raw == B.empty)
  =
  lemma_bytes_delta_refl raw.raw_received

let lemma_bytes_delta_append (old:B.bytes) (delta:B.bytes)
  : Lemma (bytes_delta old (B.append old delta) == delta)
  =
  let next = B.append old delta in
  let prefix = Seq.slice next 0 (B.length old) in
  let suffix = Seq.slice next (B.length old) (B.length next) in
  Seq.lemma_len_append old delta;
  Seq.lemma_len_slice next 0 (B.length old);
  Seq.lemma_len_slice next (B.length old) (B.length next);
  lemma_bytes_extends_append old delta;
  Seq.lemma_eq_elim old prefix;
  SP.lemma_split next (B.length old);
  assert (B.append prefix suffix == next);
  assert (B.append prefix suffix == B.append old delta);
  Seq.lemma_eq_refl (B.append prefix suffix) (B.append old delta);
  SP.lemma_append_inj prefix suffix old delta;
  Seq.lemma_eq_elim suffix delta;
  assert (bytes_delta old next == suffix);
  assert (bytes_delta old next == delta)

let lemma_raw_sent_delta_append (raw:raw_io_log) (delta:B.bytes)
  : Lemma (raw_sent_delta raw (append_raw_sent raw delta) == delta)
  =
  lemma_bytes_delta_append raw.raw_sent delta

let lemma_raw_received_delta_append (raw:raw_io_log) (delta:B.bytes)
  : Lemma (raw_received_delta raw (append_raw_received raw delta) == delta)
  =
  lemma_bytes_delta_append raw.raw_received delta

let lemma_raw_sent_delta_append_slice
  (raw:raw_io_log)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat)
  : Lemma (raw_sent_delta raw (append_raw_sent_slice raw bytes lo hi) == raw_slice bytes lo hi)
  =
  lemma_raw_sent_delta_append raw (raw_slice bytes lo hi)

let lemma_raw_received_delta_append_slice
  (raw:raw_io_log)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat)
  : Lemma (raw_received_delta raw (append_raw_received_slice raw bytes lo hi) == raw_slice bytes lo hi)
  =
  lemma_raw_received_delta_append raw (raw_slice bytes lo hi)

let request_with_network_in (op:client_operation) (network_in:B.bytes) : client_request =
  { operation = op; network_in = network_in }

let request_no_network_in (op:client_operation) : client_request =
  request_with_network_in op B.empty

let request_with_received_raw_delta (op:client_operation) (old:raw_io_log) (next:raw_io_log)
  : client_request =
  request_with_network_in op (raw_received_delta old next)

let response_with_sent_raw_delta
  (old:raw_io_log)
  (next:raw_io_log)
  (app_out:B.bytes)
  (status:client_status)
  : client_response =
  {
    network_out = raw_sent_delta old next;
    app_out = app_out;
    app_received_delta =
      (match status with
       | ApplicationDataReady -> [app_out]
       | _ -> []);
    status = status;
  }

let response_no_network_out (app_out:B.bytes) (status:client_status) : client_response =
  {
    network_out = B.empty;
    app_out = app_out;
    app_received_delta =
      (match status with
       | ApplicationDataReady -> [app_out]
       | _ -> []);
    status = status
  }

let response_no_network_out_chunks
  (app_out:B.bytes)
  (chunks:list B.bytes)
  (status:client_status)
  : client_response =
  {
    network_out = B.empty;
    app_out = app_out;
    app_received_delta = chunks;
    status = status
  }

let lemma_append_empty_right (bytes:B.bytes)
  : Lemma (B.append bytes B.empty == bytes)
  =
  Seq.lemma_empty B.empty;
  Seq.append_empty_r bytes

let lemma_append_empty_left (bytes:B.bytes)
  : Lemma (B.append B.empty bytes == bytes)
  =
  Seq.lemma_empty B.empty;
  Seq.append_empty_l bytes

let lemma_concat_bytes_nil ()
  : Lemma (concat_bytes [] == B.empty)
  =
  ()

let lemma_concat_bytes_singleton (bytes:B.bytes)
  : Lemma (Seq.equal bytes (concat_bytes [bytes]))
  =
  lemma_append_empty_right bytes;
  assert (concat_bytes [bytes] == bytes);
  Seq.lemma_eq_refl bytes (concat_bytes [bytes])

let lemma_concat_bytes_pair (bytes1 bytes2:B.bytes)
  : Lemma (Seq.equal (B.append bytes1 bytes2) (concat_bytes [bytes1; bytes2]))
  =
  lemma_append_empty_right bytes2;
  assert (concat_bytes [bytes1; bytes2] == B.append bytes1 (B.append bytes2 B.empty));
  assert (B.append bytes2 B.empty == bytes2);
  assert (concat_bytes [bytes1; bytes2] == B.append bytes1 bytes2);
  Seq.lemma_eq_refl (B.append bytes1 bytes2) (concat_bytes [bytes1; bytes2])

let rec lemma_concat_bytes_append
  (left:list B.bytes)
  (right:list B.bytes)
  : Lemma
      (ensures B.append (concat_bytes left) (concat_bytes right) == concat_bytes (left @ right))
      (decreases left)
  =
  match left with
  | [] ->
    lemma_append_empty_left (concat_bytes right);
    assert ([] @ right == right)
  | bytes :: rest ->
    lemma_concat_bytes_append rest right;
    Seq.append_assoc bytes (concat_bytes rest) (concat_bytes right);
    assert (B.append (concat_bytes rest) (concat_bytes right) == concat_bytes (rest @ right));
    assert ((bytes :: rest) @ right == bytes :: (rest @ right))

let lemma_concat_bytes_snoc
  (chunks:list B.bytes)
  (bytes:B.bytes)
  : Lemma (B.append (concat_bytes chunks) bytes == concat_bytes (chunks @ [bytes]))
  =
  lemma_concat_bytes_append chunks [bytes];
  lemma_concat_bytes_singleton bytes;
  Seq.lemma_eq_elim bytes (concat_bytes [bytes])

let lemma_concat_bytes_snoc_equal
  (chunks:list B.bytes)
  (bytes:B.bytes)
  (prefix:B.bytes)
  : Lemma
      (requires Seq.equal prefix (concat_bytes chunks))
      (ensures Seq.equal (B.append prefix bytes) (concat_bytes (chunks @ [bytes])))
  =
  lemma_concat_bytes_snoc chunks bytes;
  Seq.lemma_eq_elim prefix (concat_bytes chunks);
  Seq.lemma_eq_refl
    (B.append prefix bytes)
    (concat_bytes (chunks @ [bytes]))

let rec lemma_chunk_count_append
  (left:list B.bytes)
  (right:list B.bytes)
  : Lemma
      (ensures chunk_count (left @ right) == chunk_count left + chunk_count right)
      (decreases left)
  =
  match left with
  | [] -> ()
  | bytes :: rest ->
    lemma_chunk_count_append rest right;
    assert (left @ right == bytes :: (rest @ right));
    assert (chunk_count (left @ right) == 1 + chunk_count (rest @ right))

let lemma_chunk_count_snoc
  (chunks:list B.bytes)
  (bytes:B.bytes)
  : Lemma (chunk_count (chunks @ [bytes]) == chunk_count chunks + 1)
  =
  lemma_chunk_count_append chunks [bytes]

let lemma_response_with_sent_raw_delta_shape
  (old:raw_io_log)
  (next:raw_io_log)
  (app_out:B.bytes)
  (status:client_status)
  : Lemma
      (requires status == ApplicationDataReady \/ Seq.equal app_out B.empty)
      (ensures response_shape (response_with_sent_raw_delta old next app_out status))
  =
  match status with
  | ApplicationDataReady -> lemma_concat_bytes_singleton app_out
  | _ -> ()

let lemma_response_no_network_out_shape
  (app_out:B.bytes)
  (status:client_status)
  : Lemma
      (requires status == ApplicationDataReady \/ Seq.equal app_out B.empty)
      (ensures response_shape (response_no_network_out app_out status))
  =
  match status with
  | ApplicationDataReady -> lemma_concat_bytes_singleton app_out
  | _ -> ()

let lemma_response_no_network_out_chunks_shape
  (app_out:B.bytes)
  (chunks:list B.bytes)
  (status:client_status)
  : Lemma
      (requires Seq.equal app_out (concat_bytes chunks))
      (ensures response_shape (response_no_network_out_chunks app_out chunks status))
  =
  ()

let lemma_bytes_extends_append_delta (old:B.bytes) (next:B.bytes)
  : Lemma
      (requires bytes_extends old next)
      (ensures B.append old (bytes_delta old next) == next)
  =
  assert (B.length old <= B.length next);
  assert (bytes_delta old next == Seq.slice next (B.length old) (B.length next));
  Seq.lemma_eq_elim old (Seq.slice next 0 (B.length old));
  SP.lemma_split next (B.length old);
  assert (B.append (Seq.slice next 0 (B.length old)) (bytes_delta old next) == next);
  assert (B.append old (bytes_delta old next) == next)

let lemma_step_raw_log_sent_delta
  (old:raw_io_log)
  (next:raw_io_log)
  (op:client_operation)
  (app_out:B.bytes)
  (status:client_status)
  : Lemma
      (requires raw_io_log_extends old next /\
                raw_io_log_same_received old next)
      (ensures next == step_raw_log old (request_no_network_in op)
                   (response_with_sent_raw_delta old next app_out status))
  =
  lemma_bytes_extends_append_delta old.raw_sent next.raw_sent;
  lemma_append_empty_right old.raw_received;
  assert (B.append old.raw_received B.empty == old.raw_received);
  assert (old.raw_received == next.raw_received)

let lemma_step_raw_log_received_delta
  (old:raw_io_log)
  (next:raw_io_log)
  (op:client_operation)
  (app_out:B.bytes)
  (status:client_status)
  : Lemma
      (requires raw_io_log_extends old next /\
                raw_io_log_same_sent old next)
      (ensures next == step_raw_log old (request_with_network_in op (raw_received_delta old next))
                   (response_no_network_out app_out status))
  =
  lemma_bytes_extends_append_delta old.raw_received next.raw_received;
  lemma_append_empty_right old.raw_sent;
  assert (B.append old.raw_sent B.empty == old.raw_sent);
  assert (old.raw_sent == next.raw_sent)

let lemma_step_raw_log_received_delta_chunks
  (old:raw_io_log)
  (next:raw_io_log)
  (op:client_operation)
  (app_out:B.bytes)
  (chunks:list B.bytes)
  (status:client_status)
  : Lemma
      (requires raw_io_log_extends old next /\
                raw_io_log_same_sent old next)
      (ensures next == step_raw_log old (request_with_network_in op (raw_received_delta old next))
                   (response_no_network_out_chunks app_out chunks status))
  =
  lemma_bytes_extends_append_delta old.raw_received next.raw_received;
  lemma_append_empty_right old.raw_sent;
  assert (B.append old.raw_sent B.empty == old.raw_sent);
  assert (old.raw_sent == next.raw_sent)

let lemma_step_raw_log_extends
  (raw:raw_io_log)
  (req:client_request)
  (resp:client_response)
  : Lemma (raw_io_log_extends raw (step_raw_log raw req resp))
  =
  lemma_bytes_extends_append raw.raw_sent resp.network_out;
  lemma_bytes_extends_append raw.raw_received (request_network_in req)

let lemma_step_app_log_extends
  (app:app_log)
  (req:client_request)
  (resp:client_response)
  : Lemma (app_log_extends app (step_app_log app req resp))
  =
  let sent_delta = step_app_sent_delta req resp in
  let received_delta = step_app_received_delta resp in
  assert ((step_app_log app req resp).app_sent == app.app_sent @ sent_delta);
  assert ((step_app_log app req resp).app_received == app.app_received @ received_delta);
  assert (exists sent_delta received_delta.
            (step_app_log app req resp).app_sent == app.app_sent @ sent_delta /\
            (step_app_log app req resp).app_received == app.app_received @ received_delta)

let state_event_of_tls_message (msg:directed_message tls_message) : GTot (option S.event) =
  match msg.message_direction, msg.message_value with
  | Sent, TlsHandshake (H.ClientHello ch) -> Some (S.SendClientHello ch)
  | Received, TlsHandshake (H.ServerHello sh) -> Some (S.RecvServerHello sh)
  | Received, TlsHandshake (H.EncryptedExtensions ee) -> Some (S.RecvEncryptedExtensions ee)
  | Received, TlsHandshake (H.Certificate cert) -> Some (S.RecvCertificate cert)
  | Received, TlsHandshake (H.CertificateVerify cv) -> Some (S.RecvCertificateVerify cv)
  | Received, TlsHandshake (H.Finished fin) -> Some (S.RecvServerFinished fin)
  | Sent, TlsHandshake (H.Finished fin) -> Some (S.SendClientFinished fin)
  | Sent, TlsApplicationData bytes -> Some (S.SendApplicationData bytes)
  | Received, TlsApplicationData bytes -> Some (S.RecvApplicationData bytes)
  | Sent, TlsAlert T.CloseNotify -> Some S.SendCloseNotify
  | Received, TlsAlert T.CloseNotify -> Some S.RecvCloseNotify
  | _, TlsAlert alert -> Some (S.Fail (T.AlertError alert))
  | _, TlsChangeCipherSpec -> None
  | _, _ -> None

let state_event_of_local_event (ev:local_event) : GTot (option S.event) =
  match ev with
  | LocalValidateCertificate peer -> Some (S.ValidateCertificate peer)
  | LocalFail err -> Some (S.Fail err)
  | LocalDeliverApplicationData _ -> None

let state_event_of_host_event (ev:host_event) : GTot (option S.event) =
  match ev with
  | NetworkEvent msg -> state_event_of_tls_message msg
  | LocalEvent local -> state_event_of_local_event local

let sent_tls_delta_of_host_event (ev:host_event) : list tls_message =
  match ev with
  | NetworkEvent msg ->
    (match msg.message_direction with
     | Sent -> [msg.message_value]
     | Received -> [])
  | LocalEvent _ -> []

let received_tls_delta_of_host_event (ev:host_event) : list tls_message =
  match ev with
  | NetworkEvent msg ->
    (match msg.message_direction with
     | Received -> [msg.message_value]
     | Sent -> [])
  | LocalEvent _ -> []

let app_sent_delta_of_host_event (ev:host_event) : list B.bytes =
  match ev with
  | NetworkEvent msg ->
    (match msg.message_direction, msg.message_value with
     | Sent, TlsApplicationData bytes -> [bytes]
     | _, _ -> [])
  | LocalEvent _ -> []

let app_received_delta_of_host_event (ev:host_event) : list B.bytes =
  match ev with
  | NetworkEvent msg ->
    (match msg.message_direction, msg.message_value with
     | Received, TlsApplicationData bytes -> [bytes]
     | _, _ -> [])
  | LocalEvent local ->
    (match local with
     | LocalDeliverApplicationData bytes -> [bytes]
     | _ -> [])

let app_log_snoc_event (app:app_log) (ev:host_event) : app_log =
  {
    app_sent = app.app_sent @ app_sent_delta_of_host_event ev;
    app_received = app.app_received @ app_received_delta_of_host_event ev;
  }

let state_event_delta_of_host_event (ev:host_event) : GTot (list S.event) =
  match state_event_of_host_event ev with
  | Some state_ev -> [state_ev]
  | None -> []

let rec state_events_of_host_trace (trace:list host_event)
  : GTot (list S.event)
        (decreases trace)
  =
  match trace with
  | [] -> []
  | ev :: rest ->
    (match state_event_of_host_event ev with
     | Some state_ev -> state_ev :: state_events_of_host_trace rest
     | None -> state_events_of_host_trace rest)

let rec sent_tls_of_host_trace (trace:list host_event)
  : GTot (list tls_message)
        (decreases trace)
  =
  match trace with
  | [] -> []
  | ev :: rest ->
    (match ev with
     | NetworkEvent msg ->
       (match msg.message_direction with
        | Sent -> msg.message_value :: sent_tls_of_host_trace rest
        | Received -> sent_tls_of_host_trace rest)
     | LocalEvent _ -> sent_tls_of_host_trace rest)

let rec received_tls_of_host_trace (trace:list host_event)
  : GTot (list tls_message)
        (decreases trace)
  =
  match trace with
  | [] -> []
  | ev :: rest ->
    (match ev with
     | NetworkEvent msg ->
       (match msg.message_direction with
        | Received -> msg.message_value :: received_tls_of_host_trace rest
        | Sent -> received_tls_of_host_trace rest)
     | LocalEvent _ -> received_tls_of_host_trace rest)

let rec app_sent_of_host_trace (trace:list host_event)
  : GTot (list B.bytes)
        (decreases trace)
  =
  match trace with
  | [] -> []
  | ev :: rest ->
    (match ev with
     | NetworkEvent msg ->
       (match msg.message_direction, msg.message_value with
        | Sent, TlsApplicationData bytes -> bytes :: app_sent_of_host_trace rest
        | _, _ -> app_sent_of_host_trace rest)
     | LocalEvent _ -> app_sent_of_host_trace rest)

let rec app_received_of_host_trace (trace:list host_event)
  : GTot (list B.bytes)
        (decreases trace)
  =
  match trace with
  | [] -> []
  | ev :: rest ->
    (match ev with
     | NetworkEvent msg ->
       (match msg.message_direction, msg.message_value with
        | Received, TlsApplicationData bytes -> bytes :: app_received_of_host_trace rest
        | _, _ -> app_received_of_host_trace rest)
     | LocalEvent local ->
       (match local with
        | LocalDeliverApplicationData bytes -> bytes :: app_received_of_host_trace rest
        | _ -> app_received_of_host_trace rest))

let app_log_of_host_trace (trace:list host_event) : GTot app_log =
  {
    app_sent = app_sent_of_host_trace trace;
    app_received = app_received_of_host_trace trace;
  }

let sent_app_event (bytes:B.bytes) : host_event =
  NetworkEvent { message_direction = Sent; message_value = TlsApplicationData bytes }

let received_app_event (bytes:B.bytes) : host_event =
  NetworkEvent { message_direction = Received; message_value = TlsApplicationData bytes }

let sent_close_notify_event : host_event =
  NetworkEvent { message_direction = Sent; message_value = TlsAlert T.CloseNotify }

let received_close_notify_event : host_event =
  NetworkEvent { message_direction = Received; message_value = TlsAlert T.CloseNotify }

let local_fail_event (err:T.tls_error) : host_event =
  LocalEvent (LocalFail err)

let local_app_received_event (bytes:B.bytes) : host_event =
  LocalEvent (LocalDeliverApplicationData bytes)

let rec lemma_sent_tls_of_host_trace_snoc (trace:list host_event) (ev:host_event)
  : Lemma
      (ensures sent_tls_of_host_trace (trace @ [ev]) ==
               sent_tls_of_host_trace trace @ sent_tls_delta_of_host_event ev)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_sent_tls_of_host_trace_snoc rest ev

let rec lemma_received_tls_of_host_trace_snoc (trace:list host_event) (ev:host_event)
  : Lemma
      (ensures received_tls_of_host_trace (trace @ [ev]) ==
               received_tls_of_host_trace trace @ received_tls_delta_of_host_event ev)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_received_tls_of_host_trace_snoc rest ev

let rec lemma_state_events_of_host_trace_snoc (trace:list host_event) (ev:host_event)
  : Lemma
      (ensures state_events_of_host_trace (trace @ [ev]) ==
               state_events_of_host_trace trace @ state_event_delta_of_host_event ev)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_state_events_of_host_trace_snoc rest ev

let rec lemma_app_sent_of_host_trace_snoc (trace:list host_event) (ev:host_event)
  : Lemma
      (ensures app_sent_of_host_trace (trace @ [ev]) ==
               app_sent_of_host_trace trace @ app_sent_delta_of_host_event ev)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_app_sent_of_host_trace_snoc rest ev

let rec lemma_app_received_of_host_trace_snoc (trace:list host_event) (ev:host_event)
  : Lemma
      (ensures app_received_of_host_trace (trace @ [ev]) ==
               app_received_of_host_trace trace @ app_received_delta_of_host_event ev)
          (decreases trace)
  =
  match trace with
  | [] ->
    (match ev with
     | NetworkEvent msg ->
       (match msg.message_direction, msg.message_value with
        | Received, TlsApplicationData _ -> ()
        | _, _ -> ())
     | LocalEvent local ->
       (match local with
        | LocalDeliverApplicationData _ -> ()
        | _ -> ()))
  | _ :: rest -> lemma_app_received_of_host_trace_snoc rest ev

let rec lemma_step_many_snoc
  (s0:S.conn_state)
  (events:list S.event)
  (ev:S.event)
  (s1:S.conn_state)
  (s2:S.conn_state)
  : Lemma
      (requires S.step_many s0 events == Some s1 /\
                S.step s1 ev == Some s2)
      (ensures S.step_many s0 (events @ [ev]) == Some s2)
      (decreases events)
  =
  match events with
  | [] -> ()
  | ev0 :: rest ->
    match S.step s0 ev0 with
    | Some mid -> lemma_step_many_snoc mid rest ev s1 s2
    | None -> assert False

let rec lemma_app_sent_snoc_sent (trace:list host_event) (bytes:B.bytes)
  : Lemma
      (ensures app_sent_of_host_trace (trace @ [sent_app_event bytes]) ==
               app_sent_of_host_trace trace @ [bytes])
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_app_sent_snoc_sent rest bytes

let rec lemma_app_received_snoc_sent (trace:list host_event) (bytes:B.bytes)
  : Lemma
      (ensures app_received_of_host_trace (trace @ [sent_app_event bytes]) ==
               app_received_of_host_trace trace)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_app_received_snoc_sent rest bytes

let rec lemma_app_sent_snoc_received (trace:list host_event) (bytes:B.bytes)
  : Lemma
      (ensures app_sent_of_host_trace (trace @ [received_app_event bytes]) ==
               app_sent_of_host_trace trace)
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_app_sent_snoc_received rest bytes

let rec lemma_app_received_snoc_received (trace:list host_event) (bytes:B.bytes)
  : Lemma
      (ensures app_received_of_host_trace (trace @ [received_app_event bytes]) ==
               app_received_of_host_trace trace @ [bytes])
          (decreases trace)
  =
  match trace with
  | [] -> ()
  | _ :: rest -> lemma_app_received_snoc_received rest bytes

type connection_view = {
  raw_log: raw_io_log;
  sent_records: stream_view tls_record;
  received_records: stream_view tls_record;
  sent_tls: stream_view tls_message;
  received_tls: stream_view tls_message;
  host_trace: list host_event;
  state: S.conn_state;
  app_view: app_log;
  pending_app: B.bytes;
  pending_app_record: B.bytes;
  pending_app_offset: nat;
  pending_received_raw: B.bytes;
}

let pending_app_source_consistent (view:connection_view) : prop =
  view.pending_app_offset <= B.length view.pending_app_record /\
  Seq.equal view.pending_app
    (raw_slice view.pending_app_record view.pending_app_offset (B.length view.pending_app_record))

let connection_view_app_projected (view:connection_view) : prop =
  app_log_of_host_trace view.host_trace == view.app_view

type raw_tls_relation =
  raw_io_log -> stream_view tls_message -> stream_view tls_message -> prop

let raw_tls_stream_shapes
  (raw:raw_io_log)
  (sent:stream_view tls_message)
  (received:stream_view tls_message)
  : prop =
  stream_view_shape raw.raw_sent sent /\
  stream_view_shape raw.raw_received received

let connection_view_consistent_with
  (raw_tls:raw_tls_relation)
  (view:connection_view)
  : prop =
  raw_tls view.raw_log view.sent_tls view.received_tls /\
  view.sent_tls.values == sent_tls_of_host_trace view.host_trace /\
  view.received_tls.values == received_tls_of_host_trace view.host_trace /\
  S.step_many S.initial (state_events_of_host_trace view.host_trace) == Some view.state /\
  app_log_of_host_trace view.host_trace == view.app_view

let connection_view_raw_stream_shaped (view:connection_view) : prop =
  raw_tls_stream_shapes view.raw_log view.sent_tls view.received_tls

let connection_view_record_stream_shaped (view:connection_view) : prop =
  raw_record_prefix_parsed view.raw_log view.sent_records view.received_records

let connection_view_shape (view:connection_view) : prop =
  connection_view_consistent_with raw_tls_stream_shapes view /\
  connection_view_record_stream_shaped view /\
  pending_app_source_consistent view

let connection_view_consistent (view:connection_view) : prop =
  connection_view_shape view

let view_with_raw_streams (view:connection_view) (raw:raw_io_log) : GTot connection_view =
  {
    view with
      raw_log = raw;
      sent_records = parse_record_prefix raw.raw_sent;
      received_records = parse_record_prefix raw.raw_received;
      sent_tls = raw_stream_view raw.raw_sent view.sent_tls.values;
      received_tls = raw_stream_view raw.raw_received view.received_tls.values;
  }

let note_host_event
  (view:connection_view)
  (ev:host_event)
  (state:S.conn_state)
  : connection_view =
  {
    view with
      sent_tls =
        raw_stream_view view.raw_log.raw_sent
          (view.sent_tls.values @ sent_tls_delta_of_host_event ev);
      received_tls =
        raw_stream_view view.raw_log.raw_received
          (view.received_tls.values @ received_tls_delta_of_host_event ev);
      host_trace = view.host_trace @ [ev];
      state = state;
      app_view = app_log_snoc_event view.app_view ev;
  }

let empty_connection_view : connection_view =
  {
    raw_log = empty_raw_io_log;
    sent_records = empty_stream_view;
    received_records = empty_stream_view;
    sent_tls = empty_stream_view;
    received_tls = empty_stream_view;
    host_trace = [];
    state = S.initial;
    app_view = empty_app_log;
    pending_app = B.empty;
    pending_app_record = B.empty;
    pending_app_offset = 0;
    pending_received_raw = B.empty;
  }

let public_connection_view
  (view:connection_view)
  (state:S.conn_state)
  (app:app_log)
  : prop =
  view.state == state /\ view.app_view == app

let public_connection_view_from_raw
  (view:connection_view)
  (raw:raw_io_log)
  (state:S.conn_state)
  (app:app_log)
  : prop =
  view.raw_log == raw /\ public_connection_view view state app

let connection_view_single_step (old:connection_view) (next:connection_view) : prop =
  (old.raw_log == next.raw_log \/ raw_io_log_extends old.raw_log next.raw_log) /\
  (old.app_view == next.app_view \/ app_log_extends old.app_view next.app_view)

let step
  (view0:connection_view)
  (req:client_request)
  (view1:connection_view)
  (resp:client_response)
  : prop =
  connection_view_consistent view0 /\
  connection_view_consistent view1 /\
  view1.raw_log == step_raw_log view0.raw_log req resp /\
  view1.app_view == step_app_log view0.app_view req resp /\
  response_shape resp /\
  status_matches_phase resp.status view1.state.S.phase /\
  S.conn_evolves view0.state view1.state /\
  connection_view_single_step view0 view1

let lemma_connection_view_single_step_for_core_step
  (view0:connection_view)
  (req:client_request)
  (view1:connection_view)
  (resp:client_response)
  : Lemma
      (requires view1.raw_log == step_raw_log view0.raw_log req resp /\
                view1.app_view == step_app_log view0.app_view req resp)
      (ensures connection_view_single_step view0 view1)
  =
  lemma_step_raw_log_extends view0.raw_log req resp;
  lemma_step_app_log_extends view0.app_view req resp

let connection_view_evolves : RTC.preorder connection_view =
  RTC.closure connection_view_single_step

let sync_state (view:connection_view) (state:S.conn_state) : connection_view =
  { view with state = state }

let sync_raw (view:connection_view) (raw:raw_io_log) : GTot connection_view =
  view_with_raw_streams view raw

let sync_raw_state (view:connection_view) (raw:raw_io_log) (state:S.conn_state) : GTot connection_view =
  { view_with_raw_streams view raw with state = state }

let note_local_fail
  (view:connection_view)
  (err:T.tls_error)
  (state:S.conn_state)
  : connection_view =
  note_host_event view (local_fail_event err) state

let note_send_close_notify
  (view:connection_view)
  (state:S.conn_state)
  : connection_view =
  note_host_event view sent_close_notify_event state

let note_recv_close_notify
  (view:connection_view)
  (state:S.conn_state)
  : connection_view =
  note_host_event view received_close_notify_event state

let note_app_sent
  (view:connection_view)
  (bytes:B.bytes)
  (state:S.conn_state)
  : connection_view =
  note_host_event view (sent_app_event bytes) state

let note_app_received
  (view:connection_view)
  (bytes:B.bytes)
  (state:S.conn_state)
  : connection_view =
  note_host_event view (received_app_event bytes) state

let rec note_app_received_chunks
  (view:connection_view)
  (chunks:list B.bytes)
  : Tot connection_view
        (decreases chunks)
  =
  match chunks with
  | [] -> view
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    note_app_received_chunks (note_app_received view bytes state) rest

let note_app_delivered
  (view:connection_view)
  (bytes:B.bytes)
  : connection_view =
  note_host_event view (local_app_received_event bytes) view.state

let note_app_delivered_with_pending
  (view:connection_view)
  (bytes:B.bytes)
  (pending:B.bytes)
  : connection_view =
  {
    note_app_delivered view bytes with
      pending_app = pending;
      pending_app_record = view.pending_app_record;
      pending_app_offset = view.pending_app_offset + B.length bytes;
  }

let note_app_received_with_pending
  (view:connection_view)
  (bytes:B.bytes)
  (pending:B.bytes)
  (state:S.conn_state)
  : connection_view =
  {
    note_app_received view bytes state with
      pending_app = pending;
      pending_app_record = B.append bytes pending;
      pending_app_offset = B.length bytes;
  }

let lemma_raw_slice_split
  (source:B.bytes)
  (lo:nat)
  (mid:nat)
  (hi:nat)
  : Lemma
      (requires lo <= mid /\ mid <= hi /\ hi <= B.length source)
      (ensures Seq.equal
        (raw_slice source lo hi)
        (B.append (raw_slice source lo mid) (raw_slice source mid hi)))
  =
  let whole = raw_slice source lo hi in
  let left = raw_slice source lo mid in
  let right = raw_slice source mid hi in
  assert (whole == Seq.slice source lo hi);
  assert (left == Seq.slice source lo mid);
  assert (right == Seq.slice source mid hi);
  Seq.lemma_len_slice source lo hi;
  Seq.lemma_len_slice source lo mid;
  Seq.lemma_len_slice source mid hi;
  assert (B.length whole == hi - lo);
  assert (B.length left == mid - lo);
  assert (B.length right == hi - mid);
  assert (mid - lo <= B.length whole);
  SP.lemma_split whole (mid - lo);
  SP.slice_slice source lo hi 0 (mid - lo);
  assert (Seq.slice whole 0 (mid - lo) == left);
  SP.slice_slice source lo hi (mid - lo) (hi - lo);
  assert (Seq.slice whole (mid - lo) (B.length whole) == right);
  assert (B.append left right == whole);
  Seq.lemma_eq_refl whole (B.append left right)

let lemma_raw_slice_prefix_append_equal
  (source:B.bytes)
  (mid:nat)
  (hi:nat)
  (prefix:B.bytes)
  (chunk:B.bytes)
  : Lemma
      (requires mid <= hi /\
                hi <= B.length source /\
                Seq.equal prefix (raw_slice source 0 mid) /\
                Seq.equal chunk (raw_slice source mid hi))
      (ensures Seq.equal (raw_slice source 0 hi) (B.append prefix chunk))
  =
  lemma_raw_slice_split source 0 mid hi;
  Seq.lemma_eq_elim prefix (raw_slice source 0 mid);
  Seq.lemma_eq_elim chunk (raw_slice source mid hi);
  Seq.lemma_eq_refl
    (raw_slice source 0 hi)
    (B.append prefix chunk)

let lemma_pending_app_drain_split
  (view:connection_view)
  (bytes:B.bytes)
  (pending:B.bytes)
  : Lemma
      (requires pending_app_source_consistent view /\
                Seq.equal view.pending_app (B.append bytes pending))
      (ensures view.pending_app_offset + B.length bytes <= B.length view.pending_app_record /\
               Seq.equal pending
                 (raw_slice
                   view.pending_app_record
                   (view.pending_app_offset + B.length bytes)
                   (B.length view.pending_app_record)))
  =
  let source = view.pending_app_record in
  let off = view.pending_app_offset in
  let hi = B.length source in
  let joined = B.append bytes pending in
  assert (off <= hi);
  assert (raw_slice source off hi == Seq.slice source off hi);
  Seq.lemma_len_slice source off hi;
  Seq.lemma_len_append bytes pending;
  assert (B.length joined == B.length bytes + B.length pending);
  assert (B.length (raw_slice source off hi) == hi - off);
  Seq.lemma_eq_elim view.pending_app (raw_slice source off hi);
  Seq.lemma_eq_elim view.pending_app joined;
  assert (raw_slice source off hi == joined);
  assert (hi - off == B.length bytes + B.length pending);
  assert (off + B.length bytes <= hi);
  lemma_raw_slice_split source off (off + B.length bytes) hi;
  assert (Seq.equal
    (raw_slice source off hi)
    (B.append
      (raw_slice source off (off + B.length bytes))
      (raw_slice source (off + B.length bytes) hi)));
  Seq.lemma_eq_elim
    (raw_slice source off hi)
    (B.append
      (raw_slice source off (off + B.length bytes))
      (raw_slice source (off + B.length bytes) hi));
  assert (B.length (raw_slice source off (off + B.length bytes)) == B.length bytes);
  assert (B.append bytes pending ==
          B.append
            (raw_slice source off (off + B.length bytes))
            (raw_slice source (off + B.length bytes) hi));
  SP.lemma_append_inj
    bytes
    pending
    (raw_slice source off (off + B.length bytes))
    (raw_slice source (off + B.length bytes) hi);
  assert (Seq.equal pending (raw_slice source (off + B.length bytes) hi))

let lemma_note_app_delivered_with_pending_source_consistent
  (view:connection_view)
  (bytes:B.bytes)
  (pending:B.bytes)
  : Lemma
      (requires pending_app_source_consistent view /\
                Seq.equal view.pending_app (B.append bytes pending))
      (ensures pending_app_source_consistent
        (note_app_delivered_with_pending view bytes pending))
  =
  lemma_pending_app_drain_split view bytes pending

let with_pending_received_raw
  (view:connection_view)
  (pending:B.bytes)
  : connection_view =
  { view with pending_received_raw = pending }

let note_raw_app_sent
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : GTot connection_view =
  let next = note_app_sent view bytes state in
  view_with_raw_streams { next with raw_log = raw } raw

let note_raw_app_received
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : GTot connection_view =
  let next = note_app_received view bytes state in
  view_with_raw_streams { next with raw_log = raw } raw

let lemma_app_log_extends_snoc_event
  (app:app_log)
  (ev:host_event)
  : Lemma (app_log_extends app (app_log_snoc_event app ev))
=
  let sent_delta = app_sent_delta_of_host_event ev in
  let received_delta = app_received_delta_of_host_event ev in
  assert ((app_log_snoc_event app ev).app_sent == app.app_sent @ sent_delta);
  assert ((app_log_snoc_event app ev).app_received == app.app_received @ received_delta);
  assert (exists (s_delta:list B.bytes) (r_delta:list B.bytes).
            (app_log_snoc_event app ev).app_sent == app.app_sent @ s_delta /\
            (app_log_snoc_event app ev).app_received == app.app_received @ r_delta)

let lemma_connection_view_step_host_event
  (view:connection_view)
  (ev:host_event)
  (state:S.conn_state)
  : Lemma (connection_view_single_step view (note_host_event view ev state))
=
  lemma_app_log_extends_snoc_event view.app_view ev

let lemma_connection_view_consistent_note_host_event
  (view:connection_view)
  (ev:host_event)
  (state_ev:S.event)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view /\
                state_event_of_host_event ev == Some state_ev /\
                S.step view.state state_ev == Some state)
      (ensures connection_view_consistent (note_host_event view ev state))
=
  let next = note_host_event view ev state in
  lemma_sent_tls_of_host_trace_snoc view.host_trace ev;
  lemma_received_tls_of_host_trace_snoc view.host_trace ev;
  lemma_state_events_of_host_trace_snoc view.host_trace ev;
  lemma_app_sent_of_host_trace_snoc view.host_trace ev;
  lemma_app_received_of_host_trace_snoc view.host_trace ev;
  lemma_step_many_snoc
    S.initial
    (state_events_of_host_trace view.host_trace)
    state_ev
    view.state
    state;
  lemma_raw_stream_view_shape #tls_message
    next.raw_log.raw_sent
    next.sent_tls.values;
  lemma_raw_stream_view_shape #tls_message
    next.raw_log.raw_received
    next.received_tls.values;
  assert (state_event_delta_of_host_event ev == [state_ev]);
  assert (state_events_of_host_trace next.host_trace ==
          state_events_of_host_trace view.host_trace @ [state_ev]);
  assert (S.step_many S.initial (state_events_of_host_trace next.host_trace) ==
          Some state);
  assert (sent_tls_of_host_trace next.host_trace == next.sent_tls.values);
  assert (received_tls_of_host_trace next.host_trace == next.received_tls.values);
  assert ((app_log_of_host_trace next.host_trace).app_sent == next.app_view.app_sent);
  assert ((app_log_of_host_trace next.host_trace).app_received == next.app_view.app_received);
  assert (app_log_of_host_trace next.host_trace == next.app_view);
  assert (pending_app_source_consistent view);
  assert (pending_app_source_consistent next);
  assert (connection_view_raw_stream_shaped next);
  assert (connection_view_record_stream_shaped next);
  assert (connection_view_shape next);
  assert (connection_view_consistent_with raw_tls_stream_shapes next)

let lemma_connection_view_consistent_note_host_event_no_state
  (view:connection_view)
  (ev:host_event)
  : Lemma
      (requires connection_view_consistent view /\
                state_event_of_host_event ev == None)
      (ensures connection_view_consistent (note_host_event view ev view.state))
=
  let next = note_host_event view ev view.state in
  lemma_sent_tls_of_host_trace_snoc view.host_trace ev;
  lemma_received_tls_of_host_trace_snoc view.host_trace ev;
  lemma_state_events_of_host_trace_snoc view.host_trace ev;
  lemma_app_sent_of_host_trace_snoc view.host_trace ev;
  lemma_app_received_of_host_trace_snoc view.host_trace ev;
  assert (state_event_delta_of_host_event ev == []);
  L.append_l_nil (state_events_of_host_trace view.host_trace);
  assert (state_events_of_host_trace next.host_trace ==
          state_events_of_host_trace view.host_trace);
  assert (S.step_many S.initial (state_events_of_host_trace next.host_trace) ==
          Some view.state);
  lemma_raw_stream_view_shape #tls_message
    next.raw_log.raw_sent
    next.sent_tls.values;
  lemma_raw_stream_view_shape #tls_message
    next.raw_log.raw_received
    next.received_tls.values;
  assert (sent_tls_of_host_trace next.host_trace == next.sent_tls.values);
  assert (received_tls_of_host_trace next.host_trace == next.received_tls.values);
  assert ((app_log_of_host_trace next.host_trace).app_sent == next.app_view.app_sent);
  assert ((app_log_of_host_trace next.host_trace).app_received == next.app_view.app_received);
  assert (app_log_of_host_trace next.host_trace == next.app_view);
  assert (pending_app_source_consistent view);
  assert (pending_app_source_consistent next);
  assert (connection_view_raw_stream_shaped next);
  assert (connection_view_record_stream_shaped next);
  assert (connection_view_shape next);
  assert (connection_view_consistent_with raw_tls_stream_shapes next)

let rec lemma_note_app_received_chunks_raw_log
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (ensures (note_app_received_chunks view chunks).raw_log == view.raw_log)
      (decreases chunks)
  =
  match chunks with
  | [] -> ()
  | bytes :: rest ->
    let mid =
      note_app_received view bytes (S.advance_read_record view.state) in
    lemma_note_app_received_chunks_raw_log mid rest

let rec lemma_note_app_received_chunks_pending_fields
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (ensures
        (note_app_received_chunks view chunks).pending_app == view.pending_app /\
        (note_app_received_chunks view chunks).pending_app_record == view.pending_app_record /\
        (note_app_received_chunks view chunks).pending_app_offset == view.pending_app_offset /\
        (note_app_received_chunks view chunks).pending_received_raw == view.pending_received_raw)
      (decreases chunks)
  =
  match chunks with
  | [] -> ()
  | bytes :: rest ->
    let mid =
      note_app_received view bytes (S.advance_read_record view.state) in
    assert (mid.pending_app == view.pending_app);
    assert (mid.pending_app_record == view.pending_app_record);
    assert (mid.pending_app_offset == view.pending_app_offset);
    assert (mid.pending_received_raw == view.pending_received_raw);
    lemma_note_app_received_chunks_pending_fields mid rest

let rec lemma_note_app_received_chunks_app_view
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (ensures
        (note_app_received_chunks view chunks).app_view.app_sent ==
          view.app_view.app_sent /\
        (note_app_received_chunks view chunks).app_view.app_received ==
          view.app_view.app_received @ chunks)
      (decreases chunks)
  =
  match chunks with
  | [] ->
    L.append_l_nil view.app_view.app_received
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    let mid = note_app_received view bytes state in
    let next = note_app_received_chunks mid rest in
    L.append_l_nil view.app_view.app_sent;
    assert (mid.app_view.app_sent == view.app_view.app_sent);
    assert (mid.app_view.app_received == view.app_view.app_received @ [bytes]);
    lemma_note_app_received_chunks_app_view mid rest;
    assert (next.app_view.app_sent == mid.app_view.app_sent);
    assert (next.app_view.app_received == mid.app_view.app_received @ rest);
    L.append_assoc view.app_view.app_received [bytes] rest;
    assert ((view.app_view.app_received @ [bytes]) @ rest ==
            view.app_view.app_received @ ([bytes] @ rest));
    assert ([bytes] @ rest == chunks);
    assert (next.app_view.app_sent == view.app_view.app_sent);
    assert (next.app_view.app_received == view.app_view.app_received @ chunks)

let rec lemma_note_app_received_chunks_append
  (view:connection_view)
  (left:list B.bytes)
  (right:list B.bytes)
  : Lemma
      (ensures
        note_app_received_chunks view (left @ right) ==
        note_app_received_chunks (note_app_received_chunks view left) right)
      (decreases left)
  =
  match left with
  | [] -> ()
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    let mid = note_app_received view bytes state in
    lemma_note_app_received_chunks_append mid rest right;
    assert ((bytes :: rest) @ right == bytes :: (rest @ right));
    assert (note_app_received_chunks view left == note_app_received_chunks mid rest)

let lemma_note_app_received_chunks_snoc
  (view:connection_view)
  (chunks:list B.bytes)
  (bytes:B.bytes)
  : Lemma
      (ensures
        note_app_received_chunks view (chunks @ [bytes]) ==
        note_app_received_chunks (note_app_received_chunks view chunks) [bytes])
  =
  lemma_note_app_received_chunks_append view chunks [bytes]

let lemma_note_app_received_chunks_singleton
  (view:connection_view)
  (bytes:B.bytes)
  : Lemma
      (ensures
        note_app_received_chunks view [bytes] ==
        note_app_received view bytes (S.advance_read_record view.state))
  =
  ()

let rec lemma_note_app_received_chunks_state
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (requires view.state.S.phase == S.ApplicationData)
      (ensures (note_app_received_chunks view chunks).state ==
               S.advance_read_records view.state (chunk_count chunks))
      (decreases chunks)
  =
  match chunks with
  | [] -> ()
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    let mid = note_app_received view bytes state in
    lemma_note_app_received_chunks_state mid rest;
    assert (mid.state == state);
    assert (mid.state.S.phase == S.ApplicationData);
    S.lemma_advance_read_records_after_one view.state (chunk_count rest);
    assert (chunk_count chunks == chunk_count rest + 1);
    assert ((note_app_received_chunks view chunks).state ==
            S.advance_read_records view.state (chunk_count chunks))

let lemma_note_app_received_chunks_state_append
  (view:connection_view)
  (left:list B.bytes)
  (right:list B.bytes)
  : Lemma
      (requires view.state.S.phase == S.ApplicationData)
      (ensures
        (note_app_received_chunks (note_app_received_chunks view left) right).state ==
          S.advance_read_records view.state (chunk_count left + chunk_count right) /\
        (note_app_received_chunks view (left @ right)).state ==
          S.advance_read_records view.state (chunk_count left + chunk_count right))
  =
  let mid = note_app_received_chunks view left in
  lemma_note_app_received_chunks_state view left;
  S.lemma_advance_read_records_preserves_phase view.state (chunk_count left);
  assert (mid.state.S.phase == S.ApplicationData);
  lemma_note_app_received_chunks_state mid right;
  S.lemma_advance_read_records_append view.state (chunk_count left) (chunk_count right);
  lemma_note_app_received_chunks_append view left right;
  lemma_chunk_count_append left right

let lemma_note_app_received_chunks_state_snoc
  (view:connection_view)
  (chunks:list B.bytes)
  (bytes:B.bytes)
  : Lemma
      (requires view.state.S.phase == S.ApplicationData)
      (ensures
        (note_app_received_chunks view (chunks @ [bytes])).state ==
          S.advance_read_record (note_app_received_chunks view chunks).state)
  =
  let mid = note_app_received_chunks view chunks in
  lemma_note_app_received_chunks_state_append view chunks [bytes];
  lemma_chunk_count_snoc chunks bytes;
  lemma_note_app_received_chunks_state view chunks;
  S.lemma_advance_read_records_succ view.state (chunk_count chunks);
  assert (mid.state == S.advance_read_records view.state (chunk_count chunks))

let lemma_note_app_received_chunks_state_components
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (requires view.state.S.phase == S.ApplicationData)
      (ensures
        (note_app_received_chunks view chunks).state.S.phase == S.ApplicationData /\
        (note_app_received_chunks view chunks).state.S.write_state == view.state.S.write_state /\
        (note_app_received_chunks view chunks).state.S.read_state.R.seq ==
          view.state.S.read_state.R.seq + chunk_count chunks)
  =
  lemma_note_app_received_chunks_state view chunks;
  S.lemma_advance_read_records_preserves_phase view.state (chunk_count chunks);
  S.lemma_advance_read_records_preserves_write_state view.state (chunk_count chunks);
  S.lemma_advance_read_records_read_seq view.state (chunk_count chunks)

let rec lemma_connection_view_consistent_note_app_received_chunks
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (requires connection_view_consistent view /\
                view.state.S.phase == S.ApplicationData)
      (ensures connection_view_consistent (note_app_received_chunks view chunks) /\
               (note_app_received_chunks view chunks).state.S.phase == S.ApplicationData)
      (decreases chunks)
  =
  match chunks with
  | [] -> ()
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    let mid = note_app_received view bytes state in
    assert (S.step view.state (S.RecvApplicationData bytes) == Some state);
    lemma_connection_view_consistent_note_host_event
      view
      (received_app_event bytes)
      (S.RecvApplicationData bytes)
      state;
    assert (connection_view_consistent mid);
    assert (mid.state.S.phase == S.ApplicationData);
    lemma_connection_view_consistent_note_app_received_chunks mid rest

/// Bundle of invariant-step facts needed by the arbitrary-residual loop in Core.
/// After appending one more chunk to an accumulated list, the new view:
///   (1) is connection_view_consistent and in ApplicationData phase
///   (2) extends the app log by exactly that chunk
///   (3) preserves pending fields and raw_log from the base view
///   (4) preserves write_state unchanged from the base view
///   (5) advances read_state.seq by exactly 1 from the k-chunk view
/// Core can call this single lemma per loop iteration instead of combining several
/// separate lemma calls inside the Pulse proof context.
let lemma_note_app_received_chunks_loop_step
  (view:connection_view)
  (chunks:list B.bytes)
  (bytes:B.bytes)
  : Lemma
      (requires connection_view_consistent view /\
                view.state.S.phase == S.ApplicationData)
      (ensures (
        let acc = note_app_received_chunks view chunks in
        let next = note_app_received_chunks view (chunks @ [bytes]) in
        connection_view_consistent next /\
        next.state.S.phase == S.ApplicationData /\
        next.app_view.app_sent == view.app_view.app_sent /\
        next.app_view.app_received == acc.app_view.app_received @ [bytes] /\
        next.pending_app == view.pending_app /\
        next.pending_app_record == view.pending_app_record /\
        next.pending_app_offset == view.pending_app_offset /\
        next.pending_received_raw == view.pending_received_raw /\
        next.raw_log == view.raw_log /\
        next.state.S.write_state == view.state.S.write_state /\
        next.state.S.read_state.R.seq ==
          acc.state.S.read_state.R.seq + 1))
  =
  lemma_connection_view_consistent_note_app_received_chunks view (chunks @ [bytes]);
  lemma_note_app_received_chunks_state_components view (chunks @ [bytes]);
  lemma_chunk_count_snoc chunks bytes;
  lemma_note_app_received_chunks_state_components view chunks;
  lemma_note_app_received_chunks_app_view view (chunks @ [bytes]);
  lemma_note_app_received_chunks_app_view view chunks;
  L.append_assoc view.app_view.app_received chunks [bytes];
  lemma_note_app_received_chunks_pending_fields view (chunks @ [bytes]);
  lemma_note_app_received_chunks_raw_log view (chunks @ [bytes])

let rec lemma_note_app_received_chunks_conn_evolves
  (view:connection_view)
  (chunks:list B.bytes)
  : Lemma
      (requires view.state.S.phase == S.ApplicationData)
      (ensures S.conn_evolves view.state (note_app_received_chunks view chunks).state)
      (decreases chunks)
  =
  match chunks with
  | [] -> ()
  | bytes :: rest ->
    let state = S.advance_read_record view.state in
    let mid = note_app_received view bytes state in
    assert (S.step view.state (S.RecvApplicationData bytes) == Some state);
    assert (S.state_single_step view.state state);
    RTC.closure_step S.state_single_step view.state state;
    assert (S.conn_evolves view.state mid.state);
    assert (mid.state.S.phase == S.ApplicationData);
    lemma_note_app_received_chunks_conn_evolves mid rest;
    assert (S.conn_evolves mid.state (note_app_received_chunks mid rest).state);
    assert (RTC.transitive S.conn_evolves);
    assert (S.conn_evolves view.state (note_app_received_chunks mid rest).state)

let lemma_step_start_success_abstract
  (view0:connection_view)
  (view1:connection_view)
  (server_name:T.hostname)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent view1 /\
                view0.state.S.phase == S.Start /\
                view1.raw_log == view0.raw_log /\
                view1.app_view == view0.app_view /\
                view1.state.S.phase == S.ApplicationData /\
                S.conn_evolves view0.state view1.state)
      (ensures step
        view0
        (request_no_network_in (OpStart server_name))
        view1
        (response_no_network_out B.empty HandshakeComplete))
  =
  let req = request_no_network_in (OpStart server_name) in
  let resp = response_no_network_out B.empty HandshakeComplete in
  lemma_append_empty_right view0.raw_log.raw_sent;
  lemma_append_empty_right view0.raw_log.raw_received;
  assert ((step_raw_log view0.raw_log req resp).raw_sent == view0.raw_log.raw_sent);
  assert ((step_raw_log view0.raw_log req resp).raw_received == view0.raw_log.raw_received);
  assert (step_raw_log view0.raw_log req resp == view0.raw_log);
  assert (view1.raw_log == step_raw_log view0.raw_log req resp);
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received);
  assert (step_app_log view0.app_view req resp == view0.app_view);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_start_failed
  (view0:connection_view)
  (server_name:T.hostname)
  (err:T.tls_error)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                view0.state.S.phase == S.Start /\
                state == S.fail view0.state err)
      (ensures step
        view0
        (request_no_network_in (OpStart server_name))
        (note_local_fail view0 err state)
        (response_no_network_out B.empty (Failed err)))
  =
  let view1 = note_local_fail view0 err state in
  let req = request_no_network_in (OpStart server_name) in
  let resp = response_no_network_out B.empty (Failed err) in
  assert (S.step view0.state (S.Fail err) == Some state);
  lemma_connection_view_consistent_note_host_event
    view0
    (local_fail_event err)
    (S.Fail err)
    state;
  assert (connection_view_consistent view1);
  lemma_append_empty_right view0.raw_log.raw_sent;
  lemma_append_empty_right view0.raw_log.raw_received;
  assert ((step_raw_log view0.raw_log req resp).raw_sent == view0.raw_log.raw_sent);
  assert ((step_raw_log view0.raw_log req resp).raw_received == view0.raw_log.raw_received);
  assert (step_raw_log view0.raw_log req resp == view0.raw_log);
  assert (view1.raw_log == step_raw_log view0.raw_log req resp);
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_send_application_data_success
  (view0:connection_view)
  (raw_view:connection_view)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_received view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                state == S.advance_write_records view0.state (S.application_data_record_count bytes))
      (ensures step
        view0
        (request_no_network_in (OpSendApplicationData bytes))
        (note_app_sent raw_view bytes state)
        (response_with_sent_raw_delta view0.raw_log (note_app_sent raw_view bytes state).raw_log B.empty ActionComplete))
  =
  let view1 = note_app_sent raw_view bytes state in
  let req = request_no_network_in (OpSendApplicationData bytes) in
  let resp = response_with_sent_raw_delta view0.raw_log view1.raw_log B.empty ActionComplete in
  assert (S.step raw_view.state (S.SendApplicationData bytes) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    (sent_app_event bytes)
    (S.SendApplicationData bytes)
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_sent_delta view0.raw_log view1.raw_log (OpSendApplicationData bytes) B.empty ActionComplete;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ [bytes]);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ [bytes]);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  S.lemma_advance_write_records_preserves_phase view0.state (S.application_data_record_count bytes);
  assert (view1.state.S.phase == S.ApplicationData);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.SendApplicationData bytes) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_send_application_data_failed
  (view0:connection_view)
  (raw_view:connection_view)
  (bytes:B.bytes)
  (err:T.tls_error)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_received view0.raw_log raw_view.raw_log /\
                state == S.fail view0.state err)
      (ensures step
        view0
        (request_no_network_in (OpSendApplicationData bytes))
        (note_local_fail raw_view err state)
        (response_with_sent_raw_delta view0.raw_log (note_local_fail raw_view err state).raw_log B.empty (Failed err)))
  =
  let view1 = note_local_fail raw_view err state in
  let req = request_no_network_in (OpSendApplicationData bytes) in
  let resp = response_with_sent_raw_delta view0.raw_log view1.raw_log B.empty (Failed err) in
  assert (S.step raw_view.state (S.Fail err) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    (local_fail_event err)
    (S.Fail err)
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_sent_delta view0.raw_log view1.raw_log (OpSendApplicationData bytes) B.empty (Failed err);
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.Fail err) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_close_success
  (view0:connection_view)
  (raw_view:connection_view)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_received view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                state == S.send_close_state view0.state)
      (ensures step
        view0
        (request_no_network_in OpClose)
        (note_send_close_notify raw_view state)
        (response_with_sent_raw_delta view0.raw_log (note_send_close_notify raw_view state).raw_log B.empty Closed))
  =
  let view1 = note_send_close_notify raw_view state in
  let req = request_no_network_in OpClose in
  let resp = response_with_sent_raw_delta view0.raw_log view1.raw_log B.empty Closed in
  assert (S.step raw_view.state S.SendCloseNotify == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    sent_close_notify_event
    S.SendCloseNotify
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_sent_delta view0.raw_log view1.raw_log OpClose B.empty Closed;
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state S.SendCloseNotify == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_close_failed
  (view0:connection_view)
  (raw_view:connection_view)
  (err:T.tls_error)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_received view0.raw_log raw_view.raw_log /\
                state == S.fail view0.state err)
      (ensures step
        view0
        (request_no_network_in OpClose)
        (note_local_fail raw_view err state)
        (response_with_sent_raw_delta view0.raw_log (note_local_fail raw_view err state).raw_log B.empty (Failed err)))
  =
  let view1 = note_local_fail raw_view err state in
  let req = request_no_network_in OpClose in
  let resp = response_with_sent_raw_delta view0.raw_log view1.raw_log B.empty (Failed err) in
  assert (S.step raw_view.state (S.Fail err) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    (local_fail_event err)
    (S.Fail err)
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_sent_delta view0.raw_log view1.raw_log OpClose B.empty (Failed err);
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.Fail err) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_application_data_success
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                state == S.advance_read_record view0.state)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_app_received raw_view bytes state).raw_log)
        (note_app_received raw_view bytes state)
        (response_no_network_out bytes ApplicationDataReady))
  =
  let view1 = note_app_received raw_view bytes state in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out bytes ApplicationDataReady in
  assert (S.step raw_view.state (S.RecvApplicationData bytes) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    (received_app_event bytes)
    (S.RecvApplicationData bytes)
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_received_delta view0.raw_log view1.raw_log (OpReadApplicationData max_len) bytes ApplicationDataReady;
  L.append_l_nil view0.app_view.app_sent;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ [bytes]);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ [bytes]);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.RecvApplicationData bytes) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_application_data_chunks_success
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (app_out:B.bytes)
  (chunks:list B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                Seq.equal app_out (concat_bytes chunks))
      (ensures step
        view0
        (request_with_received_raw_delta
          (OpReadApplicationData max_len)
          view0.raw_log
          (note_app_received_chunks raw_view chunks).raw_log)
        (note_app_received_chunks raw_view chunks)
        (response_no_network_out_chunks app_out chunks ApplicationDataReady))
  =
  let view1 = note_app_received_chunks raw_view chunks in
  let req =
    request_with_received_raw_delta
      (OpReadApplicationData max_len)
      view0.raw_log
      view1.raw_log in
  let resp = response_no_network_out_chunks app_out chunks ApplicationDataReady in
  lemma_connection_view_consistent_note_app_received_chunks raw_view chunks;
  assert (connection_view_consistent view1);
  lemma_note_app_received_chunks_raw_log raw_view chunks;
  assert (view1.raw_log == raw_view.raw_log);
  lemma_step_raw_log_received_delta_chunks
    view0.raw_log
    view1.raw_log
    (OpReadApplicationData max_len)
    app_out
    chunks
    ApplicationDataReady;
  L.append_l_nil view0.app_view.app_sent;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  lemma_note_app_received_chunks_app_view raw_view chunks;
  assert (view1.app_view.app_sent == view0.app_view.app_sent);
  assert (view1.app_view.app_received == view0.app_view.app_received @ chunks);
  assert ((step_app_log view0.app_view req resp).app_sent ==
          view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received ==
          view0.app_view.app_received @ chunks);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  lemma_response_no_network_out_chunks_shape app_out chunks ApplicationDataReady;
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  lemma_note_app_received_chunks_state raw_view chunks;
  lemma_note_app_received_chunks_conn_evolves raw_view chunks;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_application_data_success_with_pending
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (bytes:B.bytes)
  (pending:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                state == S.advance_read_record view0.state)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_app_received_with_pending raw_view bytes pending state).raw_log)
        (note_app_received_with_pending raw_view bytes pending state)
        (response_no_network_out bytes ApplicationDataReady))
  =
  let base = note_app_received raw_view bytes state in
  let view1 = note_app_received_with_pending raw_view bytes pending state in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out bytes ApplicationDataReady in
  lemma_step_read_application_data_success view0 raw_view max_len bytes state;
  lemma_raw_slice_append_suffix bytes pending;
  assert (pending_app_source_consistent view1);
  assert (connection_view_consistent base);
  assert (connection_view_consistent view1);
  assert (view1.raw_log == base.raw_log);
  assert (view1.app_view == base.app_view);
  assert (view1.state == base.state);
  assert (step view0 req base resp);
  assert (view1.raw_log == step_raw_log view0.raw_log req resp);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_application_data_delivered
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (bytes:B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_app_delivered raw_view bytes).raw_log)
        (note_app_delivered raw_view bytes)
        (response_no_network_out bytes ApplicationDataReady))
  =
  let view1 = note_app_delivered raw_view bytes in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out bytes ApplicationDataReady in
  lemma_connection_view_consistent_note_host_event_no_state
    raw_view
    (local_app_received_event bytes);
  assert (connection_view_consistent view1);
  lemma_step_raw_log_received_delta view0.raw_log view1.raw_log (OpReadApplicationData max_len) bytes ApplicationDataReady;
  L.append_l_nil view0.app_view.app_sent;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ [bytes]);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ [bytes]);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (view1.state == view0.state);
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_application_data_delivered_with_pending
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (bytes:B.bytes)
  (pending:B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                Seq.equal raw_view.pending_app (B.append bytes pending))
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_app_delivered_with_pending raw_view bytes pending).raw_log)
        (note_app_delivered_with_pending raw_view bytes pending)
        (response_no_network_out bytes ApplicationDataReady))
  =
  let base = note_app_delivered raw_view bytes in
  let view1 = note_app_delivered_with_pending raw_view bytes pending in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out bytes ApplicationDataReady in
  lemma_step_read_application_data_delivered view0 raw_view max_len bytes;
  lemma_note_app_delivered_with_pending_source_consistent raw_view bytes pending;
  assert (pending_app_source_consistent view1);
  assert (connection_view_consistent base);
  assert (connection_view_consistent view1);
  assert (view1.raw_log == base.raw_log);
  assert (view1.app_view == base.app_view);
  assert (view1.state == base.state);
  assert (step view0 req base resp);
  assert (view1.raw_log == step_raw_log view0.raw_log req resp);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_need_network_input
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log raw_view.raw_log)
        raw_view
        (response_no_network_out B.empty NeedNetworkInput))
  =
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log raw_view.raw_log in
  let resp = response_no_network_out B.empty NeedNetworkInput in
  lemma_step_raw_log_received_delta view0.raw_log raw_view.raw_log (OpReadApplicationData max_len) B.empty NeedNetworkInput;
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (raw_view.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status raw_view.state.S.phase);
  assert (raw_view.state == view0.state);
  assert (S.conn_evolves view0.state raw_view.state);
  lemma_connection_view_single_step_for_core_step view0 req raw_view resp

let lemma_step_read_need_network_input_with_pending
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (pending:B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (with_pending_received_raw raw_view pending).raw_log)
        (with_pending_received_raw raw_view pending)
        (response_no_network_out B.empty NeedNetworkInput))
  =
  let view1 = with_pending_received_raw raw_view pending in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out B.empty NeedNetworkInput in
  lemma_step_read_need_network_input view0 raw_view max_len;
  assert (pending_app_source_consistent raw_view);
  assert (pending_app_source_consistent view1);
  assert (connection_view_consistent view1);
  assert (view1.raw_log == raw_view.raw_log);
  assert (view1.app_view == raw_view.app_view);
  assert (view1.state == raw_view.state);
  assert (step view0 req raw_view resp);
  assert (view1.raw_log == step_raw_log view0.raw_log req resp);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_with_pending_received_raw
  (view0:connection_view)
  (req:client_request)
  (view1:connection_view)
  (resp:client_response)
  (pending:B.bytes)
  : Lemma
      (requires step view0 req view1 resp)
      (ensures step view0 req (with_pending_received_raw view1 pending) resp)
  =
  let view2 = with_pending_received_raw view1 pending in
  assert (pending_app_source_consistent view1);
  assert (pending_app_source_consistent view2);
  assert (connection_view_consistent view2);
  assert (view2.raw_log == view1.raw_log);
  assert (view2.app_view == view1.app_view);
  assert (view2.state == view1.state);
  assert (view2.raw_log == step_raw_log view0.raw_log req resp);
  assert (view2.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view2.state.S.phase);
  assert (S.conn_evolves view0.state view2.state);
  lemma_connection_view_single_step_for_core_step view0 req view2 resp

let lemma_step_read_application_data_chunks_success_with_pending_raw
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (app_out:B.bytes)
  (chunks:list B.bytes)
  (pending:B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                Seq.equal app_out (concat_bytes chunks))
      (ensures step
        view0
        (request_with_received_raw_delta
          (OpReadApplicationData max_len)
          view0.raw_log
          (with_pending_received_raw (note_app_received_chunks raw_view chunks) pending).raw_log)
        (with_pending_received_raw (note_app_received_chunks raw_view chunks) pending)
        (response_no_network_out_chunks app_out chunks ApplicationDataReady))
  =
  let base = note_app_received_chunks raw_view chunks in
  let view1 = with_pending_received_raw base pending in
  let req =
    request_with_received_raw_delta
      (OpReadApplicationData max_len)
      view0.raw_log
      base.raw_log in
  let req_pending =
    request_with_received_raw_delta
      (OpReadApplicationData max_len)
      view0.raw_log
      view1.raw_log in
  let resp = response_no_network_out_chunks app_out chunks ApplicationDataReady in
  lemma_step_read_application_data_chunks_success
    view0
    raw_view
    max_len
    app_out
    chunks;
  assert (step view0 req base resp);
  assert (view1.raw_log == base.raw_log);
  assert (req_pending == req);
  lemma_step_with_pending_received_raw view0 req base resp pending

let lemma_step_read_application_data_single_chunk_success_with_pending_raw
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (bytes:B.bytes)
  (pending:B.bytes)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData)
      (ensures step
        view0
        (request_with_received_raw_delta
          (OpReadApplicationData max_len)
          view0.raw_log
          (with_pending_received_raw (note_app_received_chunks raw_view [bytes]) pending).raw_log)
        (with_pending_received_raw (note_app_received_chunks raw_view [bytes]) pending)
        (response_no_network_out_chunks bytes [bytes] ApplicationDataReady))
  =
  lemma_concat_bytes_singleton bytes;
  lemma_step_read_application_data_chunks_success_with_pending_raw
    view0
    raw_view
    max_len
    bytes
    [bytes]
    pending

let lemma_step_read_close_notify
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                view0.state.S.phase == S.ApplicationData /\
                state == S.recv_close_state view0.state)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_recv_close_notify raw_view state).raw_log)
        (note_recv_close_notify raw_view state)
        (response_no_network_out B.empty Closed))
  =
  let view1 = note_recv_close_notify raw_view state in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out B.empty Closed in
  assert (S.step raw_view.state S.RecvCloseNotify == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    received_close_notify_event
    S.RecvCloseNotify
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_received_delta view0.raw_log view1.raw_log (OpReadApplicationData max_len) B.empty Closed;
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state S.RecvCloseNotify == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_alert_failed
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (alert:T.alert_description)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                alert <> T.CloseNotify /\
                state == S.fail view0.state (T.AlertError alert))
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_host_event raw_view (NetworkEvent { message_direction = Received; message_value = TlsAlert alert }) state).raw_log)
        (note_host_event raw_view (NetworkEvent { message_direction = Received; message_value = TlsAlert alert }) state)
        (response_no_network_out B.empty (Failed (T.AlertError alert))))
  =
  let ev = NetworkEvent { message_direction = Received; message_value = TlsAlert alert } in
  let view1 = note_host_event raw_view ev state in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out B.empty (Failed (T.AlertError alert)) in
  assert (state_event_of_host_event ev == Some (S.Fail (T.AlertError alert)));
  assert (S.step raw_view.state (S.Fail (T.AlertError alert)) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    ev
    (S.Fail (T.AlertError alert))
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_received_delta view0.raw_log view1.raw_log (OpReadApplicationData max_len) B.empty (Failed (T.AlertError alert));
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.Fail (T.AlertError alert)) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_step_read_failed
  (view0:connection_view)
  (raw_view:connection_view)
  (max_len:nat)
  (err:T.tls_error)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_consistent view0 /\
                connection_view_consistent raw_view /\
                raw_view.state == view0.state /\
                raw_view.app_view == view0.app_view /\
                raw_io_log_extends view0.raw_log raw_view.raw_log /\
                raw_io_log_same_sent view0.raw_log raw_view.raw_log /\
                state == S.fail view0.state err)
      (ensures step
        view0
        (request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log (note_local_fail raw_view err state).raw_log)
        (note_local_fail raw_view err state)
        (response_no_network_out B.empty (Failed err)))
  =
  let view1 = note_local_fail raw_view err state in
  let req = request_with_received_raw_delta (OpReadApplicationData max_len) view0.raw_log view1.raw_log in
  let resp = response_no_network_out B.empty (Failed err) in
  assert (S.step raw_view.state (S.Fail err) == Some state);
  lemma_connection_view_consistent_note_host_event
    raw_view
    (local_fail_event err)
    (S.Fail err)
    state;
  assert (connection_view_consistent view1);
  lemma_step_raw_log_received_delta view0.raw_log view1.raw_log (OpReadApplicationData max_len) B.empty (Failed err);
  L.append_l_nil view0.app_view.app_sent;
  L.append_l_nil view0.app_view.app_received;
  assert (raw_view.app_view.app_sent == view0.app_view.app_sent);
  assert (raw_view.app_view.app_received == view0.app_view.app_received);
  assert (view1.app_view.app_sent == view0.app_view.app_sent @ []);
  assert (view1.app_view.app_received == view0.app_view.app_received @ []);
  assert ((step_app_log view0.app_view req resp).app_sent == view0.app_view.app_sent @ []);
  assert ((step_app_log view0.app_view req resp).app_received == view0.app_view.app_received @ []);
  assert (view1.app_view == step_app_log view0.app_view req resp);
  assert (response_shape resp);
  assert (status_matches_phase resp.status view1.state.S.phase);
  assert (S.step view0.state (S.Fail err) == Some state);
  assert (S.state_single_step view0.state state);
  RTC.closure_step S.state_single_step view0.state state;
  assert (S.conn_evolves view0.state view1.state);
  lemma_connection_view_single_step_for_core_step view0 req view1 resp

let lemma_connection_view_app_projected_sync_state
  (view:connection_view)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_app_projected view)
      (ensures connection_view_app_projected (sync_state view state))
  =
  ()

let lemma_connection_view_app_projected_sync_raw_state
  (view:connection_view)
  (raw:raw_io_log)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_app_projected view)
      (ensures connection_view_app_projected (sync_raw_state view raw state))
  =
  ()

let lemma_connection_view_app_projected_note_raw_app_sent
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_app_projected view)
      (ensures connection_view_app_projected (note_raw_app_sent view raw bytes state))
  =
  lemma_app_sent_snoc_sent view.host_trace bytes;
  lemma_app_received_snoc_sent view.host_trace bytes;
  assert (app_log_of_host_trace (view.host_trace @ [sent_app_event bytes]) ==
          append_app_sent (app_log_of_host_trace view.host_trace) bytes)

let lemma_connection_view_app_projected_note_raw_app_received
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_app_projected view)
      (ensures connection_view_app_projected (note_raw_app_received view raw bytes state))
  =
  lemma_app_sent_snoc_received view.host_trace bytes;
  lemma_app_received_snoc_received view.host_trace bytes;
  assert (app_log_of_host_trace (view.host_trace @ [received_app_event bytes]) ==
          append_app_received (app_log_of_host_trace view.host_trace) bytes)

let lemma_connection_view_record_stream_shaped_empty ()
  : Lemma (connection_view_record_stream_shaped empty_connection_view)
  =
  lemma_parse_record_prefix_serializes empty_raw_io_log.raw_sent;
  lemma_parse_record_prefix_serializes empty_raw_io_log.raw_received

let lemma_connection_view_raw_stream_shaped_empty ()
  : Lemma (connection_view_raw_stream_shaped empty_connection_view)
  =
  lemma_raw_stream_view_shape #tls_message empty_raw_io_log.raw_sent [];
  lemma_raw_stream_view_shape #tls_message empty_raw_io_log.raw_received []

let lemma_connection_view_raw_stream_shaped_sync_state
  (view:connection_view)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_raw_stream_shaped view)
      (ensures connection_view_raw_stream_shaped (sync_state view state))
  =
  ()

let lemma_connection_view_record_stream_shaped_sync_state
  (view:connection_view)
  (state:S.conn_state)
  : Lemma
      (requires connection_view_record_stream_shaped view)
      (ensures connection_view_record_stream_shaped (sync_state view state))
  =
  ()

let lemma_connection_view_raw_stream_shaped_sync_raw_state
  (view:connection_view)
  (raw:raw_io_log)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_raw_stream_shaped (sync_raw_state view raw state))
  =
  lemma_raw_stream_view_shape raw.raw_sent view.sent_tls.values;
  lemma_raw_stream_view_shape raw.raw_received view.received_tls.values

let lemma_connection_view_record_stream_shaped_sync_raw_state
  (view:connection_view)
  (raw:raw_io_log)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_record_stream_shaped (sync_raw_state view raw state))
  =
  lemma_parse_record_prefix_serializes raw.raw_sent;
  lemma_parse_record_prefix_serializes raw.raw_received

let lemma_connection_view_consistent_sync_raw_same_state
  (view:connection_view)
  (raw:raw_io_log)
  : Lemma
      (requires connection_view_consistent view)
      (ensures connection_view_consistent (sync_raw_state view raw view.state))
  =
  lemma_connection_view_raw_stream_shaped_sync_raw_state view raw view.state;
  lemma_connection_view_record_stream_shaped_sync_raw_state view raw view.state;
  assert (connection_view_consistent_with raw_tls_stream_shapes view);
  assert (connection_view_consistent_with raw_tls_stream_shapes (sync_raw_state view raw view.state));
  assert (pending_app_source_consistent view);
  assert (pending_app_source_consistent (sync_raw_state view raw view.state));
  assert (connection_view_shape (sync_raw_state view raw view.state))

let lemma_connection_view_raw_stream_shaped_note_raw_app_sent
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_raw_stream_shaped (note_raw_app_sent view raw bytes state))
  =
  lemma_raw_stream_view_shape raw.raw_sent (view.sent_tls.values @ [TlsApplicationData bytes]);
  lemma_raw_stream_view_shape raw.raw_received view.received_tls.values

let lemma_connection_view_record_stream_shaped_note_raw_app_sent
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_record_stream_shaped (note_raw_app_sent view raw bytes state))
  =
  lemma_parse_record_prefix_serializes raw.raw_sent;
  lemma_parse_record_prefix_serializes raw.raw_received

let lemma_connection_view_raw_stream_shaped_note_raw_app_received
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_raw_stream_shaped (note_raw_app_received view raw bytes state))
  =
  lemma_raw_stream_view_shape raw.raw_sent view.sent_tls.values;
  lemma_raw_stream_view_shape raw.raw_received (view.received_tls.values @ [TlsApplicationData bytes])

let lemma_connection_view_record_stream_shaped_note_raw_app_received
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (ensures connection_view_record_stream_shaped (note_raw_app_received view raw bytes state))
  =
  lemma_parse_record_prefix_serializes raw.raw_sent;
  lemma_parse_record_prefix_serializes raw.raw_received

let lemma_connection_view_step_same_app
  (old:connection_view)
  (next:connection_view{old.raw_log == next.raw_log /\ old.app_view == next.app_view})
  : Lemma (connection_view_single_step old next)
  = ()

let lemma_connection_view_step_raw_state
  (view:connection_view)
  (raw:raw_io_log)
  (state:S.conn_state)
  : Lemma
      (requires raw_io_log_extends view.raw_log raw)
      (ensures connection_view_single_step view (sync_raw_state view raw state))
  =
  ()

let lemma_connection_view_step_sent
  (view:connection_view)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma (connection_view_single_step view (note_app_sent view bytes state))
  =
  lemma_app_log_extends_sent view.app_view bytes

let lemma_connection_view_step_received
  (view:connection_view)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma (connection_view_single_step view (note_app_received view bytes state))
  =
  lemma_app_log_extends_received view.app_view bytes

let lemma_connection_view_step_raw_sent
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires raw_io_log_extends view.raw_log raw)
      (ensures connection_view_single_step view (note_raw_app_sent view raw bytes state))
  =
  lemma_app_log_extends_sent view.app_view bytes

let lemma_connection_view_step_raw_received
  (view:connection_view)
  (raw:raw_io_log)
  (bytes:B.bytes)
  (state:S.conn_state)
  : Lemma
      (requires raw_io_log_extends view.raw_log raw)
      (ensures connection_view_single_step view (note_raw_app_received view raw bytes state))
  =
  lemma_app_log_extends_received view.app_view bytes

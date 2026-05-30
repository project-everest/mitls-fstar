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

let raw_slice (bytes:B.bytes) (lo:nat) (hi:nat) : B.bytes =
  if lo <= hi && hi <= B.length bytes
  then Seq.slice bytes lo hi
  else B.empty

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

type host_event =
  | NetworkEvent of directed_message tls_message
  | LocalEvent of local_event

type app_log = {
  app_sent: list B.bytes;
  app_received: list B.bytes;
}

type client_request =
  | ReqStart of server_name:T.hostname
  | ReqRecvNetwork of ciphertext:B.bytes
  | ReqSendApplicationData of plaintext:B.bytes
  | ReqReadApplicationData of max_len:nat
  | ReqClose

type client_status =
  | NeedNetworkInput
  | HandshakeComplete
  | ApplicationDataReady
  | Closed
  | Failed of error:T.tls_error

type client_response = {
  network_out: B.bytes;
  app_out: B.bytes;
  status: client_status;
}

let empty_app_log : app_log =
  { app_sent = []; app_received = [] }

let append_app_sent (app:app_log) (bytes:B.bytes) : app_log =
  { app with app_sent = app.app_sent @ [bytes] }

let append_app_received (app:app_log) (bytes:B.bytes) : app_log =
  { app with app_received = app.app_received @ [bytes] }

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
  match req with
  | ReqRecvNetwork ciphertext -> ciphertext
  | _ -> B.empty

let request_app_in (req:client_request) : B.bytes =
  match req with
  | ReqSendApplicationData plaintext -> plaintext
  | _ -> B.empty

let request_read_len (req:client_request) : nat =
  match req with
  | ReqReadApplicationData max_len -> max_len
  | _ -> 0

let response_shape (resp:client_response) : prop =
  match resp.status with
  | NeedNetworkInput
  | HandshakeComplete
  | Closed
  | Failed _ -> B.length resp.app_out == 0
  | ApplicationDataReady -> True

let status_matches_phase (status:client_status) (phase:S.phase) : prop =
  match status with
  | NeedNetworkInput -> phase <> S.Closed /\ phase <> S.Failed
  | HandshakeComplete -> phase == S.ApplicationData
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
  match req, resp.status with
  | ReqSendApplicationData plaintext, Failed _ -> []
  | ReqSendApplicationData plaintext, _ -> [plaintext]
  | _, _ -> []

let step_app_received_delta (resp:client_response) : list B.bytes =
  match resp.status with
  | ApplicationDataReady -> [resp.app_out]
  | _ -> []

let step_app_log (app:app_log) (req:client_request) (resp:client_response) : app_log =
  {
    app_sent = app.app_sent @ step_app_sent_delta req resp;
    app_received = app.app_received @ step_app_received_delta resp;
  }

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
  | LocalEvent _ -> []

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
     | LocalEvent _ -> app_received_of_host_trace rest)

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
  | [] -> ()
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
}

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
  connection_view_record_stream_shaped view

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
  assert (connection_view_raw_stream_shaped next);
  assert (connection_view_record_stream_shaped next);
  assert (connection_view_shape next);
  assert (connection_view_consistent_with raw_tls_stream_shapes next)

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

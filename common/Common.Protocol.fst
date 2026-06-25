module Common.Protocol

module L = FStar.List.Tot
module TCP = Common.TCP

type network_direction =
  | NetworkReceived
  | NetworkSent

noeq
type directed_message (wire_message:Type0) = {
  dm_direction: network_direction;
  dm_payload: wire_message;
}

let received (#wire_message:Type0) (payload:wire_message) : directed_message wire_message =
  {
    dm_direction = NetworkReceived;
    dm_payload = payload;
  }

let sent (#wire_message:Type0) (payload:wire_message) : directed_message wire_message =
  {
    dm_direction = NetworkSent;
    dm_payload = payload;
  }

let direction_matches
  (#wire_message:Type0)
  (dir:network_direction)
  (msg:directed_message wire_message)
  : bool =
  match dir, msg.dm_direction with
  | NetworkReceived, NetworkReceived -> true
  | NetworkSent, NetworkSent -> true
  | _, _ -> false

let rec directed_payloads
  (#wire_message:Type0)
  (dir:network_direction)
  (log:list (directed_message wire_message))
  : Tot (list wire_message)
        (decreases log)
  =
  match log with
  | [] -> []
  | msg :: rest ->
    if direction_matches dir msg
    then msg.dm_payload :: directed_payloads dir rest
    else directed_payloads dir rest

noextract
class wire_format (wire_message:Type0) = {
  wf_stream_matches:
    network_direction ->
    TCP.bytes ->
    list wire_message ->
    TCP.bytes ->
    GTot prop;

  wf_history_matches:
    TCP.history ->
    list (directed_message wire_message) ->
    GTot prop;
}

let default_history_matches
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (tcp:TCP.history)
  (wire_log:list (directed_message wire_message))
  : prop =
  exists received_residual sent_residual.
    fmt.wf_stream_matches
      NetworkReceived
      tcp.TCP.tcp_received
      (directed_payloads NetworkReceived wire_log)
      received_residual /\
    fmt.wf_stream_matches
      NetworkSent
      tcp.TCP.tcp_sent
      (directed_payloads NetworkSent wire_log)
      sent_residual

noextract
class state_machine_protocol
  (state:Type0)
  (wire_message:Type0)
  (event:Type0)
  =
{
  sm_wire_format: wire_format wire_message;

  sm_processed_history:
    state -> GTot TCP.history;

  sm_wire_log:
    state -> GTot (list (directed_message wire_message));

  sm_event_log:
    state -> GTot (list event);

  sm_transport_matches:
    TCP.history -> state -> GTot prop;

  sm_events_refine_wire:
    state -> GTot prop;

  sm_step:
    state ->
    event ->
    state ->
    list (directed_message wire_message) ->
    GTot prop;

  sm_invariant:
    state -> GTot prop;

  sm_valid:
    state -> GTot prop;

  sm_valid_implies_layers:
    s:state ->
      Lemma
        (requires sm_valid s)
        (ensures
          sm_wire_format.wf_history_matches
            (sm_processed_history s)
            (sm_wire_log s) /\
          sm_transport_matches
            (sm_processed_history s)
            s /\
          sm_events_refine_wire s /\
          sm_invariant s);
}

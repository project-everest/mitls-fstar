module DH.Sample.DY.Model

(**
  Pure interpretation of the authoritative canonical history.

  This is not a second protocol state machine: it consumes only generic
  `system_effect`s.  Concrete values never require an equality oracle.  Their
  symbolic counterparts are recovered from endpoint-local protocol context and
  the packet index recorded by the generic system.
*)

module E = Common.Protocol.Labelled
module S = Common.Protocol.System
module I = Common.Protocol.Interpretation
module SM = DH.Sample.StateMachine
module D = DH.Sample.DY.Terms
module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module TB = DY.Core.Trace.Base
module T = DY.Core.Trace.Type
module L = FStar.List.Tot

open DH.Sample.Types
open DH.Sample.Wire

noeq
type endpoint_shadow = {
  long_term: BT.bytes;
  private_value: option BT.bytes;
  own_share: option BT.bytes;
  peer_share: option BT.bytes;
  key: option BT.bytes;
  pending_signature: option BT.bytes;
  last_received: option D.symbolic_message;
  state_position: nat;
}

noeq
type network_shadow = {
  symbolic_packet: D.symbolic_message;
  send_position: nat;
}

noeq
type model = {
  dy_trace: TB.trace;
  endpoints: list endpoint_shadow;
  network: list network_shadow;
}

let rec lookup #a (values:list a) (index:nat) : Tot (option a) =
  match values with
  | [] -> None
  | head :: tail ->
    if index = 0
    then Some head
    else lookup tail (index - 1)

let rec replace #a
  (values:list a)
  (index:nat)
  (value:a)
  : Tot (list a)
  =
  match values with
  | [] -> []
  | head :: tail ->
    if index = 0
    then value :: tail
    else head :: replace tail (index - 1) value

let append_entry (trace:TB.trace) (entry:TB.trace_entry) : TB.trace =
  TB.append_entry trace entry

let endpoint_snapshot (shadow:endpoint_shadow) : BT.bytes =
  D.snapshot
    shadow.long_term
    shadow.private_value
    shadow.own_share
    shadow.peer_share
    shadow.key

let initial_shadow (long_term:BT.bytes) (state_position:nat)
  : endpoint_shadow
  =
  {
    long_term;
    private_value = None;
    own_share = None;
    peer_share = None;
    key = None;
    pending_signature = None;
    last_received = None;
    state_position;
  }

let empty_snapshot (long_term:BT.bytes) : BT.bytes =
  D.snapshot long_term None None None None

let initial_trace : TB.trace =
  let initiator_long_term = D.long_term_term 0 in
  let responder_long_term = D.long_term_term 2 in
  let trace0 = TB.empty_trace in
  let trace1 =
    append_entry trace0
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.initiator_endpoint)
        D.long_term_length)
  in
  let trace2 =
    append_entry trace1
      (T.SetState
        D.initiator_dy_principal
        (D.role_state_id SM.initiator_endpoint)
        (empty_snapshot initiator_long_term))
  in
  let trace3 =
    append_entry trace2
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.responder_endpoint)
        D.long_term_length)
  in
  append_entry trace3
    (T.SetState
      D.responder_dy_principal
      (D.role_state_id SM.responder_endpoint)
      (empty_snapshot responder_long_term))

let initial_model : model = {
  dy_trace = initial_trace;
  endpoints = [
    initial_shadow (D.long_term_term 0) 1;
    initial_shadow (D.long_term_term 2) 3;
  ];
  network = [];
}

let put_endpoint
  (state:model)
  (who:E.endpoint_id)
  (shadow:endpoint_shadow)
  : model
  =
  { state with endpoints = replace state.endpoints who shadow }

let fresh_generated
  (state:model)
  (who:E.endpoint_id)
  (_:scalar)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    let fresh_position = TB.trace_length state.dy_trace in
    let private_value = D.ephemeral_term fresh_position in
    let generated_trace =
      append_entry state.dy_trace
        (T.RandGen
          D.ephemeral_usage
          (D.role_label who)
          D.ephemeral_length)
    in
    let shadow1 = {
      shadow with
        private_value = Some private_value;
        own_share = None;
        peer_share = None;
        key = None;
        pending_signature = None;
        state_position = fresh_position + 1;
    } in
    let trace1 =
      append_entry generated_trace
        (T.SetState
          (D.role_principal who)
          (D.role_state_id who)
          (endpoint_snapshot shadow1))
    in
    put_endpoint { state with dy_trace = trace1 } who shadow1

let symbolic_peer_share
  (shadow:endpoint_shadow)
  (fallback:share)
  : BT.bytes
  =
  match shadow.last_received with
  | Some (D.SymbolicMessage1 _ value) -> value
  | Some (D.SymbolicMessage2 _ value _) -> value
  | _ -> D.share_literal fallback

let set_public_share
  (state:model)
  (who:E.endpoint_id)
  : model
  =
  match lookup state.endpoints who with
  | Some shadow ->
    (match shadow.private_value with
     | Some private_value ->
       put_endpoint state who
         { shadow with own_share = Some (D.share_term private_value) }
     | None -> state)
  | _ -> state

let set_shared_secret
  (state:model)
  (who:E.endpoint_id)
  (peer_public:share)
  : model
  =
  match lookup state.endpoints who with
  | Some shadow ->
    (match shadow.private_value with
     | Some private_value ->
       let peer_share = symbolic_peer_share shadow peer_public in
       let key = D.secret_term private_value peer_share in
       let state_position = TB.trace_length state.dy_trace in
       let shadow1 = {
         shadow with
           peer_share = Some peer_share;
           key = Some key;
           state_position;
       } in
       let trace1 =
         append_entry state.dy_trace
           (T.SetState
             (D.role_principal who)
             (D.role_state_id who)
             (endpoint_snapshot shadow1))
       in
       put_endpoint { state with dy_trace = trace1 } who shadow1
     | None -> state)
  | _ -> state

let protocol_transcript
  (who:E.endpoint_id)
  (shadow:endpoint_shadow)
  (partner:principal)
  : option BT.bytes
  =
  match shadow.own_share, shadow.peer_share with
  | Some own_share, Some peer_share ->
    if who = SM.initiator_endpoint
    then
      Some (
        D.transcript_term
          (D.principal_term partner)
          own_share
          peer_share)
    else
      Some (
        D.transcript_term
          (D.principal_term partner)
          peer_share
          own_share)
  | _ -> None

let create_signature
  (state:model)
  (who:E.endpoint_id)
  (partner:principal)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    match protocol_transcript who shadow partner with
    | None -> state
    | Some transcript ->
      let authorization_position = TB.trace_length state.dy_trace in
      let authorization_tag =
        if who = SM.initiator_endpoint
        then D.tag_authorize_initiator
        else D.tag_authorize_responder
      in
      let trace1 =
        append_entry state.dy_trace
          (T.Event
            (D.role_principal who)
            authorization_tag
            transcript)
      in
      let nonce_position = authorization_position + 1 in
      let trace2 =
        append_entry trace1
          (T.RandGen
            D.signing_nonce_usage
            (D.role_label who)
            D.signing_nonce_length)
      in
      let signature =
        D.signature_term
          shadow.long_term
          (D.signing_nonce_term nonce_position)
          transcript
      in
      put_endpoint
        { state with dy_trace = trace2 }
        who
        { shadow with pending_signature = Some signature }

let accepted_signature
  (who:E.endpoint_id)
  (shadow:endpoint_shadow)
  : option BT.bytes
  =
  if who = SM.initiator_endpoint
  then
    match shadow.last_received with
    | Some (D.SymbolicMessage2 _ _ signature) -> Some signature
    | _ -> None
  else
    match shadow.last_received with
    | Some (D.SymbolicMessage3 signature) -> Some signature
    | _ -> None

let acceptance_transcript
  (who:E.endpoint_id)
  (shadow:endpoint_shadow)
  (partner:principal)
  : option BT.bytes
  =
  if who = SM.initiator_endpoint
  then
    match shadow.own_share, shadow.last_received with
    | Some initiator_share,
      Some (D.SymbolicMessage2 _ responder_share _) ->
      Some (
        D.transcript_term
          (D.principal_term partner)
          initiator_share
          responder_share)
    | _, _ -> None
  else
    match shadow.peer_share, shadow.own_share with
    | Some initiator_share, Some responder_share ->
      Some (
        D.transcript_term
          (D.principal_term partner)
          initiator_share
          responder_share)
    | _, _ -> None

let record_acceptance
  (state:model)
  (who:E.endpoint_id)
  (partner:principal)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    match
      acceptance_transcript who shadow partner,
      accepted_signature who shadow
    with
    | Some transcript, Some signature ->
      { state with
          dy_trace =
            append_entry state.dy_trace
              (T.Event
                (D.role_principal who)
                D.tag_accepted
                (D.accepted_content transcript signature)) }
    | _ -> state

let record_completion
  (state:model)
  (who:E.endpoint_id)
  (peer:principal)
  : model
  =
  match lookup state.endpoints who with
  | Some shadow ->
    (match shadow.key with
     | Some key ->
       { state with
           dy_trace =
             append_entry state.dy_trace
               (T.Event
                 (D.role_principal who)
                 D.tag_complete
                 (D.completion_content (D.principal_term peer) key)) }
     | None -> state)
  | _ -> state

let protocol_effect
  (state:model)
  (who:E.endpoint_id)
  (event:SM.semantic_event)
  : model
  =
  match event with
  | SM.PublicShare _ _ ->
    set_public_share state who
  | SM.SharedSecret _ peer_public _ ->
    set_shared_secret state who peer_public
  | SM.SignatureCreated _ partner _ _ _ ->
    create_signature state who partner
  | SM.SignatureAccepted _ partner _ _ _ ->
    record_acceptance state who partner
  | SM.Completed peer _ ->
    record_completion state who peer

let honest_message
  (state:model)
  (who:E.endpoint_id)
  (message:message)
  : D.symbolic_message
  =
  match lookup state.endpoints who with
  | None -> D.injected_message message
  | Some shadow ->
    match message with
    | Message1 initiator initiator_share ->
      (match shadow.own_share with
       | Some own_share ->
         D.SymbolicMessage1 (D.principal_term initiator) own_share
       | None -> D.injected_message message)
    | Message2 responder responder_share responder_signature ->
      (match shadow.own_share, shadow.pending_signature with
       | Some own_share, Some signature ->
         D.SymbolicMessage2
           (D.principal_term responder)
           own_share
           signature
       | _ -> D.injected_message message)
    | Message3 initiator_signature ->
      (match shadow.pending_signature with
       | Some signature -> D.SymbolicMessage3 signature
       | None -> D.injected_message message)

let record_send
  (state:model)
  (who:E.endpoint_id)
  (_:nat)
  (message:message)
  : model
  =
  let symbolic_packet = honest_message state who message in
  let send_position = TB.trace_length state.dy_trace in
  {
    state with
      dy_trace =
        append_entry state.dy_trace
          (T.MsgSent (D.flatten symbolic_packet));
      network =
        L.append state.network [{ symbolic_packet; send_position }];
  }

let record_injection
  (state:model)
  (_:nat)
  (message:message)
  : model
  =
  let symbolic_packet = D.injected_message message in
  let send_position = TB.trace_length state.dy_trace in
  {
    state with
      dy_trace =
        append_entry state.dy_trace
          (T.MsgSent (D.flatten symbolic_packet));
      network =
        L.append state.network [{ symbolic_packet; send_position }];
  }

let record_receive
  (state:model)
  (who:E.endpoint_id)
  (packet_index:nat)
  : model
  =
  match lookup state.endpoints who, lookup state.network packet_index with
  | Some shadow, Some packet ->
    put_endpoint state who
      { shadow with last_received = Some packet.symbolic_packet }
  | _, _ -> state

let record_compromise
  (state:model)
  (who:E.endpoint_id)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    { state with
        dy_trace =
          append_entry state.dy_trace
            (T.Corrupt
              shadow.state_position) }

noextract
let history_interpreter
  : I.interpreter message scalar SM.semantic_event model
  =
  {
    I.initial_model = initial_model;
    I.generated = fresh_generated;
    I.protocol_effect = protocol_effect;
    I.sent = record_send;
    I.received =
      (fun state who packet_index _ -> record_receive state who packet_index);
    I.injected = record_injection;
    I.compromised = record_compromise;
  }

let interpret_history
  (history:list (S.system_effect message scalar SM.semantic_event))
  : model
  =
  I.interpret_history history_interpreter history

let dy_trace_of_history
  (history:list (S.system_effect message scalar SM.semantic_event))
  : TB.trace
  =
  (interpret_history history).dy_trace

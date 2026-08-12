module NSL.Sample.DY.Model

(**
  Direct interpretation of canonical NSL history.  This is a fold over generic
  system effects, not a second protocol state machine.
 *)

module E = Common.Protocol.Labelled
module S = Common.Protocol.System
module I = Common.Protocol.Interpretation
module SM = NSL.Sample.StateMachine
module D = NSL.Sample.DY.Terms
module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module TB = DY.Core.Trace.Base
module T = DY.Core.Trace.Type
module L = FStar.List.Tot

open NSL.Sample.Types
open NSL.Sample.Wire

noeq
type symbolic_plaintext =
  | SymbolicPlaintext1:
      initiator_nonce:BT.bytes ->
      initiator:BT.bytes ->
      symbolic_plaintext
  | SymbolicPlaintext2:
      initiator_nonce:BT.bytes ->
      responder_nonce:BT.bytes ->
      responder:BT.bytes ->
      symbolic_plaintext
  | SymbolicPlaintext3:
      responder_nonce:BT.bytes ->
      symbolic_plaintext

let flatten_plaintext (value:symbolic_plaintext) : BT.bytes =
  match value with
  | SymbolicPlaintext1 initiator_nonce initiator ->
    D.plaintext1_term initiator_nonce initiator
  | SymbolicPlaintext2 initiator_nonce responder_nonce responder ->
    D.plaintext2_term initiator_nonce responder_nonce responder
  | SymbolicPlaintext3 responder_nonce ->
    D.plaintext3_term responder_nonce

noeq
type symbolic_message =
  | SymbolicEncrypted:
      ciphertext:BT.bytes ->
      plaintext:option symbolic_plaintext ->
      symbolic_message

let flatten_message (value:symbolic_message) : BT.bytes =
  match value with
  | SymbolicEncrypted ciphertext _ -> ciphertext

noeq
type endpoint_shadow = {
  secret_key: BT.bytes;
  pending_nonce: option BT.bytes;
  pending_randomness: option BT.bytes;
  initiator_nonce: option BT.bytes;
  responder_nonce: option BT.bytes;
  peer: option BT.bytes;
  pending_ciphertext: option BT.bytes;
  pending_plaintext: option symbolic_plaintext;
  last_received: option symbolic_message;
  state_position: nat;
}

noeq
type network_shadow = {
  symbolic_packet: symbolic_message;
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
    if index = 0 then Some head else lookup tail (index - 1)

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
    shadow.secret_key
    shadow.pending_nonce
    shadow.pending_randomness
    shadow.initiator_nonce
    shadow.responder_nonce

let initial_shadow
  (secret_key:BT.bytes)
  (state_position:nat)
  : endpoint_shadow
  =
  {
    secret_key;
    pending_nonce = None;
    pending_randomness = None;
    initiator_nonce = None;
    responder_nonce = None;
    peer = None;
    pending_ciphertext = None;
    pending_plaintext = None;
    last_received = None;
    state_position;
  }

let empty_snapshot (secret_key:BT.bytes) : BT.bytes =
  D.snapshot secret_key None None None None

let initial_trace : TB.trace =
  let initiator_key = D.key_term 0 in
  let responder_key = D.key_term 2 in
  let trace0 = TB.empty_trace in
  let trace1 =
    append_entry trace0
      (T.RandGen
        D.initiator_key_usage
        (D.role_label SM.initiator_endpoint)
        D.key_length)
  in
  let trace2 =
    append_entry trace1
      (T.SetState
        D.initiator_dy_principal
        (D.role_state_id SM.initiator_endpoint)
        (empty_snapshot initiator_key))
  in
  let trace3 =
    append_entry trace2
      (T.RandGen
        D.responder_key_usage
        (D.role_label SM.responder_endpoint)
        D.key_length)
  in
  append_entry trace3
    (T.SetState
      D.responder_dy_principal
      (D.role_state_id SM.responder_endpoint)
      (empty_snapshot responder_key))

let initial_model : model = {
  dy_trace = initial_trace;
  endpoints = [
    initial_shadow (D.key_term 0) 1;
    initial_shadow (D.key_term 2) 3;
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
  (value:fresh_value)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    let fresh_position = TB.trace_length state.dy_trace in
    let generated_term, usage, length =
      match value with
      | FreshNonce _ ->
        D.protocol_nonce_term fresh_position,
        D.protocol_nonce_usage,
        D.protocol_nonce_length
      | FreshRandomness _ ->
        D.encryption_nonce_term fresh_position,
        D.encryption_nonce_usage,
        D.encryption_nonce_length
    in
    let generated_trace =
      append_entry state.dy_trace
        (T.RandGen usage
          (match value with
           | FreshNonce _ -> D.session_label
           | FreshRandomness _ -> D.role_label who)
          length)
    in
    let shadow1 =
      match value with
      | FreshNonce _ ->
        { shadow with
            pending_nonce = Some generated_term;
            state_position = fresh_position + 1; }
      | FreshRandomness _ ->
        { shadow with
            pending_randomness = Some generated_term;
            state_position = fresh_position + 1; }
    in
    let trace1 =
      append_entry generated_trace
        (T.SetState
          (D.role_principal who)
          (D.role_state_id who)
          (endpoint_snapshot shadow1))
    in
    put_endpoint { state with dy_trace = trace1 } who shadow1

let received_plaintext
  (shadow:endpoint_shadow)
  : option symbolic_plaintext
  =
  match shadow.last_received with
  | Some (SymbolicEncrypted _ plaintext) -> plaintext
  | None -> None

let nonce_from_received
  (shadow:endpoint_shadow)
  (fallback:nonce)
  : BT.bytes
  =
  match received_plaintext shadow with
  | Some (SymbolicPlaintext1 initiator_nonce _) -> initiator_nonce
  | Some (SymbolicPlaintext2 _ responder_nonce _) -> responder_nonce
  | Some (SymbolicPlaintext3 responder_nonce) -> responder_nonce
  | None -> D.nonce_literal fallback

let plaintext_term
  (shadow:endpoint_shadow)
  (plaintext:plaintext)
  : symbolic_plaintext
  =
  match plaintext with
  | PlainMessage1 initiator_nonce initiator ->
    let symbolic_nonce =
      match shadow.pending_nonce with
      | Some nonce -> nonce
      | None -> D.nonce_literal initiator_nonce
    in
    SymbolicPlaintext1 symbolic_nonce (D.principal_term initiator)
  | PlainMessage2 initiator_nonce responder_nonce responder ->
    let symbolic_initiator_nonce =
      match shadow.initiator_nonce with
      | Some nonce -> nonce
      | None ->
        (match received_plaintext shadow with
         | Some (SymbolicPlaintext1 nonce _) -> nonce
         | _ -> D.nonce_literal initiator_nonce)
    in
    let symbolic_responder_nonce =
      match shadow.pending_nonce with
      | Some nonce -> nonce
      | None -> D.nonce_literal responder_nonce
    in
    SymbolicPlaintext2
      symbolic_initiator_nonce
      symbolic_responder_nonce
      (D.principal_term responder)
  | PlainMessage3 responder_nonce ->
    let symbolic_responder_nonce =
      match shadow.responder_nonce with
      | Some nonce -> nonce
      | None -> nonce_from_received shadow responder_nonce
    in
    SymbolicPlaintext3 symbolic_responder_nonce

let accepted_plaintext_term
  (shadow:endpoint_shadow)
  (plaintext:plaintext)
  : symbolic_plaintext
  =
  match plaintext with
  | PlainMessage1 initiator_nonce initiator ->
    SymbolicPlaintext1
      (D.nonce_literal initiator_nonce)
      (D.principal_term initiator)
  | PlainMessage2 initiator_nonce responder_nonce responder ->
    let symbolic_initiator_nonce =
      match shadow.initiator_nonce with
      | Some nonce -> nonce
      | None -> D.nonce_literal initiator_nonce
    in
    SymbolicPlaintext2
      symbolic_initiator_nonce
      (D.nonce_literal responder_nonce)
      (D.principal_term responder)
  | PlainMessage3 responder_nonce ->
    let symbolic_responder_nonce =
      match shadow.responder_nonce with
      | Some nonce -> nonce
      | None -> D.nonce_literal responder_nonce
    in
    SymbolicPlaintext3 symbolic_responder_nonce

let remember_created_plaintext
  (shadow:endpoint_shadow)
  (plaintext:symbolic_plaintext)
  : endpoint_shadow
  =
  match plaintext with
  | SymbolicPlaintext1 initiator_nonce _ ->
    { shadow with initiator_nonce = Some initiator_nonce }
  | SymbolicPlaintext2 initiator_nonce responder_nonce _ ->
    { shadow with
        initiator_nonce = Some initiator_nonce;
        responder_nonce = Some responder_nonce; }
  | SymbolicPlaintext3 responder_nonce ->
    { shadow with responder_nonce = Some responder_nonce }

let endpoint_recipient_public_key
  (recipient:SM.recipient_key)
  : option BT.bytes
  =
  match recipient with
  | SM.EndpointKey endpoint ->
    if endpoint = SM.initiator_endpoint
    then Some (D.role_public_key SM.initiator_endpoint)
    else if endpoint = SM.responder_endpoint
    then Some (D.role_public_key SM.responder_endpoint)
    else None
  | SM.ExternalKey _ -> None

let encryption_tag
  (plaintext:symbolic_plaintext)
  : string
  =
  match plaintext with
  | SymbolicPlaintext1 _ _ -> D.tag_message1
  | SymbolicPlaintext2 _ _ _ -> D.tag_message2
  | SymbolicPlaintext3 _ -> D.tag_message3

(**
  A genuine authorized encryption is produced only for an honest
  configured-recipient triple, i.e. a (creator, message, recipient key) that the
  protocol PKE authorization predicate actually permits:

      initiator -> responder key : Message1, Message3
      responder -> initiator/responder key : Message2

  Any other configured-recipient creation is treated as attacker material (a
  public literal), and external-recipient creations remain literals as before.
  This mirrors [Profile.pke_authorized] and keeps the honest flow unchanged
  (every canonical protocol step is authorized).
 *)
let authorized_recipient_key
  (who:E.endpoint_id)
  (recipient:SM.recipient_key)
  (plaintext:plaintext)
  : option BT.bytes
  =
  match recipient, plaintext with
  | SM.EndpointKey endpoint, PlainMessage1 _ _
  | SM.EndpointKey endpoint, PlainMessage3 _ ->
    if who = SM.initiator_endpoint && endpoint = SM.responder_endpoint
    then Some (D.role_public_key SM.responder_endpoint)
    else None
  | SM.EndpointKey endpoint, PlainMessage2 _ _ _ ->
    if who = SM.responder_endpoint && endpoint = SM.initiator_endpoint
    then Some (D.role_public_key SM.initiator_endpoint)
    else if who = SM.responder_endpoint && endpoint = SM.responder_endpoint
    then Some (D.role_public_key SM.responder_endpoint)
    else None
  | _, _ -> None

let create_ciphertext
  (state:model)
  (who:E.endpoint_id)
  (recipient:SM.recipient_key)
  (plaintext:plaintext)
  (concrete_ciphertext:ciphertext)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    let symbolic_plaintext = plaintext_term shadow plaintext in
    let flattened_plaintext = flatten_plaintext symbolic_plaintext in
    let shadow1 = remember_created_plaintext shadow symbolic_plaintext in
    match
      authorized_recipient_key who recipient plaintext,
      shadow.pending_randomness
    with
    | Some recipient_key, Some randomness ->
      let trace1 =
        append_entry state.dy_trace
          (T.Event
            (D.role_principal who)
            (encryption_tag symbolic_plaintext)
            flattened_plaintext)
      in
      let symbolic_ciphertext =
        D.ciphertext_term recipient_key randomness flattened_plaintext
      in
      put_endpoint
        { state with dy_trace = trace1 }
        who
        { shadow1 with
            pending_ciphertext = Some symbolic_ciphertext;
            pending_plaintext = Some symbolic_plaintext; }
    | _, _ ->
      put_endpoint state who
        { shadow1 with
            pending_ciphertext =
              Some (D.ciphertext_literal concrete_ciphertext);
            pending_plaintext = Some symbolic_plaintext; }

let accepted_ciphertext
  (shadow:endpoint_shadow)
  : option BT.bytes
  =
  match shadow.last_received with
  | Some (SymbolicEncrypted ciphertext _) -> Some ciphertext
  | None -> None

let accept_ciphertext
  (state:model)
  (who:E.endpoint_id)
  (plaintext:plaintext)
  : model
  =
  match lookup state.endpoints who with
  | None -> state
  | Some shadow ->
    let symbolic_plaintext =
      match received_plaintext shadow with
      | Some value -> value
      | None -> accepted_plaintext_term shadow plaintext
    in
    match accepted_ciphertext shadow with
    | None -> state
    | Some ciphertext ->
      let shadow1 =
        match symbolic_plaintext with
        | SymbolicPlaintext1 initiator_nonce initiator ->
          { shadow with
              initiator_nonce = Some initiator_nonce;
              peer = Some initiator; }
        | SymbolicPlaintext2 initiator_nonce responder_nonce responder ->
          { shadow with
              initiator_nonce = Some initiator_nonce;
              responder_nonce = Some responder_nonce;
              peer = Some responder; }
        | SymbolicPlaintext3 responder_nonce ->
          { shadow with responder_nonce = Some responder_nonce }
      in
      let event_position = TB.trace_length state.dy_trace in
      let trace1 =
        append_entry state.dy_trace
          (T.Event
            (D.role_principal who)
            D.tag_accepted
            (D.accepted_content
              ciphertext
              (flatten_plaintext symbolic_plaintext)))
      in
      let shadow2 = {
        shadow1 with state_position = event_position + 1;
      } in
      let trace2 =
        append_entry trace1
          (T.SetState
            (D.role_principal who)
            (D.role_state_id who)
            (endpoint_snapshot shadow2))
      in
      put_endpoint { state with dy_trace = trace2 } who shadow2

let record_completion
  (state:model)
  (who:E.endpoint_id)
  (peer:principal)
  : model
  =
  match lookup state.endpoints who with
  | Some shadow ->
    (match shadow.initiator_nonce, shadow.responder_nonce with
     | Some initiator_nonce, Some responder_nonce ->
       { state with
           dy_trace =
             append_entry state.dy_trace
               (T.Event
                 (D.role_principal who)
                 D.tag_complete
                 (D.session_content
                   (D.principal_term peer)
                   initiator_nonce responder_nonce)) }
     | _, _ -> state)
  | None -> state

let protocol_effect
  (state:model)
  (who:E.endpoint_id)
  (event:SM.semantic_event)
  : model
  =
  match event with
  | SM.CiphertextCreated _ _ recipient plaintext _ result ->
    create_ciphertext state who recipient plaintext result
  | SM.CiphertextAccepted _ plaintext _ ->
    accept_ciphertext state who plaintext
  | SM.Completed peer _ _ ->
    record_completion state who peer

let honest_message
  (state:model)
  (who:E.endpoint_id)
  (message:message)
  : symbolic_message
  =
  match lookup state.endpoints who with
  | Some shadow ->
    (match shadow.pending_ciphertext, shadow.pending_plaintext with
     | Some ciphertext, Some plaintext ->
       SymbolicEncrypted ciphertext (Some plaintext)
     | _, _ ->
       match message with
       | Encrypted ciphertext ->
         SymbolicEncrypted (D.ciphertext_literal ciphertext) None)
  | None ->
    match message with
    | Encrypted ciphertext ->
      SymbolicEncrypted (D.ciphertext_literal ciphertext) None

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
          (T.MsgSent (flatten_message symbolic_packet));
      network =
        L.append state.network [{ symbolic_packet; send_position }];
  }

let record_injection
  (state:model)
  (_:nat)
  (message:message)
  : model
  =
  let symbolic_packet =
    match message with
    | Encrypted ciphertext ->
      SymbolicEncrypted (D.ciphertext_literal ciphertext) None
  in
  let send_position = TB.trace_length state.dy_trace in
  {
    state with
      dy_trace =
        append_entry state.dy_trace
          (T.MsgSent (flatten_message symbolic_packet));
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
            (T.Corrupt shadow.state_position) }

noextract
let history_interpreter
  : I.interpreter
      message fresh_value SM.semantic_event model
  =
  {
    I.initial_model = initial_model;
    I.generated = fresh_generated;
    I.protocol_effect = protocol_effect;
    I.sent = record_send;
    I.received =
      (fun state who packet_index _ ->
        record_receive state who packet_index);
    I.injected = record_injection;
    I.compromised = record_compromise;
  }

let interpret_history
  (history:
    list (S.system_effect message fresh_value SM.semantic_event))
  : model
  =
  I.interpret_history history_interpreter history

let dy_trace_of_history
  (history:
    list (S.system_effect message fresh_value SM.semantic_event))
  : TB.trace
  =
  (interpret_history history).dy_trace

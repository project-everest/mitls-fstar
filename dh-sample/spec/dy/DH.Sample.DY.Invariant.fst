module DH.Sample.DY.Invariant

(**
  The direct history interpretation satisfies the genuine DY* core trace
  invariant.  The auxiliary model invariant tracks only facts needed to
  discharge DY* entry obligations; it contains no protocol transition relation.
*)

module E = Common.Protocol.Labelled
module S = Common.Protocol.System
module I = Common.Protocol.Interpretation
module SM = DH.Sample.StateMachine
module D = DH.Sample.DY.Terms
module P = DH.Sample.DY.Profile
module M = DH.Sample.DY.Model
module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module LT = DY.Core.Label.Type
module T = DY.Core.Trace.Type
module TB = DY.Core.Trace.Base
module TI = DY.Core.Trace.Invariant
module List = FStar.List.Tot

open DH.Sample.Types
open DH.Sample.Wire

let publishable (trace:TB.trace) (value:BT.bytes) : prop =
  B.is_publishable #P.dh_crypto_invariants trace value

let knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : prop
  =
  B.is_knowable_by #P.dh_crypto_invariants
    (D.role_label who)
    trace
    value

let long_term_recorded
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : prop
  =
  (who == SM.initiator_endpoint /\
    value == D.long_term_term 0 /\
    TB.entry_at trace 0
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.initiator_endpoint)
        D.long_term_length)) \/
  (who == SM.responder_endpoint /\
    value == D.long_term_term 2 /\
    TB.entry_at trace 2
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.responder_endpoint)
        D.long_term_length))

let scalar_recorded
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : prop
  =
  exists (position:nat).
    value == D.ephemeral_term position /\
    TB.entry_at trace position
      (T.RandGen
        D.ephemeral_usage
        (D.role_label who)
        D.ephemeral_length)

let message_valid
  (trace:TB.trace)
  (message:D.symbolic_message)
  : prop
  =
  match message with
  | D.SymbolicMessage1 identity share ->
    publishable trace identity /\
    publishable trace share
  | D.SymbolicMessage2 identity share signature ->
    publishable trace identity /\
    publishable trace share /\
    publishable trace signature
  | D.SymbolicMessage3 signature ->
    publishable trace signature

let optional_publishable
  (trace:TB.trace)
  (value:option BT.bytes)
  : prop
  =
  match value with
  | None -> True
  | Some term -> publishable trace term

let optional_message_valid
  (trace:TB.trace)
  (value:option D.symbolic_message)
  : prop
  =
  match value with
  | None -> True
  | Some message -> message_valid trace message

let private_valid
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:option BT.bytes)
  : prop
  =
  match value with
  | None -> True
  | Some term -> scalar_recorded who trace term

let own_share_valid
  (private_value own_share:option BT.bytes)
  : prop
  =
  match own_share with
  | None -> True
  | Some share ->
    exists (private_term:BT.bytes).
      private_value == Some private_term /\
      share == D.share_term private_term

let peer_share_valid
  (trace:TB.trace)
  (peer_share:option BT.bytes)
  : prop
  =
  optional_publishable trace peer_share

let key_valid
  (private_value peer_share key:option BT.bytes)
  : prop
  =
  match key with
  | None -> True
  | Some key_term ->
    exists (private_term peer_term:BT.bytes).
      private_value == Some private_term /\
      peer_share == Some peer_term /\
      key_term == D.secret_term private_term peer_term

let state_position_valid
  (who:E.endpoint_id)
  (trace:TB.trace)
  (position:nat)
  : prop
  =
  exists (content:BT.bytes).
    TB.entry_at trace position
      (T.SetState
        (D.role_principal who)
        (D.role_state_id who)
        content)

let shadow_valid
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  : prop
  =
  long_term_recorded who trace shadow.M.long_term /\
  private_valid who trace shadow.M.private_value /\
  own_share_valid shadow.M.private_value shadow.M.own_share /\
  peer_share_valid trace shadow.M.peer_share /\
  key_valid
    shadow.M.private_value
    shadow.M.peer_share
    shadow.M.key /\
  optional_publishable trace shadow.M.pending_signature /\
  optional_message_valid trace shadow.M.last_received /\
  state_position_valid who trace shadow.M.state_position

let rec network_valid
  (trace:TB.trace)
  (network:list M.network_shadow)
  : prop
  =
  match network with
  | [] -> True
  | packet :: tail ->
    message_valid trace packet.M.symbolic_packet /\
    TB.entry_at trace packet.M.send_position
      (T.MsgSent (D.flatten packet.M.symbolic_packet)) /\
    network_valid trace tail

let model_invariant (state:M.model) : prop =
  TI.trace_invariant #P.dh_protocol_invariants state.M.dy_trace /\
  (exists (initiator responder:M.endpoint_shadow).
    state.M.endpoints == [ initiator; responder ] /\
    shadow_valid
      SM.initiator_endpoint state.M.dy_trace initiator /\
    shadow_valid
      SM.responder_endpoint state.M.dy_trace responder) /\
  network_valid state.M.dy_trace state.M.network

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let trace_invariant_snoc
  (trace:TB.trace)
  (entry:TB.trace_entry)
  : Lemma
      (requires
        TI.trace_invariant #P.dh_protocol_invariants trace /\
        TI.trace_entry_invariant
          #P.dh_protocol_invariants trace entry)
      (ensures
        TI.trace_invariant #P.dh_protocol_invariants
          (TB.append_entry trace entry))
  =
  reveal_opaque
    (`%TI.trace_invariant)
    (TI.trace_invariant #P.dh_protocol_invariants)

let publishable_later
  (trace0 trace1:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires
        publishable trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures publishable trace1 value)
  =
  B.bytes_invariant_later
    #P.dh_crypto_invariants trace0 trace1 value;
  B.bytes_invariant_implies_well_formed
    #P.dh_crypto_invariants trace0 value;
  B.get_label_later #P.dh_crypto_usages trace0 trace1 value;
  L.can_flow_later trace0 trace1
    (B.get_label #P.dh_crypto_usages trace0 value)
    L.public

let message_valid_implies_flatten_publishable
  (trace:TB.trace)
  (message:D.symbolic_message)
  : Lemma
      (requires message_valid trace message)
      (ensures publishable trace (D.flatten message))
  =
  match message with
  | D.SymbolicMessage1 identity share ->
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace identity share
  | D.SymbolicMessage2 identity share signature ->
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace share signature;
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace identity
      (B.concat share signature)
  | D.SymbolicMessage3 _ -> ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let rand_usage_and_label
  (trace:TB.trace)
  (usage:BT.usage)
  (label:LT.label)
  (length:nat{length <> 0})
  (position:nat)
  : Lemma
      (requires
        TB.entry_at trace position
          (T.RandGen usage label length))
      (ensures
        B.get_usage #P.dh_crypto_usages trace
          (BT.Rand length position) == usage /\
        B.get_label #P.dh_crypto_usages trace
          (BT.Rand length position) == label /\
        B.has_usage #P.dh_crypto_usages trace
          (BT.Rand length position) usage)
  =
  reveal_opaque (`%B.get_usage) (B.get_usage #P.dh_crypto_usages);
  reveal_opaque (`%B.get_label) (B.get_label #P.dh_crypto_usages);
  reveal_opaque (`%B.has_usage) (B.has_usage #P.dh_crypto_usages)

let scalar_facts
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires scalar_recorded who trace value)
      (ensures
        B.bytes_invariant #P.dh_crypto_invariants trace value /\
        B.get_label #P.dh_crypto_usages trace value ==
          D.role_label who /\
        B.has_usage #P.dh_crypto_usages trace value
          D.ephemeral_usage)
  =
  eliminate
    exists (position:nat).
      value == D.ephemeral_term position /\
      TB.entry_at trace position
        (T.RandGen
          D.ephemeral_usage
          (D.role_label who)
          D.ephemeral_length)
  returns
    B.bytes_invariant #P.dh_crypto_invariants trace value /\
    B.get_label #P.dh_crypto_usages trace value ==
      D.role_label who /\
    B.has_usage #P.dh_crypto_usages trace value
      D.ephemeral_usage
  with _.
    (reveal_opaque
       (`%B.bytes_invariant)
       (B.bytes_invariant #P.dh_crypto_invariants);
     introduce
       exists (usage:BT.usage) (label:LT.label).
         TB.entry_at trace position
           (T.RandGen usage label D.ephemeral_length)
       with D.ephemeral_usage (D.role_label who) and ();
     rand_usage_and_label trace
       D.ephemeral_usage
       (D.role_label who)
       D.ephemeral_length
       position)

let share_publishable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (private_value:BT.bytes)
  : Lemma
      (requires scalar_recorded who trace private_value)
      (ensures
        publishable trace (D.share_term private_value))
  =
  scalar_facts who trace private_value
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let public_is_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires publishable trace value)
      (ensures knowable who trace value)
  =
  L.public_is_top trace (D.role_label who);
  L.can_flow_transitive trace
    (B.get_label #P.dh_crypto_usages trace value)
    L.public
    (D.role_label who)

let join_flows_left
  (trace:TB.trace)
  (left right:LT.label)
  : Lemma
      (ensures
        L.can_flow trace (L.join left right) left)
  =
  L.intro_can_flow trace (L.join left right) left
    (fun later -> L.is_corrupt_join later left right)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let long_term_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires long_term_recorded who trace value)
      (ensures knowable who trace value)
  =
  eliminate
    (who == SM.initiator_endpoint /\
      value == D.long_term_term 0 /\
      TB.entry_at trace 0
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.initiator_endpoint)
          D.long_term_length)) \/
    (who == SM.responder_endpoint /\
      value == D.long_term_term 2 /\
      TB.entry_at trace 2
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.responder_endpoint)
          D.long_term_length))
  returns knowable who trace value
  with _.
    (reveal_opaque
       (`%B.bytes_invariant)
       (B.bytes_invariant #P.dh_crypto_invariants);
     introduce
       exists (usage:BT.usage) (label:LT.label).
         TB.entry_at trace 0
           (T.RandGen usage label D.long_term_length)
       with D.long_term_usage
         (D.role_label SM.initiator_endpoint) and ();
     rand_usage_and_label trace
       D.long_term_usage
       (D.role_label SM.initiator_endpoint)
       D.long_term_length
       0)
  and _.
    (reveal_opaque
       (`%B.bytes_invariant)
       (B.bytes_invariant #P.dh_crypto_invariants);
     introduce
       exists (usage:BT.usage) (label:LT.label).
         TB.entry_at trace 2
           (T.RandGen usage label D.long_term_length)
       with D.long_term_usage
         (D.role_label SM.responder_endpoint) and ();
     rand_usage_and_label trace
       D.long_term_usage
       (D.role_label SM.responder_endpoint)
       D.long_term_length
       2)

let long_term_facts
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires long_term_recorded who trace value)
      (ensures
        B.bytes_invariant #P.dh_crypto_invariants trace value /\
        B.get_label #P.dh_crypto_usages trace value ==
          D.role_label who /\
        B.has_usage #P.dh_crypto_usages trace value
          D.long_term_usage)
  =
  eliminate
    (who == SM.initiator_endpoint /\
      value == D.long_term_term 0 /\
      TB.entry_at trace 0
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.initiator_endpoint)
          D.long_term_length)) \/
    (who == SM.responder_endpoint /\
      value == D.long_term_term 2 /\
      TB.entry_at trace 2
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.responder_endpoint)
          D.long_term_length))
  returns
    B.bytes_invariant #P.dh_crypto_invariants trace value /\
    B.get_label #P.dh_crypto_usages trace value ==
      D.role_label who /\
    B.has_usage #P.dh_crypto_usages trace value
      D.long_term_usage
  with _.
    (reveal_opaque
       (`%B.bytes_invariant)
       (B.bytes_invariant #P.dh_crypto_invariants);
     introduce
       exists (usage:BT.usage) (label:LT.label).
         TB.entry_at trace 0
           (T.RandGen usage label D.long_term_length)
       with D.long_term_usage
         (D.role_label SM.initiator_endpoint) and ();
     rand_usage_and_label trace
       D.long_term_usage
       (D.role_label SM.initiator_endpoint)
       D.long_term_length
       0)
  and _.
    (reveal_opaque
       (`%B.bytes_invariant)
       (B.bytes_invariant #P.dh_crypto_invariants);
     introduce
       exists (usage:BT.usage) (label:LT.label).
         TB.entry_at trace 2
           (T.RandGen usage label D.long_term_length)
       with D.long_term_usage
         (D.role_label SM.responder_endpoint) and ();
     rand_usage_and_label trace
       D.long_term_usage
       (D.role_label SM.responder_endpoint)
       D.long_term_length
       2)

let scalar_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires scalar_recorded who trace value)
      (ensures knowable who trace value)
  =
  scalar_facts who trace value

let key_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (private_value peer_share:BT.bytes)
  : Lemma
      (requires
        scalar_recorded who trace private_value /\
        publishable trace peer_share)
      (ensures
        knowable who trace
          (D.secret_term private_value peer_share))
  =
  scalar_facts who trace private_value;
  B.bytes_invariant_dh
    #P.dh_crypto_invariants
    trace private_value D.ephemeral_usage peer_share;
  B.get_label_dh
    #P.dh_crypto_usages trace private_value peer_share;
  join_flows_left trace
    (D.role_label who)
    (B.get_dh_label #P.dh_crypto_usages trace peer_share)
#pop-options

let optional_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:option BT.bytes)
  : prop
  =
  match value with
  | None -> True
  | Some term -> knowable who trace term

let shadow_material_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  : prop
  =
  knowable who trace shadow.M.long_term /\
  optional_knowable who trace shadow.M.private_value /\
  optional_knowable who trace shadow.M.own_share /\
  optional_knowable who trace shadow.M.peer_share /\
  optional_knowable who trace shadow.M.key

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"
let optional_term_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (value:option BT.bytes)
  : Lemma
      (requires optional_knowable who trace value)
      (ensures knowable who trace (D.optional_term value))
  =
  match value with
  | None ->
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace
      (FStar.Seq.empty #FStar.UInt8.t);
    public_is_knowable who trace D.empty_data
  | Some _ -> ()

let snapshot_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  : Lemma
      (requires shadow_material_knowable who trace shadow)
      (ensures
        P.state_predicate trace
          (D.role_principal who)
          (D.role_state_id who)
          (M.endpoint_snapshot shadow))
  =
  optional_term_knowable who trace shadow.M.private_value;
  optional_term_knowable who trace shadow.M.own_share;
  optional_term_knowable who trace shadow.M.peer_share;
  optional_term_knowable who trace shadow.M.key
#pop-options

let state_invariant
  (state:M.model)
  : prop
  =
  TI.trace_invariant
    #P.dh_protocol_invariants state.M.dy_trace

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let long_term_recorded_later
  (who:E.endpoint_id)
  (trace0 trace1:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires
        long_term_recorded who trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures long_term_recorded who trace1 value)
  =
  eliminate
    (who == SM.initiator_endpoint /\
      value == D.long_term_term 0 /\
      TB.entry_at trace0 0
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.initiator_endpoint)
          D.long_term_length)) \/
    (who == SM.responder_endpoint /\
      value == D.long_term_term 2 /\
      TB.entry_at trace0 2
        (T.RandGen
          D.long_term_usage
          (D.role_label SM.responder_endpoint)
          D.long_term_length))
  returns long_term_recorded who trace1 value
  with _.
    TB.entry_at_grows trace0 trace1 0
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.initiator_endpoint)
        D.long_term_length)
  and _.
    TB.entry_at_grows trace0 trace1 2
      (T.RandGen
        D.long_term_usage
        (D.role_label SM.responder_endpoint)
        D.long_term_length)

let scalar_recorded_later
  (who:E.endpoint_id)
  (trace0 trace1:TB.trace)
  (value:BT.bytes)
  : Lemma
      (requires
        scalar_recorded who trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures scalar_recorded who trace1 value)
  =
  eliminate
    exists (position:nat).
      value == D.ephemeral_term position /\
      TB.entry_at trace0 position
        (T.RandGen
          D.ephemeral_usage
          (D.role_label who)
          D.ephemeral_length)
  returns scalar_recorded who trace1 value
  with _.
    (TB.entry_at_grows trace0 trace1 position
       (T.RandGen
         D.ephemeral_usage
         (D.role_label who)
         D.ephemeral_length);
     introduce
       exists (later_position:nat).
         value == D.ephemeral_term later_position /\
         TB.entry_at trace1 later_position
           (T.RandGen
             D.ephemeral_usage
             (D.role_label who)
             D.ephemeral_length)
       with position and ())

let message_valid_later
  (trace0 trace1:TB.trace)
  (message:D.symbolic_message)
  : Lemma
      (requires
        message_valid trace0 message /\
        trace0 `TB.grows` trace1)
      (ensures message_valid trace1 message)
  =
  match message with
  | D.SymbolicMessage1 identity share ->
    publishable_later trace0 trace1 identity;
    publishable_later trace0 trace1 share
  | D.SymbolicMessage2 identity share signature ->
    publishable_later trace0 trace1 identity;
    publishable_later trace0 trace1 share;
    publishable_later trace0 trace1 signature
  | D.SymbolicMessage3 signature ->
    publishable_later trace0 trace1 signature

let optional_publishable_later
  (trace0 trace1:TB.trace)
  (value:option BT.bytes)
  : Lemma
      (requires
        optional_publishable trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures optional_publishable trace1 value)
  =
  match value with
  | None -> ()
  | Some term -> publishable_later trace0 trace1 term

let optional_message_valid_later
  (trace0 trace1:TB.trace)
  (value:option D.symbolic_message)
  : Lemma
      (requires
        optional_message_valid trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures optional_message_valid trace1 value)
  =
  match value with
  | None -> ()
  | Some message -> message_valid_later trace0 trace1 message

let private_valid_later
  (who:E.endpoint_id)
  (trace0 trace1:TB.trace)
  (value:option BT.bytes)
  : Lemma
      (requires
        private_valid who trace0 value /\
        trace0 `TB.grows` trace1)
      (ensures private_valid who trace1 value)
  =
  match value with
  | None -> ()
  | Some term ->
    scalar_recorded_later who trace0 trace1 term

let state_position_valid_later
  (who:E.endpoint_id)
  (trace0 trace1:TB.trace)
  (position:nat)
  : Lemma
      (requires
        state_position_valid who trace0 position /\
        trace0 `TB.grows` trace1)
      (ensures state_position_valid who trace1 position)
  =
  eliminate
    exists (content:BT.bytes).
      TB.entry_at trace0 position
        (T.SetState
          (D.role_principal who)
          (D.role_state_id who)
          content)
  returns state_position_valid who trace1 position
  with _.
    (TB.entry_at_grows trace0 trace1 position
       (T.SetState
         (D.role_principal who)
         (D.role_state_id who)
         content);
     introduce
       exists (later_content:BT.bytes).
         TB.entry_at trace1 position
           (T.SetState
             (D.role_principal who)
             (D.role_state_id who)
             later_content)
       with content and ())

let shadow_valid_later
  (who:E.endpoint_id)
  (trace0 trace1:TB.trace)
  (shadow:M.endpoint_shadow)
  : Lemma
      (requires
        shadow_valid who trace0 shadow /\
        trace0 `TB.grows` trace1)
      (ensures shadow_valid who trace1 shadow)
  =
  long_term_recorded_later
    who trace0 trace1 shadow.M.long_term;
  private_valid_later
    who trace0 trace1 shadow.M.private_value;
  optional_publishable_later
    trace0 trace1 shadow.M.peer_share;
  optional_publishable_later
    trace0 trace1 shadow.M.pending_signature;
  optional_message_valid_later
    trace0 trace1 shadow.M.last_received;
  state_position_valid_later
    who trace0 trace1 shadow.M.state_position

let rec network_valid_later
  (trace0 trace1:TB.trace)
  (network:list M.network_shadow)
  : Lemma
      (requires
        network_valid trace0 network /\
        trace0 `TB.grows` trace1)
      (ensures network_valid trace1 network)
      (decreases network)
  =
  match network with
  | [] -> ()
  | packet :: tail ->
    message_valid_later
      trace0 trace1 packet.M.symbolic_packet;
    TB.entry_at_grows trace0 trace1 packet.M.send_position
      (T.MsgSent (D.flatten packet.M.symbolic_packet));
    network_valid_later trace0 trace1 tail
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec network_valid_append
  (trace:TB.trace)
  (network:list M.network_shadow)
  (packet:M.network_shadow)
  : Lemma
      (requires
        network_valid trace network /\
        message_valid trace packet.M.symbolic_packet /\
        TB.entry_at trace packet.M.send_position
          (T.MsgSent (D.flatten packet.M.symbolic_packet)))
      (ensures
        network_valid trace
          (List.append network [ packet ]))
      (decreases network)
  =
  match network with
  | [] -> ()
  | head :: tail ->
    network_valid_append trace tail packet
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let injected_message_valid
  (trace:TB.trace)
  (message:message)
  : Lemma
      (ensures
        message_valid trace (D.injected_message message))
  =
  match message with
  | Message1 initiator initiator_share ->
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace initiator;
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace initiator_share
  | Message2 responder responder_share signature ->
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace responder;
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace responder_share;
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace signature
  | Message3 signature ->
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace signature

let own_share_publishable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  (share:BT.bytes)
  : Lemma
      (requires
        shadow_valid who trace shadow /\
        shadow.M.own_share == Some share)
      (ensures publishable trace share)
  =
  eliminate
    exists (private_value:BT.bytes).
      shadow.M.private_value == Some private_value /\
      share == D.share_term private_value
  returns publishable trace share
  with _.
    share_publishable who trace private_value

let protocol_transcript_publishable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  (partner:principal)
  (transcript:BT.bytes)
  : Lemma
      (requires
        shadow_valid who trace shadow /\
        M.protocol_transcript who shadow partner ==
          Some transcript)
      (ensures publishable trace transcript)
  =
  match shadow.M.own_share, shadow.M.peer_share with
  | Some own_share, Some peer_share ->
    own_share_publishable who trace shadow own_share;
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace partner;
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace own_share peer_share;
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace
      (D.principal_term partner)
      (B.concat own_share peer_share);
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace peer_share own_share;
    B.concat_preserves_publishability
      #P.dh_crypto_invariants trace
      (D.principal_term partner)
      (B.concat peer_share own_share)
  | _, _ -> ()

let honest_message_with_shadow_valid
  (trace:TB.trace)
  (who:E.endpoint_id)
  (shadow:M.endpoint_shadow)
  (message:message)
  : Lemma
      (requires shadow_valid who trace shadow)
      (ensures
        message_valid trace
          (match message with
           | Message1 identity initiator_share ->
             (match shadow.M.own_share with
              | Some own_share ->
                D.SymbolicMessage1
                  (D.principal_term identity)
                  own_share
              | None -> D.injected_message message)
           | Message2 identity responder_share responder_signature ->
             (match
                shadow.M.own_share,
                shadow.M.pending_signature
              with
              | Some own_share, Some signature ->
                D.SymbolicMessage2
                  (D.principal_term identity)
                  own_share
                  signature
              | _, _ -> D.injected_message message)
           | Message3 initiator_signature ->
             (match shadow.M.pending_signature with
              | Some signature ->
                D.SymbolicMessage3 signature
              | None -> D.injected_message message)))
  =
  match message with
  | Message1 identity _ ->
    (match shadow.M.own_share with
     | Some share ->
       B.literal_to_bytes_is_publishable
         #P.dh_crypto_invariants trace identity;
       own_share_publishable who trace shadow share
     | None -> injected_message_valid trace message)
  | Message2 identity _ _ ->
    (match shadow.M.own_share, shadow.M.pending_signature with
     | Some share, Some _ ->
       B.literal_to_bytes_is_publishable
         #P.dh_crypto_invariants trace identity;
       own_share_publishable who trace shadow share
     | _, _ -> injected_message_valid trace message)
  | Message3 _ ->
    (match shadow.M.pending_signature with
     | Some _ -> ()
     | None -> injected_message_valid trace message)

let honest_message_valid
  (state:M.model)
  (who:E.endpoint_id)
  (message:message)
  : Lemma
      (requires model_invariant state)
      (ensures
        message_valid state.M.dy_trace
          (M.honest_message state who message))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    message_valid state.M.dy_trace
      (M.honest_message state who message)
  with _.
    (match who with
     | 0 ->
       honest_message_with_shadow_valid
         state.M.dy_trace
         SM.initiator_endpoint
         initiator
         message
     | 1 ->
       honest_message_with_shadow_valid
         state.M.dy_trace
         SM.responder_endpoint
         responder
         message
     | _ ->
       injected_message_valid state.M.dy_trace message)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let signature_publishable
  (trace:TB.trace)
  (who:E.endpoint_id)
  (long_term nonce transcript:BT.bytes)
  (nonce_position:nat)
  : Lemma
      (requires
        long_term_recorded who trace long_term /\
        nonce == D.signing_nonce_term nonce_position /\
        TB.entry_at trace nonce_position
          (T.RandGen
            D.signing_nonce_usage
            (D.role_label who)
            D.signing_nonce_length) /\
        ((who == SM.initiator_endpoint /\
          TB.event_triggered trace
            D.initiator_dy_principal
            D.tag_authorize_initiator
            transcript) \/
         (who == SM.responder_endpoint /\
          TB.event_triggered trace
            D.responder_dy_principal
            D.tag_authorize_responder
            transcript)) /\
        publishable trace transcript)
      (ensures
        publishable trace
          (D.signature_term long_term nonce transcript))
  =
  long_term_facts who trace long_term;
  rand_usage_and_label trace
    D.signing_nonce_usage
    (D.role_label who)
    D.signing_nonce_length
    nonce_position;
  reveal_opaque
    (`%B.bytes_invariant)
    (B.bytes_invariant #P.dh_crypto_invariants);
  eliminate
    (who == SM.initiator_endpoint /\
      TB.event_triggered trace
        D.initiator_dy_principal
        D.tag_authorize_initiator
        transcript) \/
    (who == SM.responder_endpoint /\
      TB.event_triggered trace
        D.responder_dy_principal
        D.tag_authorize_responder
        transcript)
  returns
    publishable trace
      (D.signature_term long_term nonce transcript)
  with _.
    (assert (
       P.sign_predicate trace
         D.long_term_usage
         (D.verification_key_term long_term)
         transcript);
     assert (
       B.bytes_invariant #P.dh_crypto_invariants trace
         (D.signature_term long_term nonce transcript)))
  and _.
    (assert (
       P.sign_predicate trace
         D.long_term_usage
         (D.verification_key_term long_term)
         transcript);
     assert (
       B.bytes_invariant #P.dh_crypto_invariants trace
         (D.signature_term long_term nonce transcript)))
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let initial_model_invariant ()
  : Lemma (ensures model_invariant M.initial_model)
  =
  let e0 =
    T.RandGen
      D.long_term_usage
      (D.role_label SM.initiator_endpoint)
      D.long_term_length
  in
  let tr0 = TB.empty_trace in
  let tr1 = TB.append_entry tr0 e0 in
  reveal_opaque
    (`%TI.trace_invariant)
    (TI.trace_invariant #P.dh_protocol_invariants);
  assert (
    TI.trace_invariant #P.dh_protocol_invariants tr1);
  let initiator = M.initial_shadow (D.long_term_term 0) 1 in
  assert (
    long_term_recorded
      SM.initiator_endpoint tr1 initiator.M.long_term);
  long_term_knowable
    SM.initiator_endpoint tr1 initiator.M.long_term;
  snapshot_knowable SM.initiator_endpoint tr1 initiator;
  let e1 =
    T.SetState
      D.initiator_dy_principal
      (D.role_state_id SM.initiator_endpoint)
      (M.endpoint_snapshot initiator)
  in
  trace_invariant_snoc tr1 e1;
  let tr2 = TB.append_entry tr1 e1 in
  assert (
    state_position_valid
      SM.initiator_endpoint tr2 initiator.M.state_position);
  assert (
    shadow_valid
      SM.initiator_endpoint tr2 initiator);
  let e2 =
    T.RandGen
      D.long_term_usage
      (D.role_label SM.responder_endpoint)
      D.long_term_length
  in
  trace_invariant_snoc tr2 e2;
  let tr3 = TB.append_entry tr2 e2 in
  let responder = M.initial_shadow (D.long_term_term 2) 3 in
  assert (
    long_term_recorded
      SM.responder_endpoint tr3 responder.M.long_term);
  long_term_knowable
    SM.responder_endpoint tr3 responder.M.long_term;
  snapshot_knowable SM.responder_endpoint tr3 responder;
  let e3 =
    T.SetState
      D.responder_dy_principal
      (D.role_state_id SM.responder_endpoint)
      (M.endpoint_snapshot responder)
  in
  trace_invariant_snoc tr3 e3;
  let tr4 = TB.append_entry tr3 e3 in
  assert (
    state_position_valid
      SM.responder_endpoint tr4 responder.M.state_position);
  assert (
    shadow_valid
      SM.responder_endpoint tr4 responder);
  TB.grows_snoc tr0 e0;
  TB.grows_snoc tr1 e1;
  TB.grows_snoc tr2 e2;
  TB.grows_snoc tr3 e3;
  assert (tr1 `TB.grows` tr4);
  assert (tr2 `TB.grows` tr4);
  assert (tr3 `TB.grows` tr4);
  shadow_valid_later
    SM.initiator_endpoint tr2 tr4 initiator;
  introduce
    exists (i r:M.endpoint_shadow).
      M.initial_model.M.endpoints == [ i; r ] /\
      shadow_valid
        SM.initiator_endpoint M.initial_model.M.dy_trace i /\
      shadow_valid
        SM.responder_endpoint M.initial_model.M.dy_trace r
    with initiator responder and ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10 --split_queries always"
let model_trace_snoc
  (state:M.model)
  (entry:TB.trace_entry)
  : Lemma
      (requires
        model_invariant state /\
        TI.trace_entry_invariant
          #P.dh_protocol_invariants state.M.dy_trace entry)
      (ensures
        model_invariant
          { state with
              M.dy_trace =
                TB.append_entry state.M.dy_trace entry })
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant
      { state with
          M.dy_trace =
            TB.append_entry state.M.dy_trace entry }
  with _.
    (let trace1 = TB.append_entry state.M.dy_trace entry in
     trace_invariant_snoc state.M.dy_trace entry;
     TB.grows_snoc state.M.dy_trace entry;
     shadow_valid_later
       SM.initiator_endpoint state.M.dy_trace trace1 initiator;
     shadow_valid_later
       SM.responder_endpoint state.M.dy_trace trace1 responder;
     network_valid_later state.M.dy_trace trace1 state.M.network;
     introduce
       exists (i r:M.endpoint_shadow).
         state.M.endpoints == [ i; r ] /\
         shadow_valid SM.initiator_endpoint trace1 i /\
         shadow_valid SM.responder_endpoint trace1 r
       with initiator responder and ())

let authorization_event_entry
  (trace:TB.trace)
  (who:E.endpoint_id{who == SM.initiator_endpoint \/
                     who == SM.responder_endpoint})
  (transcript:BT.bytes)
  : Lemma
      (requires
        exists (partner gx gy:BT.bytes).
          transcript == D.transcript_term partner gx gy)
      (ensures
        TI.trace_entry_invariant
          #P.dh_protocol_invariants
          trace
          (T.Event
            (D.role_principal who)
            (if who = SM.initiator_endpoint
             then D.tag_authorize_initiator
             else D.tag_authorize_responder)
            transcript))
  =
  eliminate
    exists (partner gx gy:BT.bytes).
      transcript == D.transcript_term partner gx gy
  returns
    TI.trace_entry_invariant
      #P.dh_protocol_invariants
      trace
      (T.Event
        (D.role_principal who)
        (if who = SM.initiator_endpoint
         then D.tag_authorize_initiator
         else D.tag_authorize_responder)
        transcript)
  with _.
    introduce
      exists (p x y:BT.bytes).
        transcript == D.transcript_term p x y
      with partner gx gy and ()

let accepted_event_entry
  (trace:TB.trace)
  (who:E.endpoint_id{who == SM.initiator_endpoint \/
                     who == SM.responder_endpoint})
  (transcript signature:BT.bytes)
  : Lemma
      (ensures
        TI.trace_entry_invariant
          #P.dh_protocol_invariants
          trace
          (T.Event
            (D.role_principal who)
            D.tag_accepted
            (D.accepted_content transcript signature)))
  =
  introduce
    exists (accepted_transcript accepted_signature:BT.bytes).
      D.accepted_content transcript signature ==
        D.accepted_content accepted_transcript accepted_signature
    with transcript signature and ()

let completion_event_entry
  (trace:TB.trace)
  (who:E.endpoint_id{who == SM.initiator_endpoint \/
                     who == SM.responder_endpoint})
  (peer key:BT.bytes)
  : Lemma
      (ensures
        TI.trace_entry_invariant
          #P.dh_protocol_invariants
          trace
          (T.Event
            (D.role_principal who)
            D.tag_complete
            (D.completion_content peer key)))
  =
  introduce
    exists (completed_peer completed_key:BT.bytes).
      D.completion_content peer key ==
        D.completion_content completed_peer completed_key
    with peer key and ()
#pop-options

#push-options "--fuel 3 --ifuel 1 --z3rlimit 10"
let rec network_lookup_valid
  (trace:TB.trace)
  (network:list M.network_shadow)
  (index:nat)
  (packet:M.network_shadow)
  : Lemma
      (requires
        network_valid trace network /\
        M.lookup network index == Some packet)
      (ensures message_valid trace packet.M.symbolic_packet)
      (decreases network)
  =
  match network with
  | [] -> ()
  | head :: tail ->
    if index = 0
    then ()
    else network_lookup_valid trace tail (index - 1) packet
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let sent_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (index:nat)
  (message:message)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_send state who index message))
  =
  let symbolic_packet = M.honest_message state who message in
  honest_message_valid state who message;
  message_valid_implies_flatten_publishable
    state.M.dy_trace symbolic_packet;
  let entry = T.MsgSent (D.flatten symbolic_packet) in
  let trace1 = TB.append_entry state.M.dy_trace entry in
  model_trace_snoc state entry;
  TB.grows_snoc state.M.dy_trace entry;
  message_valid_later
    state.M.dy_trace trace1 symbolic_packet;
  assert (
    TB.entry_at trace1
      (TB.trace_length state.M.dy_trace)
      entry);
  network_valid_append trace1 state.M.network
    {
      M.symbolic_packet = symbolic_packet;
      M.send_position = TB.trace_length state.M.dy_trace;
    }

let injected_preserves
  (state:M.model)
  (index:nat)
  (message:message)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_injection state index message))
  =
  let symbolic_packet = D.injected_message message in
  injected_message_valid state.M.dy_trace message;
  message_valid_implies_flatten_publishable
    state.M.dy_trace symbolic_packet;
  let entry = T.MsgSent (D.flatten symbolic_packet) in
  let trace1 = TB.append_entry state.M.dy_trace entry in
  model_trace_snoc state entry;
  TB.grows_snoc state.M.dy_trace entry;
  message_valid_later
    state.M.dy_trace trace1 symbolic_packet;
  assert (
    TB.entry_at trace1
      (TB.trace_length state.M.dy_trace)
      entry);
  network_valid_append trace1 state.M.network
    {
      M.symbolic_packet = symbolic_packet;
      M.send_position = TB.trace_length state.M.dy_trace;
    }

let compromised_preserves
  (state:M.model)
  (who:E.endpoint_id)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_compromise state who))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant (M.record_compromise state who)
  with _.
    (match who with
     | 0 ->
       model_trace_snoc state
         (T.Corrupt initiator.M.state_position)
     | 1 ->
       model_trace_snoc state
         (T.Corrupt responder.M.state_position)
     | _ -> ())

let received_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (index:nat)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_receive state who index))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant (M.record_receive state who index)
  with _.
    (match M.lookup state.M.network index with
     | None -> ()
     | Some packet ->
       network_lookup_valid
         state.M.dy_trace state.M.network index packet;
       (match who with
        | 0 ->
          introduce
            exists (i r:M.endpoint_shadow).
              (M.record_receive state who index).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint
                state.M.dy_trace i /\
              shadow_valid
                SM.responder_endpoint
                state.M.dy_trace r
            with
              ({ initiator with
                  M.last_received =
                    Some packet.M.symbolic_packet })
              responder
            and ()
        | 1 ->
          introduce
            exists (i r:M.endpoint_shadow).
              (M.record_receive state who index).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint
                state.M.dy_trace i /\
              shadow_valid
                SM.responder_endpoint
                state.M.dy_trace r
            with
              initiator
              ({ responder with
                  M.last_received =
                    Some packet.M.symbolic_packet })
            and ()
        | _ -> ()))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let public_share_preserves
  (state:M.model)
  (who:E.endpoint_id)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.set_public_share state who))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant (M.set_public_share state who)
  with _.
    (match who with
     | 0 ->
       (match initiator.M.private_value with
        | None -> ()
        | Some private_value ->
          let initiator1 = {
            initiator with
              M.own_share =
                Some (D.share_term private_value)
          } in
          introduce
            exists (value:BT.bytes).
              initiator1.M.private_value == Some value /\
              D.share_term private_value == D.share_term value
            with private_value and ();
          introduce
            exists (i r:M.endpoint_shadow).
              (M.set_public_share state who).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint state.M.dy_trace i /\
              shadow_valid
                SM.responder_endpoint state.M.dy_trace r
            with initiator1 responder and ())
     | 1 ->
       (match responder.M.private_value with
        | None -> ()
        | Some private_value ->
          let responder1 = {
            responder with
              M.own_share =
                Some (D.share_term private_value)
          } in
          introduce
            exists (value:BT.bytes).
              responder1.M.private_value == Some value /\
              D.share_term private_value == D.share_term value
            with private_value and ();
          introduce
            exists (i r:M.endpoint_shadow).
              (M.set_public_share state who).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint state.M.dy_trace i /\
              shadow_valid
                SM.responder_endpoint state.M.dy_trace r
            with initiator responder1 and ())
     | _ -> ())

let symbolic_peer_share_publishable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  (fallback:share)
  : Lemma
      (requires shadow_valid who trace shadow)
      (ensures
        publishable trace
          (M.symbolic_peer_share shadow fallback))
  =
  match shadow.M.last_received with
  | Some (D.SymbolicMessage1 _ peer_share) -> ()
  | Some (D.SymbolicMessage2 _ peer_share _) -> ()
  | _ ->
    B.literal_to_bytes_is_publishable
      #P.dh_crypto_invariants trace fallback

let optional_own_share_knowable
  (who:E.endpoint_id)
  (trace:TB.trace)
  (shadow:M.endpoint_shadow)
  : Lemma
      (requires shadow_valid who trace shadow)
      (ensures
        optional_knowable who trace shadow.M.own_share)
  =
  match shadow.M.own_share with
  | None -> ()
  | Some share ->
    own_share_publishable who trace shadow share;
    public_is_knowable who trace share

let shared_shadow_preserves
  (trace:TB.trace)
  (who:E.endpoint_id)
  (shadow:M.endpoint_shadow)
  (private_value:BT.bytes)
  (fallback:share)
  : Lemma
      (requires
        TI.trace_invariant #P.dh_protocol_invariants trace /\
        shadow_valid who trace shadow /\
        shadow.M.private_value == Some private_value)
      (ensures (
        let peer_share =
          M.symbolic_peer_share shadow fallback in
        let key =
          D.secret_term private_value peer_share in
        let position = TB.trace_length trace in
        let shadow1 = {
          shadow with
            M.peer_share = Some peer_share;
            M.key = Some key;
            M.state_position = position;
        } in
        let trace1 =
          TB.append_entry trace
            (T.SetState
              (D.role_principal who)
              (D.role_state_id who)
              (M.endpoint_snapshot shadow1))
        in
        TI.trace_invariant
          #P.dh_protocol_invariants trace1 /\
        shadow_valid who trace1 shadow1))
  =
  let peer_share = M.symbolic_peer_share shadow fallback in
  let key = D.secret_term private_value peer_share in
  let position = TB.trace_length trace in
  let shadow1 = {
    shadow with
      M.peer_share = Some peer_share;
      M.key = Some key;
      M.state_position = position;
  } in
  symbolic_peer_share_publishable
    who trace shadow fallback;
  long_term_knowable who trace shadow.M.long_term;
  scalar_knowable who trace private_value;
  optional_own_share_knowable who trace shadow;
  public_is_knowable who trace peer_share;
  key_knowable who trace private_value peer_share;
  assert (shadow_material_knowable who trace shadow1);
  snapshot_knowable who trace shadow1;
  let entry =
    T.SetState
      (D.role_principal who)
      (D.role_state_id who)
      (M.endpoint_snapshot shadow1)
  in
  trace_invariant_snoc trace entry;
  let trace1 = TB.append_entry trace entry in
  TB.grows_snoc trace entry;
  assert (state_position_valid who trace1 position);
  long_term_recorded_later
    who trace trace1 shadow.M.long_term;
  private_valid_later
    who trace trace1 shadow.M.private_value;
  optional_publishable_later
    trace trace1 shadow.M.own_share;
  optional_publishable_later
    trace trace1 (Some peer_share);
  optional_publishable_later
    trace trace1 shadow.M.pending_signature;
  optional_message_valid_later
    trace trace1 shadow.M.last_received;
  introduce
    exists (private_term peer_term:BT.bytes).
      shadow1.M.private_value == Some private_term /\
      shadow1.M.peer_share == Some peer_term /\
      shadow1.M.key ==
        Some (D.secret_term private_term peer_term)
    with private_value peer_share and ()
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let shared_secret_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (peer_public:share)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.set_shared_secret state who peer_public))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant
      (M.set_shared_secret state who peer_public)
  with _.
    (match who with
     | 0 ->
       (match initiator.M.private_value with
        | None -> ()
        | Some private_value ->
          let peer_share =
            M.symbolic_peer_share initiator peer_public
          in
          let key =
            D.secret_term private_value peer_share
          in
          let position = TB.trace_length state.M.dy_trace in
          let initiator1 = {
            initiator with
              M.peer_share = Some peer_share;
              M.key = Some key;
              M.state_position = position;
          } in
          let entry =
            T.SetState
              D.initiator_dy_principal
              (D.role_state_id SM.initiator_endpoint)
              (M.endpoint_snapshot initiator1)
          in
          let trace1 =
            TB.append_entry state.M.dy_trace entry
          in
          shared_shadow_preserves
            state.M.dy_trace
            SM.initiator_endpoint
            initiator
            private_value
            peer_public;
          TB.grows_snoc state.M.dy_trace entry;
          shadow_valid_later
            SM.responder_endpoint
            state.M.dy_trace trace1 responder;
          network_valid_later
            state.M.dy_trace trace1 state.M.network;
          introduce
            exists (i r:M.endpoint_shadow).
              (M.set_shared_secret state who peer_public).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint trace1 i /\
              shadow_valid
                SM.responder_endpoint trace1 r
            with initiator1 responder and ())
     | 1 ->
       (match responder.M.private_value with
        | None -> ()
        | Some private_value ->
          let peer_share =
            M.symbolic_peer_share responder peer_public
          in
          let key =
            D.secret_term private_value peer_share
          in
          let position = TB.trace_length state.M.dy_trace in
          let responder1 = {
            responder with
              M.peer_share = Some peer_share;
              M.key = Some key;
              M.state_position = position;
          } in
          let entry =
            T.SetState
              D.responder_dy_principal
              (D.role_state_id SM.responder_endpoint)
              (M.endpoint_snapshot responder1)
          in
          let trace1 =
            TB.append_entry state.M.dy_trace entry
          in
          shared_shadow_preserves
            state.M.dy_trace
            SM.responder_endpoint
            responder
            private_value
            peer_public;
          TB.grows_snoc state.M.dy_trace entry;
          shadow_valid_later
            SM.initiator_endpoint
            state.M.dy_trace trace1 initiator;
          network_valid_later
            state.M.dy_trace trace1 state.M.network;
          introduce
            exists (i r:M.endpoint_shadow).
              (M.set_shared_secret state who peer_public).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint trace1 i /\
              shadow_valid
                SM.responder_endpoint trace1 r
            with initiator responder1 and ())
     | _ -> ())
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let generated_shadow_preserves
  (trace:TB.trace)
  (who:E.endpoint_id)
  (shadow:M.endpoint_shadow)
  : Lemma
      (requires
        TI.trace_invariant #P.dh_protocol_invariants trace /\
        shadow_valid who trace shadow)
      (ensures (
        let position = TB.trace_length trace in
        let private_value = D.ephemeral_term position in
        let generated_trace =
          TB.append_entry trace
            (T.RandGen
              D.ephemeral_usage
              (D.role_label who)
              D.ephemeral_length)
        in
        let shadow1 = {
          shadow with
            M.private_value = Some private_value;
            M.own_share = None;
            M.peer_share = None;
            M.key = None;
            M.pending_signature = None;
            M.state_position = position + 1;
        } in
        let trace1 =
          TB.append_entry generated_trace
            (T.SetState
              (D.role_principal who)
              (D.role_state_id who)
              (M.endpoint_snapshot shadow1))
        in
        TI.trace_invariant #P.dh_protocol_invariants trace1 /\
        shadow_valid who trace1 shadow1))
  =
  let position = TB.trace_length trace in
  let private_value = D.ephemeral_term position in
  let random_entry =
    T.RandGen
      D.ephemeral_usage
      (D.role_label who)
      D.ephemeral_length
  in
  let generated_trace = TB.append_entry trace random_entry in
  trace_invariant_snoc trace random_entry;
  TB.grows_snoc trace random_entry;
  long_term_recorded_later
    who trace generated_trace shadow.M.long_term;
  long_term_knowable who generated_trace shadow.M.long_term;
  introduce
    exists (fresh_position:nat).
      private_value == D.ephemeral_term fresh_position /\
      TB.entry_at generated_trace fresh_position
        (T.RandGen
          D.ephemeral_usage
          (D.role_label who)
          D.ephemeral_length)
    with position and ();
  scalar_knowable who generated_trace private_value;
  let shadow1 = {
    shadow with
      M.private_value = Some private_value;
      M.own_share = None;
      M.peer_share = None;
      M.key = None;
      M.pending_signature = None;
      M.state_position = position + 1;
  } in
  assert (
    shadow_material_knowable who generated_trace shadow1);
  snapshot_knowable who generated_trace shadow1;
  let state_entry =
    T.SetState
      (D.role_principal who)
      (D.role_state_id who)
      (M.endpoint_snapshot shadow1)
  in
  trace_invariant_snoc generated_trace state_entry;
  let trace1 = TB.append_entry generated_trace state_entry in
  TB.grows_snoc generated_trace state_entry;
  long_term_recorded_later
    who generated_trace trace1 shadow.M.long_term;
  assert (state_position_valid who trace1 (position + 1));
  introduce
    exists (fresh_position:nat).
      private_value == D.ephemeral_term fresh_position /\
      TB.entry_at trace1 fresh_position
        (T.RandGen
          D.ephemeral_usage
          (D.role_label who)
          D.ephemeral_length)
    with position and ()

let generated_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (value:scalar)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.fresh_generated state who value))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant (M.fresh_generated state who value)
  with _.
    (match who with
     | 0 ->
       let position = TB.trace_length state.M.dy_trace in
       let private_value = D.ephemeral_term position in
       let random_entry =
         T.RandGen
           D.ephemeral_usage
           (D.role_label SM.initiator_endpoint)
           D.ephemeral_length
       in
       let generated_trace =
         TB.append_entry state.M.dy_trace random_entry
       in
       let initiator1 = {
         initiator with
           M.private_value = Some private_value;
           M.own_share = None;
           M.peer_share = None;
           M.key = None;
           M.pending_signature = None;
           M.state_position = position + 1;
       } in
       let state_entry =
         T.SetState
           D.initiator_dy_principal
           (D.role_state_id SM.initiator_endpoint)
           (M.endpoint_snapshot initiator1)
       in
       let trace1 =
         TB.append_entry generated_trace state_entry
       in
       generated_shadow_preserves
         state.M.dy_trace
         SM.initiator_endpoint
         initiator;
       TB.grows_snoc state.M.dy_trace random_entry;
       TB.grows_snoc generated_trace state_entry;
       assert (state.M.dy_trace `TB.grows` trace1);
       shadow_valid_later
         SM.responder_endpoint
         state.M.dy_trace trace1 responder;
       network_valid_later
         state.M.dy_trace trace1 state.M.network;
       introduce
         exists (i r:M.endpoint_shadow).
           (M.fresh_generated state who value).M.endpoints ==
             [ i; r ] /\
           shadow_valid
             SM.initiator_endpoint trace1 i /\
           shadow_valid
             SM.responder_endpoint trace1 r
         with initiator1 responder and ()
     | 1 ->
       let position = TB.trace_length state.M.dy_trace in
       let private_value = D.ephemeral_term position in
       let random_entry =
         T.RandGen
           D.ephemeral_usage
           (D.role_label SM.responder_endpoint)
           D.ephemeral_length
       in
       let generated_trace =
         TB.append_entry state.M.dy_trace random_entry
       in
       let responder1 = {
         responder with
           M.private_value = Some private_value;
           M.own_share = None;
           M.peer_share = None;
           M.key = None;
           M.pending_signature = None;
           M.state_position = position + 1;
       } in
       let state_entry =
         T.SetState
           D.responder_dy_principal
           (D.role_state_id SM.responder_endpoint)
           (M.endpoint_snapshot responder1)
       in
       let trace1 =
         TB.append_entry generated_trace state_entry
       in
       generated_shadow_preserves
         state.M.dy_trace
         SM.responder_endpoint
         responder;
       TB.grows_snoc state.M.dy_trace random_entry;
       TB.grows_snoc generated_trace state_entry;
       assert (state.M.dy_trace `TB.grows` trace1);
       shadow_valid_later
         SM.initiator_endpoint
         state.M.dy_trace trace1 initiator;
       network_valid_later
         state.M.dy_trace trace1 state.M.network;
       introduce
         exists (i r:M.endpoint_shadow).
           (M.fresh_generated state who value).M.endpoints ==
             [ i; r ] /\
           shadow_valid
             SM.initiator_endpoint trace1 i /\
           shadow_valid
             SM.responder_endpoint trace1 r
         with initiator responder1 and ()
     | _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let protocol_transcript_shape
  (who:E.endpoint_id)
  (shadow:M.endpoint_shadow)
  (partner:principal)
  (transcript:BT.bytes)
  : Lemma
      (requires
        M.protocol_transcript who shadow partner ==
          Some transcript)
      (ensures
        exists (partner_term gx gy:BT.bytes).
          transcript ==
            D.transcript_term partner_term gx gy)
  =
  match shadow.M.own_share, shadow.M.peer_share with
  | Some own_share, Some peer_share ->
    if who = SM.initiator_endpoint
    then
      introduce
        exists (partner_term gx gy:BT.bytes).
          transcript ==
            D.transcript_term partner_term gx gy
        with
          (D.principal_term partner)
          own_share
          peer_share
        and ()
    else
      introduce
        exists (partner_term gx gy:BT.bytes).
          transcript ==
            D.transcript_term partner_term gx gy
        with
          (D.principal_term partner)
          peer_share
          own_share
        and ()
  | _, _ -> ()
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let created_shadow_preserves
  (trace:TB.trace)
  (who:E.endpoint_id{who == SM.initiator_endpoint \/
                     who == SM.responder_endpoint})
  (shadow:M.endpoint_shadow)
  (partner:principal)
  (transcript:BT.bytes)
  : Lemma
      (requires
        TI.trace_invariant #P.dh_protocol_invariants trace /\
        shadow_valid who trace shadow /\
        M.protocol_transcript who shadow partner ==
          Some transcript)
      (ensures (
        let authorization_position = TB.trace_length trace in
        let tag =
          if who = SM.initiator_endpoint
          then D.tag_authorize_initiator
          else D.tag_authorize_responder
        in
        let event_entry =
          T.Event (D.role_principal who) tag transcript
        in
        let trace1 = TB.append_entry trace event_entry in
        let nonce_position = authorization_position + 1 in
        let random_entry =
          T.RandGen
            D.signing_nonce_usage
            (D.role_label who)
            D.signing_nonce_length
        in
        let trace2 = TB.append_entry trace1 random_entry in
        let signature =
          D.signature_term
            shadow.M.long_term
            (D.signing_nonce_term nonce_position)
            transcript
        in
        let shadow1 = {
          shadow with M.pending_signature = Some signature
        } in
        TI.trace_invariant #P.dh_protocol_invariants trace2 /\
        shadow_valid who trace2 shadow1))
  =
  let authorization_position = TB.trace_length trace in
  let tag =
    if who = SM.initiator_endpoint
    then D.tag_authorize_initiator
    else D.tag_authorize_responder
  in
  let event_entry =
    T.Event (D.role_principal who) tag transcript
  in
  protocol_transcript_shape who shadow partner transcript;
  authorization_event_entry trace who transcript;
  trace_invariant_snoc trace event_entry;
  let trace1 = TB.append_entry trace event_entry in
  let nonce_position = authorization_position + 1 in
  let random_entry =
    T.RandGen
      D.signing_nonce_usage
      (D.role_label who)
      D.signing_nonce_length
  in
  trace_invariant_snoc trace1 random_entry;
  let trace2 = TB.append_entry trace1 random_entry in
  TB.grows_snoc trace event_entry;
  TB.grows_snoc trace1 random_entry;
  assert (trace `TB.grows` trace2);
  shadow_valid_later who trace trace2 shadow;
  network_valid_later trace trace2 [];
  protocol_transcript_publishable
    who trace shadow partner transcript;
  publishable_later trace trace2 transcript;
  assert (
    TB.entry_at trace2 nonce_position random_entry);
  assert (
    TB.event_triggered trace2
      (D.role_principal who) tag transcript);
  signature_publishable
    trace2 who shadow.M.long_term
    (D.signing_nonce_term nonce_position)
    transcript nonce_position;
  let signature =
    D.signature_term
      shadow.M.long_term
      (D.signing_nonce_term nonce_position)
      transcript
  in
  let shadow1 = {
    shadow with M.pending_signature = Some signature
  } in
  assert (
    optional_publishable trace2
      shadow1.M.pending_signature)
#pop-options

#push-options "--fuel 8 --ifuel 2 --z3rlimit 10 --split_queries always"
let signature_created_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (partner:principal)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.create_signature state who partner))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant
      (M.create_signature state who partner)
  with _.
    (match who with
     | 0 ->
       (match
          M.protocol_transcript
            SM.initiator_endpoint initiator partner
        with
        | None -> ()
        | Some transcript ->
          let authorization_position =
            TB.trace_length state.M.dy_trace
          in
          let event_entry =
            T.Event
              D.initiator_dy_principal
              D.tag_authorize_initiator
              transcript
          in
          let trace1 =
            TB.append_entry state.M.dy_trace event_entry
          in
          let nonce_position = authorization_position + 1 in
          let random_entry =
            T.RandGen
              D.signing_nonce_usage
              (D.role_label SM.initiator_endpoint)
              D.signing_nonce_length
          in
          let trace2 =
            TB.append_entry trace1 random_entry
          in
          let signature =
            D.signature_term
              initiator.M.long_term
              (D.signing_nonce_term nonce_position)
              transcript
          in
          let initiator1 = {
            initiator with
              M.pending_signature = Some signature
          } in
          created_shadow_preserves
            state.M.dy_trace
            SM.initiator_endpoint
            initiator
            partner
            transcript;
          TB.grows_snoc state.M.dy_trace event_entry;
          TB.grows_snoc trace1 random_entry;
          assert (state.M.dy_trace `TB.grows` trace2);
          shadow_valid_later
            SM.responder_endpoint
            state.M.dy_trace trace2 responder;
          network_valid_later
            state.M.dy_trace trace2 state.M.network;
          introduce
            exists (i r:M.endpoint_shadow).
              (M.create_signature state who partner).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint trace2 i /\
              shadow_valid
                SM.responder_endpoint trace2 r
            with initiator1 responder and ())
     | 1 ->
       (match
          M.protocol_transcript
            SM.responder_endpoint responder partner
        with
        | None -> ()
        | Some transcript ->
          let authorization_position =
            TB.trace_length state.M.dy_trace
          in
          let event_entry =
            T.Event
              D.responder_dy_principal
              D.tag_authorize_responder
              transcript
          in
          let trace1 =
            TB.append_entry state.M.dy_trace event_entry
          in
          let nonce_position = authorization_position + 1 in
          let random_entry =
            T.RandGen
              D.signing_nonce_usage
              (D.role_label SM.responder_endpoint)
              D.signing_nonce_length
          in
          let trace2 =
            TB.append_entry trace1 random_entry
          in
          let signature =
            D.signature_term
              responder.M.long_term
              (D.signing_nonce_term nonce_position)
              transcript
          in
          let responder1 = {
            responder with
              M.pending_signature = Some signature
          } in
          created_shadow_preserves
            state.M.dy_trace
            SM.responder_endpoint
            responder
            partner
            transcript;
          TB.grows_snoc state.M.dy_trace event_entry;
          TB.grows_snoc trace1 random_entry;
          assert (state.M.dy_trace `TB.grows` trace2);
          shadow_valid_later
            SM.initiator_endpoint
            state.M.dy_trace trace2 initiator;
          network_valid_later
            state.M.dy_trace trace2 state.M.network;
          introduce
            exists (i r:M.endpoint_shadow).
              (M.create_signature state who partner).M.endpoints ==
                [ i; r ] /\
              shadow_valid
                SM.initiator_endpoint trace2 i /\
              shadow_valid
                SM.responder_endpoint trace2 r
            with initiator responder1 and ())
     | _ -> ())
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 10 --split_queries always"
let acceptance_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (partner:principal)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_acceptance state who partner))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant
      (M.record_acceptance state who partner)
  with _.
    (match who with
     | 0 ->
       (match
          M.acceptance_transcript
            SM.initiator_endpoint initiator partner,
          M.accepted_signature
            SM.initiator_endpoint initiator
        with
        | Some transcript, Some signature ->
          accepted_event_entry
            state.M.dy_trace
            SM.initiator_endpoint
            transcript signature;
          model_trace_snoc state
            (T.Event
              D.initiator_dy_principal
              D.tag_accepted
              (D.accepted_content transcript signature))
        | _, _ -> ())
     | 1 ->
       (match
          M.acceptance_transcript
            SM.responder_endpoint responder partner,
          M.accepted_signature
            SM.responder_endpoint responder
        with
        | Some transcript, Some signature ->
          accepted_event_entry
            state.M.dy_trace
            SM.responder_endpoint
            transcript signature;
          model_trace_snoc state
            (T.Event
              D.responder_dy_principal
              D.tag_accepted
              (D.accepted_content transcript signature))
        | _, _ -> ())
     | _ -> ())

let completion_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (peer:principal)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.record_completion state who peer))
  =
  eliminate
    exists (initiator responder:M.endpoint_shadow).
      state.M.endpoints == [ initiator; responder ] /\
      shadow_valid
        SM.initiator_endpoint state.M.dy_trace initiator /\
      shadow_valid
        SM.responder_endpoint state.M.dy_trace responder
  returns
    model_invariant
      (M.record_completion state who peer)
  with _.
    (match who with
     | 0 ->
       (match initiator.M.key with
        | Some key ->
          completion_event_entry
            state.M.dy_trace
            SM.initiator_endpoint
            (D.principal_term peer)
            key;
          model_trace_snoc state
            (T.Event
              D.initiator_dy_principal
              D.tag_complete
              (D.completion_content
                (D.principal_term peer)
                key))
        | None -> ())
     | 1 ->
       (match responder.M.key with
        | Some key ->
          completion_event_entry
            state.M.dy_trace
            SM.responder_endpoint
            (D.principal_term peer)
            key;
          model_trace_snoc state
            (T.Event
              D.responder_dy_principal
              D.tag_complete
              (D.completion_content
                (D.principal_term peer)
                key))
        | None -> ())
     | _ -> ())

let protocol_effect_preserves
  (state:M.model)
  (who:E.endpoint_id)
  (event:SM.semantic_event)
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (M.protocol_effect state who event))
  =
  match event with
  | SM.PublicShare _ _ ->
    public_share_preserves state who
  | SM.SharedSecret _ peer_public _ ->
    shared_secret_preserves state who peer_public
  | SM.SignatureCreated _ partner _ _ _ ->
    signature_created_preserves state who partner
  | SM.SignatureAccepted _ partner _ _ _ ->
    acceptance_preserves state who partner
  | SM.Completed peer _ ->
    completion_preserves state who peer
#pop-options

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10 --split_queries always"
let effect_preserves
  (state:M.model)
  (history_event:(S.system_effect message scalar SM.semantic_event))
  : Lemma
      (requires model_invariant state)
      (ensures
        model_invariant
          (I.interpret_one
            M.history_interpreter state history_event))
  =
  match history_event with
  | S.Generated who value ->
    generated_preserves state who value
  | S.ObservedReceive who index _ ->
    received_preserves state who index
  | S.ProtocolEffect who event ->
    protocol_effect_preserves state who event
  | S.ObservedSend who index message ->
    sent_preserves state who index message
  | S.AttackerInjected index message ->
    injected_preserves state index message
  | S.Compromised who ->
    compromised_preserves state who
#pop-options

noextract
let verified_history_interpreter
  : I.verified_interpreter
      message scalar SM.semantic_event M.model
      M.history_interpreter
  =
  {
    I.model_invariant = model_invariant;
    I.initial_valid = initial_model_invariant;
    I.effect_preserves = effect_preserves;
  }

let history_model_invariant
  (history:list (S.system_effect message scalar SM.semantic_event))
  : Lemma
      (ensures
        model_invariant
          (M.interpret_history history))
  =
  I.lemma_interpret_history_valid
    M.history_interpreter
    verified_history_interpreter
    history

let history_trace_invariant
  (history:list (S.system_effect message scalar SM.semantic_event))
  : Lemma
      (ensures
        TI.trace_invariant
          #P.dh_protocol_invariants
          (M.dy_trace_of_history history))
  =
  history_model_invariant history

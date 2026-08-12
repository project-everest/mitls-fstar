module NSL.Sample.DY.Profile

(** Non-vacuous NSL protocol profile installed into the DY* core invariant. *)

module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module T = DY.Core.Trace.Type
module TB = DY.Core.Trace.Base
module TI = DY.Core.Trace.Invariant
module D = NSL.Sample.DY.Terms
module SM = NSL.Sample.StateMachine

instance nsl_crypto_usages : B.crypto_usages =
  B.default_crypto_usages

let pke_authorized
  (public_key:BT.bytes)
  (principal:T.principal)
  (tag:string)
  : prop
  =
  (public_key == D.role_public_key SM.responder_endpoint /\
    ((principal == D.initiator_dy_principal /\
      (tag == D.tag_message1 \/ tag == D.tag_message3)) \/
     (principal == D.responder_dy_principal /\
      tag == D.tag_message2))) \/
  (public_key == D.role_public_key SM.initiator_endpoint /\
    principal == D.responder_dy_principal /\
    tag == D.tag_message2)

let pke_predicate
  (trace:TB.trace)
  (usage:BT.usage{BT.PkeKey? usage})
  (public_key content:BT.bytes)
  : prop
  =
  exists (principal:T.principal) (tag:string).
    pke_authorized public_key principal tag /\
    TB.event_triggered trace principal tag content

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let pke_predicate_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage{BT.PkeKey? usage})
  (public_key content:BT.bytes)
  : Lemma
      (requires
        pke_predicate trace0 usage public_key content /\
        B.bytes_well_formed trace0 public_key /\
        B.bytes_well_formed trace0 content /\
        trace0 `TB.grows` trace1)
      (ensures
        pke_predicate trace1 usage public_key content)
  =
  eliminate
    exists (principal:T.principal) (tag:string).
      pke_authorized public_key principal tag /\
      TB.event_triggered trace0 principal tag content
  returns pke_predicate trace1 usage public_key content
  with _.
    (TB.event_triggered_grows
       trace0 trace1 principal tag content;
     introduce
       exists (principal':T.principal) (tag':string).
         pke_authorized public_key principal' tag' /\
         TB.event_triggered trace1 principal' tag' content
     with principal tag and ())
#pop-options

let public_predicate
  (trace:TB.trace)
  (usage:BT.usage)
  (left right:BT.bytes)
  : prop
  =
  B.get_label #nsl_crypto_usages trace right == L.public

let public_predicate4
  (trace:TB.trace)
  (usage:BT.usage)
  (one two three four:BT.bytes)
  : prop
  =
  B.get_label #nsl_crypto_usages trace three == L.public

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let public_predicate_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage)
  (left right:BT.bytes)
  : Lemma
      (requires
        public_predicate trace0 usage left right /\
        B.bytes_well_formed trace0 left /\
        B.bytes_well_formed trace0 right /\
        trace0 `TB.grows` trace1)
      (ensures public_predicate trace1 usage left right)
  =
  B.get_label_later #nsl_crypto_usages trace0 trace1 right

let public_predicate4_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage)
  (one two three four:BT.bytes)
  : Lemma
      (requires
        public_predicate4 trace0 usage one two three four /\
        B.bytes_well_formed trace0 one /\
        B.bytes_well_formed trace0 two /\
        B.bytes_well_formed trace0 three /\
        B.bytes_well_formed trace0 four /\
        trace0 `TB.grows` trace1)
      (ensures public_predicate4 trace1 usage one two three four)
  =
  B.get_label_later #nsl_crypto_usages trace0 trace1 three
#pop-options

let pke_crypto_predicate : B.pke_crypto_predicate #nsl_crypto_usages = {
  B.pred = pke_predicate;
  B.pred_later = pke_predicate_later;
}

let aead_crypto_predicate : B.aead_crypto_predicate #nsl_crypto_usages = {
  B.pred = public_predicate4;
  B.pred_later = public_predicate4_later;
}

let sign_crypto_predicate : B.sign_crypto_predicate #nsl_crypto_usages = {
  B.pred = public_predicate;
  B.pred_later = public_predicate_later;
}

let mac_crypto_predicate : B.mac_crypto_predicate #nsl_crypto_usages = {
  B.pred = public_predicate;
  B.pred_later = public_predicate_later;
}

let crypto_predicates : B.crypto_predicates #nsl_crypto_usages = {
  B.aead_pred = aead_crypto_predicate;
  B.pke_pred = pke_crypto_predicate;
  B.sign_pred = sign_crypto_predicate;
  B.mac_pred = mac_crypto_predicate;
}

instance nsl_crypto_invariants : B.crypto_invariants = {
  B.usages = nsl_crypto_usages;
  B.preds = crypto_predicates;
}

let state_predicate
  (trace:TB.trace)
  (principal:T.principal)
  (state_id:T.state_id)
  (content:BT.bytes)
  : prop
  =
  B.is_knowable_by #nsl_crypto_invariants
    (L.principal_state_label principal state_id)
    trace content

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let state_predicate_later
  (trace0 trace1:TB.trace)
  (principal:T.principal)
  (state_id:T.state_id)
  (content:BT.bytes)
  : Lemma
      (requires
        state_predicate trace0 principal state_id content /\
        trace0 `TB.grows` trace1)
      (ensures
        state_predicate trace1 principal state_id content)
  =
  B.bytes_invariant_later #nsl_crypto_invariants trace0 trace1 content;
  B.bytes_invariant_implies_well_formed
    #nsl_crypto_invariants trace0 content;
  B.get_label_later #nsl_crypto_usages trace0 trace1 content;
  L.can_flow_later trace0 trace1
    (B.get_label #nsl_crypto_usages trace0 content)
    (L.principal_state_label principal state_id)

let state_predicate_knowable
  (trace:TB.trace)
  (principal:T.principal)
  (state_id:T.state_id)
  (content:BT.bytes)
  : Lemma
      (requires
        state_predicate trace principal state_id content)
      (ensures
        B.is_knowable_by #nsl_crypto_invariants
          (L.principal_state_content_label
            principal state_id content)
          trace content)
  =
  let content_label = B.get_label #nsl_crypto_usages trace content in
  L.state_pred_label_can_flow_state_pred_label trace
    (L.principal_state_label_input principal state_id)
    (L.principal_state_content_label_input
      principal state_id content);
  L.can_flow_transitive trace
    content_label
    (L.principal_state_label principal state_id)
    (L.principal_state_content_label principal state_id content)
#pop-options

let nsl_state_predicate : TI.state_predicate #nsl_crypto_invariants = {
  TI.pred = state_predicate;
  TI.pred_later = state_predicate_later;
  TI.pred_knowable = state_predicate_knowable;
}

let event_predicate
  (trace:TB.trace)
  (principal:T.principal)
  (tag:string)
  (content:BT.bytes)
  : prop
  =
  (tag == D.tag_message1 /\
    principal == D.initiator_dy_principal /\
    (exists (initiator_nonce initiator:BT.bytes).
      content == D.plaintext1_term initiator_nonce initiator)) \/
  (tag == D.tag_message2 /\
    principal == D.responder_dy_principal /\
    (exists (initiator_nonce responder_nonce responder:BT.bytes).
      content ==
        D.plaintext2_term
          initiator_nonce responder_nonce responder)) \/
  (tag == D.tag_message3 /\
    principal == D.initiator_dy_principal /\
    (exists (responder_nonce:BT.bytes).
      content == D.plaintext3_term responder_nonce)) \/
  (tag == D.tag_accepted /\
    (principal == D.initiator_dy_principal \/
     principal == D.responder_dy_principal) /\
    (exists (ciphertext plaintext:BT.bytes).
      content == D.accepted_content ciphertext plaintext)) \/
  (tag == D.tag_complete /\
    (principal == D.initiator_dy_principal \/
     principal == D.responder_dy_principal) /\
    (exists (peer initiator_nonce responder_nonce:BT.bytes).
      content ==
        D.session_content peer initiator_nonce responder_nonce))

let trace_invariants : TI.trace_invariants #nsl_crypto_invariants = {
  TI.state_pred = nsl_state_predicate;
  TI.event_pred = event_predicate;
}

instance nsl_protocol_invariants : TI.protocol_invariants = {
  TI.crypto_invs = nsl_crypto_invariants;
  TI.trace_invs = trace_invariants;
}

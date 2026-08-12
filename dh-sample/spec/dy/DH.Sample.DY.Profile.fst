module DH.Sample.DY.Profile

(** Non-vacuous protocol profile installed into the DY* core invariant. *)

module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module LT = DY.Core.Label.Type
module T = DY.Core.Trace.Type
module TB = DY.Core.Trace.Base
module TI = DY.Core.Trace.Invariant
module D = DH.Sample.DY.Terms
module SM = DH.Sample.StateMachine

instance dh_crypto_usages : B.crypto_usages =
  B.default_crypto_usages

let sign_predicate
  (trace:TB.trace)
  (usage:BT.usage{BT.SigKey? usage})
  (verification_key content:BT.bytes)
  : prop
  =
  (verification_key ==
      D.verification_key_term (D.long_term_term 0) /\
    TB.event_triggered
      trace
      D.initiator_dy_principal
      D.tag_authorize_initiator
      content) \/
  (verification_key ==
      D.verification_key_term (D.long_term_term 2) /\
    TB.event_triggered
      trace
      D.responder_dy_principal
      D.tag_authorize_responder
      content)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let sign_predicate_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage{BT.SigKey? usage})
  (verification_key content:BT.bytes)
  : Lemma
      (requires
        sign_predicate trace0 usage verification_key content /\
        B.bytes_well_formed trace0 verification_key /\
        B.bytes_well_formed trace0 content /\
        trace0 `TB.grows` trace1)
      (ensures
        sign_predicate trace1 usage verification_key content)
  =
  eliminate
    (verification_key ==
        D.verification_key_term (D.long_term_term 0) /\
      TB.event_triggered
        trace0
        D.initiator_dy_principal
        D.tag_authorize_initiator
        content) \/
    (verification_key ==
        D.verification_key_term (D.long_term_term 2) /\
      TB.event_triggered
        trace0
        D.responder_dy_principal
        D.tag_authorize_responder
        content)
  returns sign_predicate trace1 usage verification_key content
  with _.
    TB.event_triggered_grows
      trace0 trace1
      D.initiator_dy_principal
      D.tag_authorize_initiator
      content
  and _.
    TB.event_triggered_grows
      trace0 trace1
      D.responder_dy_principal
      D.tag_authorize_responder
      content
#pop-options

let sign_crypto_predicate : B.sign_crypto_predicate #dh_crypto_usages = {
  B.pred = sign_predicate;
  B.pred_later = sign_predicate_later;
}

let aead_predicate
  (trace:TB.trace)
  (usage:BT.usage{BT.AeadKey? usage})
  (key nonce content associated_data:BT.bytes)
  : prop
  =
  B.get_label #dh_crypto_usages trace content == L.public

let pke_predicate
  (trace:TB.trace)
  (usage:BT.usage{BT.PkeKey? usage})
  (public_key content:BT.bytes)
  : prop
  =
  B.get_label #dh_crypto_usages trace content == L.public

let mac_predicate
  (trace:TB.trace)
  (usage:BT.usage{BT.MacKey? usage})
  (key content:BT.bytes)
  : prop
  =
  B.get_label #dh_crypto_usages trace content == L.public

#push-options "--fuel 2 --ifuel 1 --z3rlimit 10"
let aead_predicate_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage{BT.AeadKey? usage})
  (key nonce content associated_data:BT.bytes)
  : Lemma
      (requires
        aead_predicate trace0 usage key nonce content associated_data /\
        B.bytes_well_formed trace0 key /\
        B.bytes_well_formed trace0 nonce /\
        B.bytes_well_formed trace0 content /\
        B.bytes_well_formed trace0 associated_data /\
        trace0 `TB.grows` trace1)
      (ensures
        aead_predicate trace1 usage key nonce content associated_data)
  =
  B.get_label_later #dh_crypto_usages trace0 trace1 content

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
  B.get_label_later #dh_crypto_usages trace0 trace1 content

let mac_predicate_later
  (trace0 trace1:TB.trace)
  (usage:BT.usage{BT.MacKey? usage})
  (key content:BT.bytes)
  : Lemma
      (requires
        mac_predicate trace0 usage key content /\
        B.bytes_well_formed trace0 key /\
        B.bytes_well_formed trace0 content /\
        trace0 `TB.grows` trace1)
      (ensures
        mac_predicate trace1 usage key content)
  =
  B.get_label_later #dh_crypto_usages trace0 trace1 content
#pop-options

let aead_crypto_predicate : B.aead_crypto_predicate #dh_crypto_usages = {
  B.pred = aead_predicate;
  B.pred_later = aead_predicate_later;
}

let pke_crypto_predicate : B.pke_crypto_predicate #dh_crypto_usages = {
  B.pred = pke_predicate;
  B.pred_later = pke_predicate_later;
}

let mac_crypto_predicate : B.mac_crypto_predicate #dh_crypto_usages = {
  B.pred = mac_predicate;
  B.pred_later = mac_predicate_later;
}

let crypto_predicates : B.crypto_predicates #dh_crypto_usages = {
  B.aead_pred = aead_crypto_predicate;
  B.pke_pred = pke_crypto_predicate;
  B.sign_pred = sign_crypto_predicate;
  B.mac_pred = mac_crypto_predicate;
}

instance dh_crypto_invariants : B.crypto_invariants = {
  B.usages = dh_crypto_usages;
  B.preds = crypto_predicates;
}

let state_predicate
  (trace:TB.trace)
  (principal:T.principal)
  (state_id:T.state_id)
  (content:BT.bytes)
  : prop
  =
  B.is_knowable_by #dh_crypto_invariants
    (L.principal_state_label principal state_id)
    trace
    content

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
  B.bytes_invariant_later #dh_crypto_invariants trace0 trace1 content;
  B.bytes_invariant_implies_well_formed
    #dh_crypto_invariants trace0 content;
  B.get_label_later #dh_crypto_usages trace0 trace1 content;
  L.can_flow_later trace0 trace1
    (B.get_label #dh_crypto_usages trace0 content)
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
        B.is_knowable_by #dh_crypto_invariants
          (L.principal_state_content_label principal state_id content)
          trace
          content)
  =
  let content_label = B.get_label #dh_crypto_usages trace content in
  L.state_pred_label_can_flow_state_pred_label trace
    (L.principal_state_label_input principal state_id)
    (L.principal_state_content_label_input principal state_id content);
  L.can_flow_transitive trace
    content_label
    (L.principal_state_label principal state_id)
    (L.principal_state_content_label principal state_id content)
#pop-options

let dh_state_predicate : TI.state_predicate #dh_crypto_invariants = {
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
  (tag == D.tag_authorize_initiator /\
    principal == D.initiator_dy_principal /\
    (exists (partner gx gy:BT.bytes).
      content == D.transcript_term partner gx gy)) \/
  (tag == D.tag_authorize_responder /\
    principal == D.responder_dy_principal /\
    (exists (partner gx gy:BT.bytes).
      content == D.transcript_term partner gx gy)) \/
  (tag == D.tag_accepted /\
    (principal == D.initiator_dy_principal \/
     principal == D.responder_dy_principal) /\
    (exists (transcript signature:BT.bytes).
      content == D.accepted_content transcript signature)) \/
  (tag == D.tag_complete /\
    (principal == D.initiator_dy_principal \/
     principal == D.responder_dy_principal) /\
    (exists (peer key:BT.bytes).
      content == D.completion_content peer key))

let trace_invariants : TI.trace_invariants #dh_crypto_invariants = {
  TI.state_pred = dh_state_predicate;
  TI.event_pred = event_predicate;
}

instance dh_protocol_invariants : TI.protocol_invariants = {
  TI.crypto_invs = dh_crypto_invariants;
  TI.trace_invs = trace_invariants;
}

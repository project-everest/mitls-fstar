module DH.Sample.DY.Terms

(** DY* vocabulary for the canonical ISO-DH history. *)

module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module LT = DY.Core.Label.Type
module T = DY.Core.Trace.Type
module Seq = FStar.Seq
module U8 = FStar.UInt8
module E = Common.Protocol.Labelled

open DH.Sample.Types
open DH.Sample.Wire

let initiator_dy_principal : T.principal = "DH.Sample.Initiator"
let responder_dy_principal : T.principal = "DH.Sample.Responder"

let role_principal (who:E.endpoint_id) : T.principal =
  if who = 0 then initiator_dy_principal else responder_dy_principal

let role_state_id (who:E.endpoint_id) : T.state_id = { T.the_id = who }

let role_label (who:E.endpoint_id) : LT.label =
  L.principal_state_label (role_principal who) (role_state_id who)

let empty_data : BT.bytes = B.literal_to_bytes (Seq.empty #U8.t)

let ephemeral_length : n:nat{n <> 0} = 32
let long_term_length : n:nat{n <> 0} = 32
let signing_nonce_length : n:nat{n <> 0} = 32

let ephemeral_usage : BT.usage =
  BT.DhKey "DH.Sample.ephemeral" empty_data

let long_term_usage : BT.usage =
  BT.SigKey "DH.Sample.longterm" empty_data

let signing_nonce_usage : BT.usage =
  BT.SigNonce

let ephemeral_term (time:nat) : BT.bytes =
  BT.Rand ephemeral_length time

let long_term_term (time:nat) : BT.bytes =
  BT.Rand long_term_length time

let signing_nonce_term (time:nat) : BT.bytes =
  BT.Rand signing_nonce_length time

let share_term (private_value:BT.bytes) : BT.bytes =
  B.dh_pk private_value

let secret_term (private_value peer_share:BT.bytes) : BT.bytes =
  B.dh private_value peer_share

let verification_key_term (private_value:BT.bytes) : BT.bytes =
  B.vk private_value

let signature_term
  (private_value nonce content:BT.bytes)
  : BT.bytes
  =
  B.sign private_value nonce content

let principal_term (value:principal) : BT.bytes =
  B.literal_to_bytes value

let share_literal (value:share) : BT.bytes =
  B.literal_to_bytes value

let signature_literal (value:signature) : BT.bytes =
  B.literal_to_bytes value

let transcript_term
  (partner initiator_share responder_share:BT.bytes)
  : BT.bytes
  =
  B.concat partner (B.concat initiator_share responder_share)

noeq
type symbolic_message =
  | SymbolicMessage1:
      initiator:BT.bytes ->
      initiator_share:BT.bytes ->
      symbolic_message
  | SymbolicMessage2:
      responder:BT.bytes ->
      responder_share:BT.bytes ->
      responder_signature:BT.bytes ->
      symbolic_message
  | SymbolicMessage3:
      initiator_signature:BT.bytes ->
      symbolic_message

let flatten (value:symbolic_message) : BT.bytes =
  match value with
  | SymbolicMessage1 initiator initiator_share ->
    B.concat initiator initiator_share
  | SymbolicMessage2 responder responder_share responder_signature ->
    B.concat responder (B.concat responder_share responder_signature)
  | SymbolicMessage3 initiator_signature ->
    initiator_signature

let injected_message (value:message) : symbolic_message =
  match value with
  | Message1 initiator initiator_share ->
    SymbolicMessage1
      (principal_term initiator)
      (share_literal initiator_share)
  | Message2 responder responder_share responder_signature ->
    SymbolicMessage2
      (principal_term responder)
      (share_literal responder_share)
      (signature_literal responder_signature)
  | Message3 initiator_signature ->
    SymbolicMessage3 (signature_literal initiator_signature)

let optional_term (value:option BT.bytes) : BT.bytes =
  match value with
  | None -> empty_data
  | Some term -> term

(** No erasure: every later snapshot retains the scalar and session key. *)
let snapshot
  (long_term:BT.bytes)
  (private_value own_share peer_share key:option BT.bytes)
  : BT.bytes
  =
  B.concat long_term
    (B.concat (optional_term private_value)
      (B.concat (optional_term own_share)
        (B.concat (optional_term peer_share) (optional_term key))))

let tag_authorize_initiator : string =
  "DH.Sample.AuthorizeInitiator"

let tag_authorize_responder : string =
  "DH.Sample.AuthorizeResponder"

let tag_complete : string =
  "DH.Sample.Complete"

let tag_accepted : string =
  "DH.Sample.SignatureAccepted"

let completion_content (peer key:BT.bytes) : BT.bytes =
  B.concat peer key

let accepted_content (transcript signature:BT.bytes) : BT.bytes =
  B.concat transcript signature

let lemma_dh_agreement (left right:BT.bytes)
  : Lemma
      (ensures
        secret_term left (share_term right) ==
        secret_term right (share_term left))
  =
  B.dh_shared_secret_lemma left right

let lemma_signature_verifies
  (private_value nonce content:BT.bytes)
  : Lemma
      (ensures
        B.verify
          (verification_key_term private_value)
          content
          (signature_term private_value nonce content))
  =
  B.verify_sign private_value nonce content

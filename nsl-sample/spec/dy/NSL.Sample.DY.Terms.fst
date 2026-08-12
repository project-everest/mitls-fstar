module NSL.Sample.DY.Terms

(** DY* vocabulary for canonical NSL histories. *)

module B = DY.Core.Bytes
module BT = DY.Core.Bytes.Type
module L = DY.Core.Label
module LT = DY.Core.Label.Type
module T = DY.Core.Trace.Type
module Seq = FStar.Seq
module U8 = FStar.UInt8
module E = Common.Protocol.Labelled

open NSL.Sample.Types

let initiator_dy_principal : T.principal = "NSL.Sample.Initiator"
let responder_dy_principal : T.principal = "NSL.Sample.Responder"

let role_principal (who:E.endpoint_id) : T.principal =
  if who = 0 then initiator_dy_principal else responder_dy_principal

let role_state_id (who:E.endpoint_id) : T.state_id = { T.the_id = who }

let role_label (who:E.endpoint_id) : LT.label =
  L.principal_state_label (role_principal who) (role_state_id who)

let session_label : LT.label =
  L.join (role_label 0) (role_label 1)

let empty_data : BT.bytes = B.literal_to_bytes (Seq.empty #U8.t)

let key_length : n:nat{n <> 0} = 32
let protocol_nonce_length : n:nat{n <> 0} = nonce_length
let encryption_nonce_length : n:nat{n <> 0} = pke_randomness_length

let initiator_key_usage : BT.usage =
  BT.PkeKey "NSL.Sample.InitiatorKey" empty_data

let responder_key_usage : BT.usage =
  BT.PkeKey "NSL.Sample.ResponderKey" empty_data

let key_usage (who:E.endpoint_id) : BT.usage =
  if who = 0 then initiator_key_usage else responder_key_usage

let protocol_nonce_usage : BT.usage = BT.NoUsage
let encryption_nonce_usage : BT.usage = BT.PkeNonce

let key_term (time:nat) : BT.bytes =
  BT.Rand key_length time

let protocol_nonce_term (time:nat) : BT.bytes =
  BT.Rand protocol_nonce_length time

let encryption_nonce_term (time:nat) : BT.bytes =
  BT.Rand encryption_nonce_length time

let public_key_term (secret_key:BT.bytes) : BT.bytes =
  B.pk secret_key

let role_secret_key (who:E.endpoint_id) : BT.bytes =
  if who = 0 then key_term 0 else key_term 2

let role_public_key (who:E.endpoint_id) : BT.bytes =
  public_key_term (role_secret_key who)

let principal_term (value:principal) : BT.bytes =
  B.literal_to_bytes value

let nonce_literal (value:nonce) : BT.bytes =
  B.literal_to_bytes value

let ciphertext_literal (value:ciphertext) : BT.bytes =
  B.literal_to_bytes value

let plaintext1_term
  (initiator_nonce initiator:BT.bytes)
  : BT.bytes
  =
  B.concat initiator_nonce initiator

let plaintext2_term
  (initiator_nonce responder_nonce responder:BT.bytes)
  : BT.bytes
  =
  B.concat initiator_nonce (B.concat responder_nonce responder)

let plaintext3_term (responder_nonce:BT.bytes) : BT.bytes =
  responder_nonce

let ciphertext_term
  (recipient_key randomness plaintext:BT.bytes)
  : BT.bytes
  =
  B.pke_enc recipient_key randomness plaintext

let optional_term (value:option BT.bytes) : BT.bytes =
  match value with
  | None -> empty_data
  | Some term -> term

let snapshot
  (secret_key:BT.bytes)
  (pending_nonce pending_randomness:option BT.bytes)
  (initiator_nonce responder_nonce:option BT.bytes)
  : BT.bytes
  =
  B.concat secret_key
    (B.concat (optional_term pending_nonce)
      (B.concat (optional_term pending_randomness)
        (B.concat
          (optional_term initiator_nonce)
          (optional_term responder_nonce))))

let tag_message1 : string = "NSL.Sample.Message1"
let tag_message2 : string = "NSL.Sample.Message2"
let tag_message3 : string = "NSL.Sample.Message3"
let tag_accepted : string = "NSL.Sample.CiphertextAccepted"
let tag_complete : string = "NSL.Sample.Complete"

let accepted_content
  (ciphertext plaintext:BT.bytes)
  : BT.bytes
  =
  B.concat ciphertext plaintext

let session_content
  (peer initiator_nonce responder_nonce:BT.bytes)
  : BT.bytes
  =
  B.concat peer (B.concat initiator_nonce responder_nonce)

let lemma_decrypt_encrypt
  (secret_key randomness plaintext:BT.bytes)
  : Lemma
      (ensures
        B.pke_dec secret_key
          (ciphertext_term
            (public_key_term secret_key)
            randomness plaintext) ==
        Some plaintext)
  =
  B.pke_dec_enc secret_key randomness plaintext

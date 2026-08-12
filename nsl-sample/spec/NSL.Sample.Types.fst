module NSL.Sample.Types

(** Minimal concrete vocabulary for the fresh NSL model. *)

module Seq = FStar.Seq
module U8 = FStar.UInt8

type byte = U8.t
type bytes = Seq.seq byte
type lbytes (n:nat) = value:bytes { Seq.length value == n }

let principal_length : nat = 4
let nonce_length : nat = 8
let pke_randomness_length : nat = 8
let ciphertext_length : nat = 32

type principal = lbytes principal_length
type nonce = lbytes nonce_length
type pke_randomness = lbytes pke_randomness_length
type ciphertext = lbytes ciphertext_length

noeq
type plaintext =
  | PlainMessage1:
      initiator_nonce:nonce ->
      initiator:principal ->
      plaintext
  | PlainMessage2:
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      responder:principal ->
      plaintext
  | PlainMessage3:
      responder_nonce:nonce ->
      plaintext

type role =
  | Initiator
  | Responder

type phase =
  | InitiatorReady
  | InitiatorWaiting
  | InitiatorComplete
  | ResponderReady
  | ResponderWaiting
  | ResponderComplete

noeq
type endpoint_state = {
  role: role;
  phase: phase;
  me: principal;
  peer: option principal;
  initiator_nonce: option nonce;
  responder_nonce: option nonce;
}

let initiator_initial (me peer:principal) : endpoint_state = {
  role = Initiator;
  phase = InitiatorReady;
  me;
  peer = Some peer;
  initiator_nonce = None;
  responder_nonce = None;
}

let responder_initial (me:principal) : endpoint_state = {
  role = Responder;
  phase = ResponderReady;
  me;
  peer = None;
  initiator_nonce = None;
  responder_nonce = None;
}

type local_event =
  | Start

noeq
type local_output =
  | SessionEstablished:
      peer:principal ->
      initiator_nonce:nonce ->
      responder_nonce:nonce ->
      local_output

noeq
type fresh_value =
  | FreshNonce:
      value:nonce ->
      fresh_value
  | FreshRandomness:
      value:pke_randomness ->
      fresh_value

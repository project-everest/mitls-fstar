module DH.Sample.Types

(** Minimal concrete vocabulary for the fresh ISO-DH model. *)

module Seq = FStar.Seq
module U8 = FStar.UInt8

type byte = U8.t
type bytes = Seq.seq byte
type lbytes (n:nat) = value:bytes { Seq.length value == n }

let principal_length : nat = 4
let scalar_length : nat = 4
let share_length : nat = 4
let signature_length : nat = 8
let secret_length : nat = 8

type principal = lbytes principal_length
type scalar = lbytes scalar_length
type share = lbytes share_length
type signature = lbytes signature_length
type session_key = lbytes secret_length

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
  role:
    role;
  phase:
    phase;
  me:
    principal;
  peer:
    option principal;
  my_scalar:
    option scalar;
  my_share:
    option share;
  peer_share:
    option share;
  key:
    option session_key;
}

let initiator_initial (me peer:principal) : endpoint_state = {
  role = Initiator;
  phase = InitiatorReady;
  me = me;
  peer = Some peer;
  my_scalar = None;
  my_share = None;
  peer_share = None;
  key = None;
}

let responder_initial (me:principal) : endpoint_state = {
  role = Responder;
  phase = ResponderReady;
  me = me;
  peer = None;
  my_scalar = None;
  my_share = None;
  peer_share = None;
  key = None;
}

(** Starting contains no randomness; the selected scalar belongs to the rule. *)
type local_event =
  | Start

noeq
type local_output =
  | SessionEstablished:
      peer:principal ->
      key:session_key ->
      local_output

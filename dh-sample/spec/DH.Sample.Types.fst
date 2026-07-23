module DH.Sample.Types

(**
  DH.Sample.Types — foundational data types for a small, self-contained
  Diffie–Hellman authenticated key-exchange sample (the "ISO-DH" three-message
  flow), specified purely and machine-checked by F*.

  This module is DELIBERATELY standalone: it depends only on low-level FStar
  libraries and nothing from any Dolev–Yao / DY* development.  It fixes the
  abstract byte material used throughout the sample and the endpoint-state /
  event / output vocabulary consumed by the protocol state machine.

  Design choices for a *small sample*:
    * All cryptographic material is modelled as FIXED-SIZE byte sequences
      (`lbytes n`).  This keeps wire formats length-delimited by construction
      and makes the parse/serialize round-trip proofs tractable.
    * Principals are 4-byte abstract identifiers.
    * DH scalars/shares are 4 bytes, signatures are 8 bytes, derived session
      secrets are 8 bytes.  These sizes are arbitrary but concrete; the proofs
      do not rely on the specific numbers beyond their being fixed.
*)

module Seq = FStar.Seq
module U8  = FStar.UInt8

(** A byte is a machine byte; a byte string is an F* sequence of bytes. *)
type byte  = U8.t
type bytes = Seq.seq byte

(** Length-indexed byte strings: the workhorse fixed-size abstraction. *)
type lbytes (n:nat) = b:bytes { Seq.length b == n }

(** ── Fixed field sizes (bytes) ─────────────────────────────────────────── *)

let principal_len : nat = 4   (* size of a principal identifier            *)
let scalar_len    : nat = 4   (* size of a DH private exponent (scalar)    *)
let share_len     : nat = 4   (* size of a DH public share g^x             *)
let sig_len       : nat = 8   (* size of a signature                       *)
let secret_len    : nat = 8   (* size of a derived shared secret / key     *)

(** ── Cryptographic material (all fixed-size, abstract byte blobs) ──────── *)

(** A principal identity (e.g., "A" or "B" in the informal protocol). *)
type principal = lbytes principal_len

(** A DH private exponent x (kept secret by an endpoint). *)
type dh_scalar = lbytes scalar_len

(** A DH public share g^x transmitted on the wire. *)
type dh_share  = lbytes share_len

(** A signature Sign_P(...) produced by principal P. *)
type signature = lbytes sig_len

(** The shared secret / session key derived from a completed exchange. *)
type shared_secret = lbytes secret_len

(** ── Roles and phases ──────────────────────────────────────────────────── *)

(**
  The two roles in the exchange.  `Initiator` is party A (sends message 1),
  `Responder` is party B (answers with message 2).
*)
type role =
  | Initiator
  | Responder

(**
  The per-endpoint control-flow phase.  Each role walks a small linear chain
  of phases; the state machine (DH.Sample.StateMachine) drives these.

    Initiator:  Init_Start ──(gen/send msg1)──▶ Init_Wait2
                Init_Wait2 ──(recv msg2, send msg3)──▶ Init_Done

    Responder:  Resp_Start ──(recv msg1, gen/send msg2)──▶ Resp_Wait3
                Resp_Wait3 ──(recv msg3)──▶ Resp_Done
*)
type phase =
  | Init_Start   (* initiator: nothing sent yet                            *)
  | Init_Wait2   (* initiator: msg1 sent, awaiting msg2                    *)
  | Init_Done    (* initiator: verified msg2, sent msg3, session complete  *)
  | Resp_Start   (* responder: nothing received yet                       *)
  | Resp_Wait3   (* responder: msg1 received, msg2 sent, awaiting msg3     *)
  | Resp_Done    (* responder: verified msg3, session complete            *)

(** ── Endpoint state ────────────────────────────────────────────────────── *)

(**
  The complete local state of one protocol endpoint.  Fields that are only
  meaningful after a certain phase are wrapped in `option`, and the phase
  discipline (enforced by the step relation) determines when they are `Some`.

    * `ep_role`        : which role this endpoint plays (never changes);
    * `ep_phase`       : current control-flow phase;
    * `ep_me`          : this endpoint's own identity;
    * `ep_peer`        : the peer's identity (learned/known once engaged);
    * `ep_scalar`      : this endpoint's ephemeral secret exponent x/y;
    * `ep_my_share`    : this endpoint's own share g^x/g^y;
    * `ep_peer_share`  : the peer's share, once received;
    * `ep_key`         : the derived session key, once the exchange completes.
*)
noeq
type endpoint_state = {
  ep_role       : role;
  ep_phase      : phase;
  ep_me         : principal;
  ep_peer       : option principal;
  ep_scalar     : option dh_scalar;
  ep_my_share   : option dh_share;
  ep_peer_share : option dh_share;
  ep_key        : option shared_secret;
}

(** The pristine initiator state for identity [me] (targeting peer [peer]).

    The initiator knows whom it wishes to talk to up front (the "A -> B"
    convention of the informal protocol), so `ep_peer` starts as `Some peer`. *)
let initial_initiator (me:principal) (peer:principal) : endpoint_state = {
  ep_role       = Initiator;
  ep_phase      = Init_Start;
  ep_me         = me;
  ep_peer       = Some peer;
  ep_scalar     = None;
  ep_my_share   = None;
  ep_peer_share = None;
  ep_key        = None;
}

(** The pristine responder state for identity [me].

    The responder does not know its peer until message 1 arrives, so
    `ep_peer` starts as `None`. *)
let initial_responder (me:principal) : endpoint_state = {
  ep_role       = Responder;
  ep_phase      = Resp_Start;
  ep_me         = me;
  ep_peer       = None;
  ep_scalar     = None;
  ep_my_share   = None;
  ep_peer_share = None;
  ep_key        = None;
}

(** ── Local events and outputs ──────────────────────────────────────────── *)

(**
  Non-wire (local) stimuli that drive an endpoint.  In this sample the only
  local stimulus is a *start* signal that also supplies the freshly generated
  ephemeral scalar (modelling key generation happening outside the protocol
  proper).  The responder generates its scalar reactively when message 1
  arrives (see the step relation), so it needs no separate local start event.
*)
type local_event =
  | StartInitiator : scalar:dh_scalar -> local_event

(**
  Local outputs an endpoint may emit.  The single interesting output is the
  signal that a session key has been established, carrying the peer identity
  and the derived key.  This is the observable "success" of the exchange.
*)
type local_output =
  | SessionEstablished : peer:principal -> key:shared_secret -> local_output

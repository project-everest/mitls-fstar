module TLS13.Impl.Client.DrainLoop

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module D = TLS13.Impl.Client.Drain
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

(**
  Running the internal protected-handshake drain to completion.

  [C.process_pending_protected_handshake] applies at most one pending handshake
  message per call, which is the right granularity for an event loop that polls
  (the client engine drains across successive polls).  A driver that owns the
  socket has no such loop, so it must drain here.

  The loop is bounded by [drain_fuel].  Every handshake message carries a
  four-byte header, so a protected record whose plaintext is at most
  [max_handshake_flight_len] bytes cannot contain more messages than that;
  the bound is therefore never reached in practice and exists only to make
  progress manifest.

  That bound is discharged by the loop's [decreases] measure, so the drain is
  proved terminating and [drain_pending] is an [stt] (not [stt_div]) function.
  A [while] with no measure is divergent in Pulse and would force both this
  function and every caller onto the divergent fragment.

  The fuel is therefore the loop's *only* control: every exit path zeroes
  [remaining] rather than clearing a separate flag, which keeps the measure a
  single reference read.  (Pulse's specification purifier does not descend into
  the branches of an [if], so a measure of the form
  [if !keep_going then ... else ...] cannot be elaborated.)  Fuel exhaustion and
  a completed drain are still distinguished, by [quiescent]: it is set only when
  the client reports no pending message.
**)

let drain_fuel : SZ.t = 16384sz

#push-options "--z3refresh --split_queries always --fuel 1 --ifuel 1"
fn drain_pending (c:C.client) (empty:array U8.t)
  requires CR.connection_exactly c 'st0 **
           pts_to empty 'empty_bytes **
           pure (Seq.equal (Ghost.reveal 'empty_bytes) B.empty /\
                 CT.client_end_to_end_invariant 'st0)
  returns quiet:bool
  ensures exists* st1.
          CR.connection_exactly c st1 **
          pts_to empty 'empty_bytes **
          pure (D.drained (Ghost.reveal 'st0) st1 /\
                CT.client_end_to_end_invariant st1 /\
                (quiet ==> ~ (D.internal_pending st1)))
{
  D.lemma_drained_refl (Ghost.reveal 'st0);
  let mut remaining = drain_fuel;
  let mut quiescent = false;
  while (
    let r = !remaining;
    SZ.gt r 0sz
  )
  invariant exists* st_cur rv qv.
    CR.connection_exactly c st_cur **
    pts_to empty 'empty_bytes **
    R.pts_to remaining rv **
    R.pts_to quiescent qv **
    pure (D.drained (Ghost.reveal 'st0) st_cur /\
          CT.client_end_to_end_invariant st_cur /\
          (qv ==> ~ (D.internal_pending st_cur)))
  decreases (SZ.v !remaining)
  {
    with st_cur. assert (CR.connection_exactly c st_cur);
    let r = !remaining;
    remaining := SZ.sub r 1sz;
    let pending = C.process_pending_protected_handshake c empty;
    with st_next. assert (CR.connection_exactly c st_next);
    match pending {
      None -> {
        D.lemma_pending_none_quiescent st_cur st_next;
        quiescent := true;
        remaining := 0sz
      }
      Some resp -> {
        if (resp.CT.status = CT.StepOk) {
          assert (pure (CT.pending_protected_handshake_result_correct
            st_cur st_next (Some resp)));
          assert (pure (resp.CT.status == CT.StepOk));
          assert (pure (D.drain_step st_cur st_next));
          assert (pure (D.drained (Ghost.reveal 'st0) st_cur));
          D.lemma_drained_snoc (Ghost.reveal 'st0) st_cur st_next;
          assert (pure (D.drained (Ghost.reveal 'st0) st_next));
          assert (pure (CT.client_end_to_end_invariant st_next));
          quiescent := false
        } else {
          assert (pure (st_next == st_cur));
          quiescent := false;
          remaining := 0sz
        }
      }
    }
  };
  let q = !quiescent;
  q
}
#pop-options

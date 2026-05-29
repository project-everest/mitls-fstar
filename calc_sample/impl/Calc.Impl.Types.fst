module Calc.Impl.Types

#lang-pulse

module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module Arr = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Log

(** Server state: concrete stack + monotonic ghost log **)
noeq
type server_state = {
  stack: array U32.t;              // Concrete stack (max 10 elements)
  size: ref SZ.t;                   // Concrete size
  ghost_log: MR.mref log_evolves;  // Monotonic ghost log
}

(** Knowledge that server has exact log state **)
[@@pulse_unfold]
let server_exactly (srv: server_state) (log: calc_log) =
  exists* (stack_bytes: Ghost.erased (Seq.seq U32.t)) (sz: SZ.t).
    Arr.pts_to srv.stack stack_bytes **
    R.pts_to srv.size sz **
    MR.pts_to srv.ghost_log #1.0R log **
    pure (
      Seq.length (Ghost.reveal stack_bytes) == 10 /\
      SZ.v sz <= 10 /\
      SZ.v sz == L.length log.current_state /\
      // Concrete stack matches ghost state (stack is reversed!)
      // stack[0..sz] contains current_state in reverse order
      (forall (i:nat{i < SZ.v sz}).
         U32.v (Seq.index (Ghost.reveal stack_bytes) i) == 
         L.index log.current_state (SZ.v sz - 1 - i)) /\
      // Wire-to-semantic correspondence is always maintained
      log_consistent log
    )

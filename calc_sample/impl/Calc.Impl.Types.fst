module Calc.Impl.Types

#lang-pulse

module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module MR = Pulse.Lib.MonotonicGhostRef
module S = Pulse.Lib.Slice
module LP = LowParse.Spec
module Resp = Calc.Wire.Generated.Response

open Calc.Log

(** Server state: heap-allocated stack + monotonic ghost log **)
noeq
type server_state = {
  stack: Vec.vec U32.t;             // Heap-allocated stack (max 10 elements)
  size: Vec.vec SZ.t;               // Heap-allocated size (single element)
  ghost_log: MR.mref log_evolves;  // Monotonic ghost log
}

(** Knowledge that server has exact log state **)
[@@pulse_unfold]
let server_exactly (srv: server_state) (log: calc_log) =
  exists* (stack_bytes: Ghost.erased (Seq.seq U32.t)) (size_seq: Ghost.erased (Seq.seq SZ.t)).
    Vec.pts_to srv.stack stack_bytes **
    Vec.pts_to srv.size size_seq **
    MR.pts_to srv.ghost_log #1.0R log **
    pure (
      Seq.length (Ghost.reveal stack_bytes) == 10 /\
      Seq.length (Ghost.reveal size_seq) == 1 /\
      (let sz = Seq.index (Ghost.reveal size_seq) 0 in
       SZ.v sz <= 10 /\
       SZ.v sz == L.length log.current_state /\
       // Concrete stack matches ghost state (stack is reversed!)
       // stack[0..sz] contains current_state in reverse order
       (forall (i:nat{i < SZ.v sz}).
          Seq.index (Ghost.reveal stack_bytes) i ==
          L.index log.current_state (SZ.v sz - 1 - i))) /\
      // Wire-to-semantic correspondence is always maintained
      log_consistent log
    )

(** Shared response writer.

    Serializes a generated [response] record into a 5-byte slice using the
    QuackyDucky-generated [response_writer] (an [l2r_leaf_writer]).  The
    postcondition exposes that the resulting bytes are exactly
    [serialize_response resp], which is what each handler needs to discharge
    the serialize precondition of [lemma_step_log_consistent]. **)
fn write_response (resp_slice: Pulse.Lib.Slice.slice FStar.UInt8.t) (resp: Calc.Wire.Generated.Response.response)
  requires Pulse.Lib.Slice.pts_to resp_slice 'rb ** pure (Seq.length 'rb == 5)
  ensures exists* (rb1: bytes). Pulse.Lib.Slice.pts_to resp_slice rb1 **
    pure (Seq.length rb1 == 5 /\ rb1 `Seq.equal` serialize_response resp)
{
  Pulse.Lib.Slice.pts_to_len resp_slice;
  LP.serialize_length Resp.response_serializer resp;
  let _n = Resp.response_writer resp resp_slice 0sz;
  with rb1. assert (Pulse.Lib.Slice.pts_to resp_slice rb1);
  // The l2r_leaf_writer postcondition gives Seq.slice rb1 0 5 == bare_serialize resp,
  // and bare_serialize == serialize == serialize_response; rb1 has length 5 so the
  // full slice is rb1 itself.
  assert (pure (rb1 `Seq.equal` serialize_response resp));
  ()
}

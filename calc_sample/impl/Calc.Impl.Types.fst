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
module R = Pulse.Lib.Reference
module LP = LowParse.Spec
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators
module PPB = LowParse.PulseParse.Base
module Resp = Calc.Wire.Generated.Response
module RespType = Calc.Wire.Generated.RespType

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

(** Introduce the generated [response_vmatch] relating the low-level pair
    [(tag, value)] to the identical "mid" pair.  Because both child predicates are
    [eq_as_slprop] (pure equalities), the relation holds reflexively from [emp].
    This is the only place the response vmatch structure is exposed. **)
ghost
fn intro_response_vmatch (tag: RespType.respType) (value: U32.t)
  requires emp
  ensures Resp.response_vmatch (tag, value) (tag, value)
{
  fold (LPS.eq_as_slprop RespType.respType tag tag);
  rewrite (LPS.eq_as_slprop RespType.respType tag tag)
      as (RespType.respType_vmatch tag tag);
  fold (LPS.eq_as_slprop U32.t value value);
  fold (LPC.vmatch_pair RespType.respType_vmatch (LPS.eq_as_slprop U32.t)
          (tag, value) (tag, value));
  rewrite (LPC.vmatch_pair RespType.respType_vmatch (LPS.eq_as_slprop U32.t)
          (tag, value) (tag, value))
      as (Resp.response_vmatch (tag, value) (tag, value));
}

(** Shared response writer (extraction-ready, COPYFUL path).

    Serializes the response [(tag, value)] into a 5-byte slice using the
    QuackyDucky-generated COPYFUL writer [Resp.write_response] (an
    [l2r_safe_writer]) which operates on the low-level representation
    [(respType & U32.t)] -- both extractable -- rather than the [noextract]
    [response] record.  The postcondition still exposes that the resulting bytes
    are exactly [serialize_response { tag; value }], which is what each handler
    needs to discharge the serialize precondition of [lemma_step_log_consistent].

    The slice has length 5 == the serialized size, so the safe writer never
    fails (err == false) and the full slice equals the serialization. **)
fn write_response (resp_slice: Pulse.Lib.Slice.slice FStar.UInt8.t) (tag: RespType.respType) (value: U32.t)
  requires Pulse.Lib.Slice.pts_to resp_slice 'rb ** pure (Seq.length 'rb == 5)
  ensures exists* (rb1: bytes). Pulse.Lib.Slice.pts_to resp_slice rb1 **
    pure (Seq.length rb1 == 5 /\ rb1 `Seq.equal` serialize_response ({ Resp.tag = tag; Resp.value = value }))
{
  let x : Resp.response_lowtype = (tag, value);
  intro_response_vmatch tag value;
  rewrite (Resp.response_vmatch (tag, value) (tag, value))
      as (Resp.response_vmatch x (Ghost.reveal (Ghost.hide #Resp.response_mid (tag, value))));
  S.pts_to_len resp_slice;
  LP.serialize_length Resp.response_serializer ({ Resp.tag = tag; Resp.value = value });
  let mut perr = false;
  let _sz = Resp.write_response x #(Ghost.hide #Resp.response_mid (tag, value)) resp_slice #'rb perr;
  // From the safe-writer postcondition: response_conv (tag,value) == Some {tag;value},
  // the serialized length is 5, and the 5-byte slice now holds the serialization.
  with v' err. assert (S.pts_to resp_slice v' ** R.pts_to perr err);
  S.pts_to_len resp_slice;
  assert (pure (Resp.response_conv (tag, value) == Some ({ Resp.tag = tag; Resp.value = value })));
  rewrite (Resp.response_vmatch x (Ghost.reveal (Ghost.hide #Resp.response_mid (tag, value))))
      as (Resp.response_vmatch (tag, value) (tag, value));
  drop_ (Resp.response_vmatch (tag, value) (tag, value));
  ()
}

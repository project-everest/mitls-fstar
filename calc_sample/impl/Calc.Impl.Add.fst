module Calc.Impl.Add

#lang-pulse

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Spec
open Calc.Log
open Calc.Impl.Types
open Calc.Wire.Generated.OpType
open Calc.Wire.Generated.RespType
open Calc.Wire.Generated.Request
open Calc.Wire.Generated.Response

(** Process an Add request: pop two operands, push their (wrapping) sum. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_add
  (srv: server_state)
  (resp_slice: Pulse.Lib.Slice.slice U8.t)
  (#log0: erased calc_log)
  (#req: erased request)
  (#req_bytes: erased (b: bytes { Seq.length b == 5 }))
requires
  server_exactly srv log0 **
  Pulse.Lib.Slice.pts_to resp_slice 'rb **
  pure (
    Seq.length 'rb == 5 /\
    Seq.length req_bytes == 5 /\
    parse_request req_bytes == Some (Ghost.reveal req) /\
    (Ghost.reveal req).op == Add
  )
ensures exists* (resp_bytes1: bytes) (log1: calc_log).
  server_exactly srv log1 **
  Pulse.Lib.Slice.pts_to resp_slice resp_bytes1 **
  pure (
    Seq.length resp_bytes1 == 5 /\
    log1 == step_log req req_bytes resp_bytes1 log0 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1
  )
{
  unfold (server_exactly srv log0);
  with sb size_seq. _;
  let csz = Vec.op_Array_Access srv.size 0sz;

  if SZ.gte csz 2sz {
    // Add success: pop two, push wrapping sum
    let v_top = Vec.op_Array_Access srv.stack (SZ.sub csz 1sz);     // x (top)
    let v_second = Vec.op_Array_Access srv.stack (SZ.sub csz 2sz);  // y (second)
    assert (pure (v_top == L.index log0.current_state 0));
    assert (pure (v_second == L.index log0.current_state 1));
    let result = U32.add_mod v_top v_second;                       // add_mod x y, as in step
    Vec.op_Array_Assignment srv.stack (SZ.sub csz 2sz) result;
    Vec.op_Array_Assignment srv.size 0sz (SZ.sub csz 1sz);
    Calc.Impl.Types.write_response resp_slice Ok 0ul;
    with resp_bytes1. _;

    assert (pure (snd (step log0.current_state (Ghost.reveal req)) == ({ tag = Ok; value = 0ul })));
    assert (pure (serialize_response (snd (step log0.current_state (Ghost.reveal req))) `Seq.equal` resp_bytes1));

    lemma_step_log_consistent (Ghost.reveal req) req_bytes resp_bytes1 log0;
    lemma_step_log_evolves (Ghost.reveal req) req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log (Ghost.reveal req) req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log (Ghost.reveal req) req_bytes resp_bytes1 log0))
  } else {
    // Add error: stack underflow
    Calc.Impl.Types.write_response resp_slice Error 0ul;
    with resp_bytes1. _;

    assert (pure (snd (step log0.current_state (Ghost.reveal req)) == ({ tag = Error; value = 0ul })));
    assert (pure (serialize_response (snd (step log0.current_state (Ghost.reveal req))) `Seq.equal` resp_bytes1));

    lemma_step_log_consistent (Ghost.reveal req) req_bytes resp_bytes1 log0;
    lemma_step_log_evolves (Ghost.reveal req) req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log (Ghost.reveal req) req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log (Ghost.reveal req) req_bytes resp_bytes1 log0))
  }
}
#pop-options

module Calc.Impl.Div

#lang-pulse

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq
module L = FStar.List.Tot

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module Arr = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module MR = Pulse.Lib.MonotonicGhostRef

open Calc.Spec
open Calc.Wire
open Calc.Log
open Calc.Impl.Types

fn write_ok_response (resp_buf: array U8.t)
  requires Arr.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Arr.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\ 
      Seq.index resp_bytes1 0 == 0uy /\
      Seq.index resp_bytes1 1 == 0uy /\
      Seq.index resp_bytes1 2 == 0uy /\
      Seq.index resp_bytes1 3 == 0uy /\
      Seq.index resp_bytes1 4 == 0uy
    )
{
  resp_buf.(0sz) <- 0uy;
  resp_buf.(1sz) <- 0uy;
  resp_buf.(2sz) <- 0uy;
  resp_buf.(3sz) <- 0uy;
  resp_buf.(4sz) <- 0uy
}

fn write_error_response (resp_buf: array U8.t)
  requires Arr.pts_to resp_buf 'bytes ** pure (Seq.length 'bytes == 5)
  ensures exists* (resp_bytes1: bytes).
    Arr.pts_to resp_buf resp_bytes1 **
    pure (
      Seq.length resp_bytes1 == 5 /\ 
      Seq.index resp_bytes1 0 == 2uy /\
      Seq.index resp_bytes1 1 == 0uy /\
      Seq.index resp_bytes1 2 == 0uy /\
      Seq.index resp_bytes1 3 == 0uy /\
      Seq.index resp_bytes1 4 == 0uy
    )
{
  resp_buf.(0sz) <- 2uy;
  resp_buf.(1sz) <- 0uy;
  resp_buf.(2sz) <- 0uy;
  resp_buf.(3sz) <- 0uy;
  resp_buf.(4sz) <- 0uy
}

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_div
  (srv: server_state)
  (req_buf: array U8.t)
  (resp_buf: array U8.t)
  (#log0: erased calc_log)
  (#req_bytes: erased bytes{Seq.length req_bytes == 5})
requires
  server_exactly srv log0 **
  Arr.pts_to req_buf req_bytes **
  Arr.pts_to resp_buf 'resp_bytes **
  pure (
    parse_request req_bytes == Some Div /\
    Seq.length 'resp_bytes == 5
  )
ensures exists* (resp_bytes1: bytes{Seq.length resp_bytes1 == 5}) (log1: calc_log).
  server_exactly srv log1 **
  Arr.pts_to req_buf req_bytes **
  Arr.pts_to resp_buf resp_bytes1 **
  pure (
    log1 == step_log_div req_bytes resp_bytes1 log0 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1
  )
{
  unfold (server_exactly srv log0);
  with sb sz. _;
  let csz = !srv.size;

  if SZ.gte csz 2sz {
    let val1 = srv.stack.(SZ.sub csz 2sz);  // y (second from top)
    let val2 = srv.stack.(SZ.sub csz 1sz);  // x (top)

    assert (pure (U32.v val1 == L.index log0.current_state 1));
    assert (pure (U32.v val2 == L.index log0.current_state 0));

    if U32.eq val2 0ul {
      // Div error: divide by zero
      write_error_response resp_buf;
      with resp_bytes1. _;
      
      assert (pure (
        (step_log_div req_bytes resp_bytes1 log0).current_state ==
        log0.current_state
      ));
      
      // Establish serialize_response correspondence
      Calc.Wire.lemma_serialize_error_bytes resp_bytes1;
      assert (pure (snd (step log0.current_state Div) == Error));
      assert (pure (serialize_response (snd (step log0.current_state Div)) `Seq.equal` resp_bytes1));
      
      lemma_step_log_div_consistent req_bytes resp_bytes1 log0;
      lemma_step_log_div_evolves req_bytes resp_bytes1 log0;
      MR.update srv.ghost_log (step_log_div req_bytes resp_bytes1 log0);
      fold (server_exactly srv (step_log_div req_bytes resp_bytes1 log0))
    } else {
      // Div success: pop two, divide y by x, push result
      let result = U32.div val1 val2;
      srv.stack.(SZ.sub csz 2sz) <- result;
      srv.size := SZ.sub csz 1sz;
      write_ok_response resp_buf;
      with resp_bytes1. _;
      
      assert (pure (
        (step_log_div req_bytes resp_bytes1 log0).current_state ==
        (L.index log0.current_state 1 / L.index log0.current_state 0) ::
        L.tl (L.tl log0.current_state)
      ));
      
      // Establish serialize_response correspondence
      Calc.Wire.lemma_serialize_ok_bytes resp_bytes1;
      assert (pure (snd (step log0.current_state Div) == Ok));
      assert (pure (serialize_response (snd (step log0.current_state Div)) `Seq.equal` resp_bytes1));
      
      lemma_step_log_div_consistent req_bytes resp_bytes1 log0;
      lemma_step_log_div_evolves req_bytes resp_bytes1 log0;
      MR.update srv.ghost_log (step_log_div req_bytes resp_bytes1 log0);
      fold (server_exactly srv (step_log_div req_bytes resp_bytes1 log0))
    }
  } else {
    // Div error: stack underflow
    write_error_response resp_buf;
    with resp_bytes1. _;
    
    assert (pure (
      (step_log_div req_bytes resp_bytes1 log0).current_state ==
      log0.current_state
    ));
    
    // Establish serialize_response correspondence
    Calc.Wire.lemma_serialize_error_bytes resp_bytes1;
    assert (pure (snd (step log0.current_state Div) == Error));
    assert (pure (serialize_response (snd (step log0.current_state Div)) `Seq.equal` resp_bytes1));
    
    lemma_step_log_div_consistent req_bytes resp_bytes1 log0;
    lemma_step_log_div_evolves req_bytes resp_bytes1 log0;
    MR.update srv.ghost_log (step_log_div req_bytes resp_bytes1 log0);
    fold (server_exactly srv (step_log_div req_bytes resp_bytes1 log0))
  }
}
#pop-options

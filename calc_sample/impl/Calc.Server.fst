module Calc.Server

#lang-pulse

(**
  Modular Pulse implementation with separate handler modules.

  The request is parsed ONCE here with the QuackyDucky-generated
  [request_reader]; the parsed [request] value is then dispatched (as a ghost
  together with the raw request bytes) to the per-op handlers, each of which
  produces the wire response with the generated [response_writer] and advances
  the monotonic ghost log by the single uniform [step_log].
**)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Seq = FStar.Seq

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module MR = Pulse.Lib.MonotonicGhostRef
module S = Pulse.Lib.Slice
module Trade = Pulse.Lib.Trade.Util
module PPB = LowParse.PulseParse.Base
module LPB = LowParse.Spec.Base
module LPS = LowParse.Pulse.Base
module LPC = LowParse.Pulse.Combinators

open Calc.Spec
open Calc.Log
open Calc.Impl.Types
open Calc.Wire.Generated.OpType
open Calc.Wire.Generated.Request

// Import all handlers
module Push = Calc.Impl.Push
module Peek = Calc.Impl.Peek
module Add = Calc.Impl.Add
module Sub = Calc.Impl.Sub
module Mul = Calc.Impl.Mul
module Div = Calc.Impl.Div

(** Maximum stack size **)
let max_stack_size : SZ.t = 10sz

(** Create new server with empty stack and initial ghost log **)
fn new_server ()
  requires emp
  returns srv: server_state
  ensures server_exactly srv initial_log
{
  lemma_initial_log_consistent ();
  let stack = Vec.alloc 0ul 10sz;
  let size_vec = Vec.alloc 0sz 1sz;  // Single-element vector for size
  let ghost_log = MR.alloc #_ #log_evolves initial_log;
  let srv = {
    stack = stack;
    size = size_vec;
    ghost_log = ghost_log;
  };

  // Rewrite predicates to match srv fields
  with stack_bytes. rewrite (Vec.pts_to stack stack_bytes) as (Vec.pts_to srv.stack stack_bytes);
  with size_seq. rewrite (Vec.pts_to size_vec size_seq) as (Vec.pts_to srv.size size_seq);
  rewrite (MR.pts_to ghost_log #1.0R initial_log) as (MR.pts_to srv.ghost_log #1.0R initial_log);

  fold (server_exactly srv initial_log);
  srv
}

(**
  Recover the field equalities from the COPYFUL reader's packed read-result.

  [read_request] returns the low-level pair [reslow : (opType & U32.t)] together
  with [vmatch_conv request_vmatch request_conv reslow req] relating it to the
  ghost [request] record [req].  Unfolding the [vmatch_pair]/[eq_as_slprop]
  structure (the reverse of [intro_response_vmatch]) and the [request_conv]
  exposes [fst reslow == req.op /\ snd reslow == req.operand], which is all the
  dispatcher needs.  This confines the request-side vmatch plumbing here.
**)
let lemma_request_conv (vm: request_mid) (req: request)
  : Lemma
    (requires request_conv vm == Some req)
    (ensures req.op == fst vm /\ req.operand == snd vm)
  = ()

ghost
fn elim_request_vmatch (reslow: request_lowtype) (#req_value: erased request)
  requires PPB.vmatch_conv request_vmatch request_conv reslow req_value
  ensures pure (fst reslow == (Ghost.reveal req_value).op /\
                snd reslow == (Ghost.reveal req_value).operand)
{
  PPB.elim_vmatch_conv request_vmatch request_conv reslow req_value;
  with vm. assert (request_vmatch reslow vm **
                   pure (request_conv vm == Some (Ghost.reveal req_value)));
  rewrite (request_vmatch reslow vm)
      as (LPC.vmatch_pair opType_vmatch (LPS.eq_as_slprop U32.t) reslow vm);
  unfold (LPC.vmatch_pair opType_vmatch (LPS.eq_as_slprop U32.t) reslow vm);
  rewrite (opType_vmatch (fst reslow) (fst vm))
      as (LPS.eq_as_slprop opType (fst reslow) (fst vm));
  unfold (LPS.eq_as_slprop opType (fst reslow) (fst vm));
  unfold (LPS.eq_as_slprop U32.t (snd reslow) (snd vm));
  lemma_request_conv vm (Ghost.reveal req_value);
}

(**
  Dispatch the request -- given as the low-level [(opType & U32.t)] pair [reslow]
  (extractable) plus the ghost [request] record [req] it relates to -- to the
  matching handler.  Factored as its own function so the [match] is a tail
  conditional and Pulse can take each handler's postcondition as the result.
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn dispatch
  (srv: server_state)
  (reslow: request_lowtype)
  (resp_slice: S.slice U8.t)
  (#log0: erased calc_log)
  (#req: erased request)
  (#req_bytes: erased (b: bytes { Seq.length b == 5 }))
requires
  server_exactly srv log0 **
  S.pts_to resp_slice 'rb **
  pure (
    Seq.length 'rb == 5 /\
    Seq.length req_bytes == 5 /\
    parse_request req_bytes == Some (Ghost.reveal req) /\
    fst reslow == (Ghost.reveal req).op /\
    snd reslow == (Ghost.reveal req).operand
  )
ensures exists* (resp_bytes1: bytes) (log1: calc_log).
  server_exactly srv log1 **
  S.pts_to resp_slice resp_bytes1 **
  pure (
    Seq.length resp_bytes1 == 5 /\
    log1 == step_log req req_bytes resp_bytes1 log0 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1
  )
{
  match fst reslow {
    Push -> {
      Push.process_push srv (snd reslow) resp_slice #log0 #req #req_bytes;
    }
    Peek -> {
      Peek.process_peek srv resp_slice #log0 #req #req_bytes;
    }
    Add -> {
      Add.process_add srv resp_slice #log0 #req #req_bytes;
    }
    Sub -> {
      Sub.process_sub srv resp_slice #log0 #req #req_bytes;
    }
    Mul -> {
      Mul.process_mul srv resp_slice #log0 #req #req_bytes;
    }
    Div -> {
      Div.process_div srv resp_slice #log0 #req #req_bytes;
    }
  }
}
#pop-options

(**
  process_request: modular dispatcher.

  1. Read the request from [req_buf] via a slice and the generated reader.
  2. Bridge [resp_buf] to a slice.
  3. Dispatch on the parsed op to the matching handler.
  4. Bridge the response slice back to [resp_buf].
  5. Conclude single-step progression of the ghost log.
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_request
  (srv: server_state)
  (req_buf: Vec.vec U8.t)
  (resp_buf: Vec.vec U8.t)
  (#log0: erased calc_log)
requires
  server_exactly srv log0 **
  Vec.pts_to req_buf 'req_bytes **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    Seq.length 'req_bytes == 5 /\
    Seq.length 'resp_bytes == 5 /\
    parse_request 'req_bytes <> None
  )
ensures exists* (resp_bytes1: bytes) (log1: calc_log).
  server_exactly srv log1 **
  Vec.pts_to req_buf 'req_bytes **
  Vec.pts_to resp_buf resp_bytes1 **
  pure (
    log_single_step log0 log1 /\
    log1.input_bytes `Seq.equal` Seq.append log0.input_bytes 'req_bytes /\
    log1.output_bytes `Seq.equal` Seq.append log0.output_bytes resp_bytes1
  )
{
  // (a) Read the request via a slice and the generated COPYFUL reader.
  Vec.pts_to_len req_buf;
  Vec.to_array_pts_to req_buf;
  let req_slice = S.from_array (Vec.vec_to_array req_buf) 5sz;
  let req_value : Ghost.erased request = Ghost.hide (Some?.v (parse_request 'req_bytes));
  LPB.parser_kind_prop_equiv request_parser_kind request_parser;
  PPB.pts_to_parsed_intro_injective request_parser req_slice (Ghost.reveal req_value);
  let reslow = read_request req_slice;
  // reslow : (opType & U32.t); recover the field equalities to the ghost request.
  elim_request_vmatch reslow #req_value;
  Trade.elim
    (PPB.pts_to_parsed request_parser req_slice (Ghost.reveal req_value))
    (S.pts_to req_slice 'req_bytes);
  S.to_array req_slice;
  Vec.to_vec_pts_to req_buf;

  // (b) Bridge resp_buf to a slice for the handlers.
  Vec.pts_to_len resp_buf;
  Vec.to_array_pts_to resp_buf;
  let resp_slice = S.from_array (Vec.vec_to_array resp_buf) 5sz;

  // (c) Dispatch on the parsed op (low-level pair + ghost request).
  dispatch srv reslow resp_slice #log0 #req_value
    #(Ghost.hide #(b: bytes { Seq.length b == 5 }) (Ghost.reveal 'req_bytes));

  // (d) Bridge the response slice back to resp_buf.
  with resp_bytes1 log1. _;
  S.to_array resp_slice;
  Vec.to_vec_pts_to resp_buf;

  // (e) Conclude single-step progression of the ghost log.
  assert (pure (log_single_step log0 log1))
}
#pop-options

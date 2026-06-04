module TLS13.Impl.ConnectionState.Fail

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.ConnectionState
module H = TLS13.Handshake.Spec
module IM = TLS13.Impl.Messages
module K = TLS13.Keys
module KS = TLS13.KeySchedule
module M = TLS13.Messages
module MR = Pulse.Lib.MonotonicGhostRef
module Bounds = TLS13.Impl.ConnectionState.Bounds
module Model = TLS13.Impl.ConnectionState.Model
module Queries = TLS13.Impl.ConnectionState.Queries
module Repr = TLS13.Impl.ConnectionState.Repr
module Tags = TLS13.Impl.ConnectionState.Tags
module Arr = Pulse.Lib.Array
module ArrPts = Pulse.Lib.Array.PtsTo
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Ser = TLS13.Impl.Serializer
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.StateMachine
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open TLS13.Impl.ConnectionState.Bounds
open TLS13.Impl.ConnectionState.Model
open TLS13.Impl.ConnectionState.Queries
open TLS13.Impl.ConnectionState.Repr

fn mark_decode_error
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  ensures connection_exactly c (local_fail_state st0 tls_decode_error)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 50uy;

  fold (control_exactly
    c.control
    (CS.ControlFailed tls_decode_error)
    (Some tls_decode_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_decode_error).CS.model_control == CS.ControlFailed tls_decode_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_decode_error).CS.model_failure == Some tls_decode_error));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model tls_decode_error));

  lemma_local_fail_state_evolves st0 tls_decode_error;
  MR.update c.ghost_state (local_fail_state st0 tls_decode_error);
  fold (connection_exactly c (local_fail_state st0 tls_decode_error))
}

fn mark_unexpected_message
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  ensures connection_exactly c (local_fail_state st0 tls_unexpected_message_error)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);

  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 0uy;
  c.control.failure_alert := 10uy;

  fold (control_exactly
    c.control
    (CS.ControlFailed tls_unexpected_message_error)
    (Some tls_unexpected_message_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_unexpected_message_error).CS.model_control == CS.ControlFailed tls_unexpected_message_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_unexpected_message_error).CS.model_failure == Some tls_unexpected_message_error));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model tls_unexpected_message_error));

  lemma_local_fail_state_evolves st0 tls_unexpected_message_error;
  MR.update c.ghost_state (local_fail_state st0 tls_unexpected_message_error);
  fold (connection_exactly c (local_fail_state st0 tls_unexpected_message_error))
}

fn mark_bad_finished
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  ensures connection_exactly c (local_fail_state st0 tls_bad_finished_error)
{
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);
  unfold (control_exactly c.control st0.CS.cs_model.CS.model_control st0.CS.cs_model.CS.model_failure);
  c.control.control_tag := 5uy;
  c.control.failure_present := true;
  c.control.failure_code := 7uy;
  c.control.failure_alert := 0uy;
  assert (pure (Tags.tls_error_code_matches 7uy 0uy tls_bad_finished_error));
  assert (pure (Tags.control_state_matches
    5uy
    0uy
    true
    7uy
    0uy
    (CS.ControlFailed tls_bad_finished_error)));
  fold (control_exactly
    c.control
    (CS.ControlFailed tls_bad_finished_error)
    (Some tls_bad_finished_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_bad_finished_error).CS.model_control ==
                CS.ControlFailed tls_bad_finished_error));
  assert (pure ((CS.fail_model st0.CS.cs_model tls_bad_finished_error).CS.model_failure ==
                Some tls_bad_finished_error));
  fold (connection_model_exactly c (CS.fail_model st0.CS.cs_model tls_bad_finished_error));
  lemma_local_fail_state_evolves st0 tls_bad_finished_error;
  MR.update c.ghost_state (local_fail_state st0 tls_bad_finished_error);
  fold (connection_exactly c (local_fail_state st0 tls_bad_finished_error))
}

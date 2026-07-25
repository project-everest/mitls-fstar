module TLS13.Impl.ConnectionState.LocalApp

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }
open FStar.List.Tot

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module Crypto = TLS13.Crypto
module CS = TLS13.Spec.StateMachine
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
module SM = TLS13.Spec.StateMachine.ClientTrace
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

fn mark_delivered_application_data
  (c:connection_state)
  (#bytes:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
                 CS.legal_event
                   st0.CS.cs_model
                   (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)))
  ensures connection_exactly c (delivered_application_data_state st0 bytes)
{
  assert (pure (st0.CS.cs_model.CS.model_control == CS.ControlApplicationData));
  assert (pure (CS.legal_event
    st0.CS.cs_model
    (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes))));
  unfold (connection_exactly c st0);
  unfold (connection_model_exactly c st0.CS.cs_model);

  unfold (application_exactly c.application st0.CS.cs_model.CS.model_application);
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_plaintext ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_plaintext));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_source_record ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_record));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_source_offset ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_source_offset));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application.CS.app_pending_received_raw ==
                st0.CS.cs_model.CS.model_application.CS.app_pending_received_raw));
  assert (pure (TLS13.Spec.StateMachine.Correspondence.pending_application_consistent
    (delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application));
  fold (application_exactly
    c.application
    (delivered_application_data_state st0 bytes).CS.cs_model.CS.model_application);

  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_config ==
                st0.CS.cs_model.CS.model_config));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_control ==
                st0.CS.cs_model.CS.model_control));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_record ==
                st0.CS.cs_model.CS.model_record));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_handshake ==
                st0.CS.cs_model.CS.model_handshake));
  assert (pure ((delivered_application_data_state st0 bytes).CS.cs_model.CS.model_failure ==
                st0.CS.cs_model.CS.model_failure));
  fold (connection_model_exactly
    c
    (delivered_application_data_state st0 bytes).CS.cs_model);

  lemma_delivered_application_data_state_evolves st0 bytes;
  MR.update
    c.ghost_state
    (delivered_application_data_state st0 bytes);
  fold (connection_exactly c (delivered_application_data_state st0 bytes))
}

module TLS13.Impl.ConnectionState.LocalSend

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

fn write_close_notify_alert
  (alert:array U8.t)
  requires ArrPts.pts_to alert (Seq.create 2 0uy)
  ensures exists* alert_bytes.
            ArrPts.pts_to alert alert_bytes **
            pure (B.length alert_bytes == 2 /\
                  Seq.equal alert_bytes close_notify_alert_fragment)

fn write_key_update_response
  (handshake:array U8.t)
  requires ArrPts.pts_to handshake (Seq.create 5 0uy)
  ensures exists* handshake_bytes.
            ArrPts.pts_to handshake handshake_bytes **
            pure (B.length handshake_bytes == 5 /\
                  Seq.equal handshake_bytes key_update_response_fragment)

fn mark_sent_client_finished
  (c:connection_state)
  (handshake_bytes:array U8.t)
  (handshake_len:SZ.t)
  (lfin:IM.finished)
  (network_out:array U8.t)
  (written:SZ.t)
  (#fin:erased M.finished)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to handshake_bytes 'handshake_storage **
           IM.is_valid_finished lfin fin **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (can_send_client_finished st0 (Ghost.reveal fin) (Ghost.reveal raw_sent) /\
                 B.length 'handshake_storage == SZ.v handshake_len /\
                 SZ.v handshake_len == 36 /\
                 Seq.equal
                   (Ghost.reveal 'handshake_storage)
                   (W.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                 SZ.v written == 58 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_client_finished_state st0 (Ghost.reveal fin) (Ghost.reveal raw_sent)) **
          ArrPts.pts_to handshake_bytes 'handshake_storage **
          ArrPts.pts_to network_out 'network_out_bytes

fn try_send_client_finished
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* fin raw_sent network_out_bytes.
              connection_exactly c (sent_client_finished_state st0 fin raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    58 <= B.length network_out_bytes /\
                    can_send_client_finished st0 fin raw_sent /\
                    Seq.equal raw_sent (Seq.slice network_out_bytes 0 58))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)

fn mark_sent_application_data_after_record_advanced
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 B.length 'payload_bytes == SZ.v payload_len /\
                 can_send_application_data
                   st0
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == SZ.v payload_len + 22 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_application_data_state
              st0
              (Ghost.reveal 'payload_bytes)
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to payload 'payload_bytes **
          ArrPts.pts_to network_out 'network_out_bytes

fn mark_sent_close_notify_after_record_advanced
  (c:connection_state)
  (network_out:array U8.t)
  (written:SZ.t)
  (#raw_sent:erased B.bytes)
  (#st0:erased CS.connection_state)
  requires MR.pts_to c.ghost_state #1.0R st0 **
           connection_config_exactly c.config st0.CS.cs_model.CS.model_config **
           control_exactly
             c.control
             st0.CS.cs_model.CS.model_control
             st0.CS.cs_model.CS.model_failure **
           record_layer_exactly
             c.records
             ({ st0.CS.cs_model.CS.model_record with
                 CS.record_write =
                   R.next_seq st0.CS.cs_model.CS.model_record.CS.record_write }) **
           handshake_exactly c.handshake st0.CS.cs_model.CS.model_handshake **
           application_exactly c.application st0.CS.cs_model.CS.model_application **
           ArrPts.pts_to network_out 'network_out_bytes **
           pure (CS.connection_state_consistent st0 /\
                 can_send_close_notify
                   st0
                   (Ghost.reveal raw_sent) /\
                 SZ.v written == 24 /\
                 SZ.v written <= B.length 'network_out_bytes /\
                 Seq.equal
                   (Ghost.reveal raw_sent)
                   (Seq.slice (Ghost.reveal 'network_out_bytes) 0 (SZ.v written)))
  ensures connection_exactly
            c
            (sent_close_notify_state
              st0
              (Ghost.reveal raw_sent)) **
          ArrPts.pts_to network_out 'network_out_bytes

fn try_send_application_data
  (c:connection_state)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to payload 'payload_bytes **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_application_data_state
                  st0
                  (Ghost.reveal 'payload_bytes)
                  raw_sent) **
              ArrPts.pts_to payload 'payload_bytes **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    SZ.v payload_len + 22 <= B.length network_out_bytes /\
                    can_send_application_data
                      st0
                      (Ghost.reveal 'payload_bytes)
                      raw_sent /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22)))
          else
            connection_exactly c st0 **
            ArrPts.pts_to payload 'payload_bytes **
            ArrPts.pts_to network_out 'old_network_out)

fn try_send_close_notify
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_close_notify_state
                  st0
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    24 <= B.length network_out_bytes /\
                    can_send_close_notify
                      st0
                      raw_sent /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 24))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)

fn try_send_key_update
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns ok: bool
  ensures (if ok then
            exists* raw_sent network_out_bytes.
              connection_exactly
                c
                (sent_key_update_response_state
                  st0
                  raw_sent) **
              ArrPts.pts_to network_out network_out_bytes **
              pure (B.length network_out_bytes == SZ.v network_out_len /\
                    27 <= B.length network_out_bytes /\
                    can_send_key_update
                      st0
                      raw_sent /\
                    Seq.equal
                      raw_sent
                      (Seq.slice network_out_bytes 0 27))
          else
            connection_exactly c st0 **
            ArrPts.pts_to network_out 'old_network_out)

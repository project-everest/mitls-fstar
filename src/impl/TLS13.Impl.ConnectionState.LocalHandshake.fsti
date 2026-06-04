module TLS13.Impl.ConnectionState.LocalHandshake

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

fn try_start_handshake
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* start.
               connection_exactly c (started_handshake_state st0 start) **
               pure (can_start_handshake st0 start /\
                     CS.legal_connection_delta
                       st0
                       {
                         CS.delta_event =
                           CS.ConnLocalEvent (CS.LocalStartHandshake start);
                         CS.delta_raw_sent = B.empty;
                         CS.delta_raw_received = B.empty;
                       }
                       (started_handshake_state st0 start))
           else
             connection_exactly c st0)

fn try_send_client_hello
  (c:connection_state)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0 **
           ArrPts.pts_to network_out 'old_network_out **
           pure (B.length 'old_network_out == SZ.v network_out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures (match written with
           | Some n ->
             exists* ch raw_sent network_out_bytes.
               connection_exactly c (sent_client_hello_state st0 ch raw_sent) **
               ArrPts.pts_to network_out network_out_bytes **
               pure (B.length network_out_bytes == SZ.v network_out_len /\
                     5 <= SZ.v n /\
                     SZ.v n <= B.length network_out_bytes /\
                     can_send_client_hello st0 ch raw_sent /\
                     Seq.equal raw_sent (Seq.slice network_out_bytes 0 (SZ.v n)))
           | None ->
             connection_exactly c st0 **
             ArrPts.pts_to network_out 'old_network_out)

fn try_derive_shared_secret
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* shared.
               connection_exactly c (derived_shared_secret_state st0 shared) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (derived_shared_secret_state st0 shared))
           else
             connection_exactly c st0)

fn try_install_client_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)

fn try_install_server_handshake_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficHandshake;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficHandshake;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)

fn try_install_client_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficWrite;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)

fn try_install_server_application_traffic_keys
  (c:connection_state)
  (#st0:erased CS.connection_state)
  requires connection_exactly c st0
  returns ok: bool
  ensures (if ok then
             exists* material.
               connection_exactly c
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }) **
               pure (CS.legal_connection_delta
                 st0
                 {
                   CS.delta_event =
                     CS.ConnLocalEvent
                       (CS.LocalInstallTrafficKeys {
                         CS.install_epoch = CS.TrafficApplication;
                         CS.install_direction = CS.TrafficRead;
                         CS.install_material = material;
                       });
                   CS.delta_raw_sent = B.empty;
                   CS.delta_raw_received = B.empty;
                 }
                 (installed_traffic_keys_state st0 {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = material;
                 }))
           else
             connection_exactly c st0)

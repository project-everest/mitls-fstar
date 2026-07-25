module TLS13.Impl.Client.Driver.Cleanup

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module C = TLS13.Impl.Client
module DS = TLS13.Impl.Client.Driver.State
module IO = Common.TCP
module MR = Pulse.Lib.MonotonicGhostRef
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT

inline_for_extraction
fn free_client_driver_buffers
  (d:DS.client_driver)
  requires DS.client_driver_buffers d
  ensures emp

inline_for_extraction
fn free_disconnected_client_driver
  (d:DS.client_driver)
  requires C.connection_exactly d.DS.client_driver_client 'st0 **
           DS.client_driver_canonical_progress d 'st0 **
           O.is_auth_context d.DS.client_driver_auth **
           Box.pts_to d.DS.client_driver_channel DS.no_channel **
           (exists* h. MR.pts_to d.DS.client_driver_tcp_history #1.0R h) **
           DS.client_driver_buffers d **
           (exists* model.
             BT.is_storage d.DS.client_driver_storage model)
  ensures DS.client_driver_closed d 'st0

inline_for_extraction
fn close_failed_connect
  (d:DS.client_driver)
  (channel:BT.t)
  requires DS.top_buffered_driver_exactly
             (DS.client_top_buffered_driver d channel)
             'st0
             'buffered
             'buffered_len **
           Box.pts_to d.DS.client_driver_channel DS.no_channel **
           DS.client_driver_buffers d
  ensures DS.client_driver_closed d 'st0

inline_for_extraction
fn close_connected_client_driver
  (d:DS.client_driver)
  requires DS.client_driver_connected d 'st0 'received 'sent
  ensures DS.client_driver_closed d 'st0

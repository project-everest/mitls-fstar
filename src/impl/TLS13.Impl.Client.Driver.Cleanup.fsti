module TLS13.Impl.Client.Driver.Cleanup

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Impl.Client
module DS = TLS13.Impl.Client.Driver.State
module IO = Common.TCP
module O = TLS13.OpenSSL
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT

inline_for_extraction
fn free_client_driver_buffers
  (d:DS.client_driver)
  (buffered_len:SZ.t)
  requires (exists* buffered. DS.client_driver_buffers d buffered buffered_len)
  ensures emp

inline_for_extraction
fn free_disconnected_client_driver
  (d:DS.client_driver)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.DS.client_driver_client 'st0 **
           DS.client_driver_canonical_seed d **
           O.is_auth_context d.DS.client_driver_auth **
           Box.pts_to d.DS.client_driver_channel DS.no_channel **
           (exists* buffered.
             DS.client_driver_buffers d buffered buffered_len)
  ensures DS.client_driver_closed d 'st0

inline_for_extraction
fn close_failed_connect
  (d:DS.client_driver)
  (ch:IO.channel)
  (buffered_len:SZ.t)
  requires C.connection_exactly d.DS.client_driver_client 'st0 **
           DS.client_driver_canonical_seed d **
           O.is_auth_context d.DS.client_driver_auth **
           DS.channel_open ch 'st0 'buffered buffered_len **
           Box.pts_to d.DS.client_driver_channel DS.no_channel **
           DS.client_driver_buffers d (Ghost.reveal 'buffered) buffered_len
  ensures DS.client_driver_closed d 'st0

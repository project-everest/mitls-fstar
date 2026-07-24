module TLS13.Impl.Server.Driver.BufferedClose

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module DS = TLS13.Impl.Server.Driver.State
module SZ = FStar.SizeT

type close_status =
  | BufferedCloseClosed
  | BufferedCloseExhausted
  | BufferedCloseFailed

fn run
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns status:close_status
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed
        d st certificate_chain credential_identity

fn abort_terminal
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_terminal
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed
        d st certificate_chain credential_identity

fn abort_connected
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d
      'st
      'certificate_chain
      'credential_identity
      'received
      'sent
  ensures
    DS.top_server_driver_closed
      d 'st 'certificate_chain 'credential_identity

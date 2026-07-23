module TLS13.Impl.Server.Driver.BufferedChannel

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel

ghost fn pack_connected_channel_invariant
  (d:DS.top_server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* pending.
      DS.top_server_channel_inv
        d
        (Ghost.reveal received)
        (Ghost.reveal sent)
        pending
        (TChannel.application_log (Ghost.reveal st))

ghost fn pack_connected_channel
  (d:DS.top_server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  requires
    DS.top_server_driver_connected
      d
      (Ghost.reveal st)
      (Ghost.reveal certificate_chain)
      (Ghost.reveal credential_identity)
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    pure (ST.server_connection_control_not_failed (Ghost.reveal st))
  ensures
    exists* wire_received wire_sent pending app_log.
      DS.top_server_channel_inv
        d wire_received wire_sent pending app_log

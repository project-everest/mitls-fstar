module TLS13.Impl.Server.Driver.BufferedChannel

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module IO = Common.TCP
module ST = TLS13.Impl.Server.Types
module TChannel = TLS13.Impl.Channel
module CI = Common.ChannelImplementation

ghost fn open_channel_invariant
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent) **
      pure (
        ST.server_connection_control_not_failed st /\
        (Ghost.reveal app_log) == TChannel.application_log st)

ghost fn open_io_channel
  (d:DS.top_server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns ch:IO.channel
  ensures
    IO.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.top_server_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)

ghost fn close_io_channel
  (d:DS.top_server_driver)
  (ch:IO.channel)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires
    IO.is_channel
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent) **
    DS.top_server_channel_io_frame
      d
      ch
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  ensures
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)

ghost fn open_terminal_invariant
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
      DS.top_server_driver_connected
        d
        st
        certificate_chain
        credential_identity
        (Ghost.reveal wire_received)
        (Ghost.reveal wire_sent)

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

ghost fn pack_connected_channel_terminal
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
      (Ghost.reveal sent)
  ensures
    DS.top_server_channel_terminal
      d
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (TChannel.application_log (Ghost.reveal st))

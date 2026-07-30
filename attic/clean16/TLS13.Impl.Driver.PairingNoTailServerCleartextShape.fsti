module TLS13.Impl.Driver.PairingNoTailServerCleartextShape

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module SD = TLS13.Impl.Server.Driver

val lemma_server_no_tail_third_event_select_parameters_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists ch e2 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            e2 ::
            rest /\
          ~ (exists m.
              e2 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch selection rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest)

val lemma_server_no_tail_fourth_event_derive_shared_secret_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists ch selection e3 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            e3 ::
            rest /\
          ~ (exists m.
              e3 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch selection server_shared rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            rest)

val lemma_server_no_tail_fifth_event_server_hello_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists ch selection server_shared e4 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            e4 ::
            rest /\
          ~ (exists m.
              e4 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch selection server_shared sh rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            rest)

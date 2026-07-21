module TLS13.Impl.Driver.PairingNoTailClientProtectedShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape

noextract
let client_after_certificate_model
  (model:CS.connection_model)
  : prop =
  model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived /\
  Some? model.CS.model_handshake.CS.hs_certificate /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
  Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
  model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None

(**
  First protected-flight milestone for the no-tail client trace.

  The fifth/sixth events after the cleartext prefix are the two commuting
  handshake-traffic installs (one client-write, one server-read).  Once both are
  installed, the length-16 no-tail/application-ready hypothesis leaves exactly
  enough room for the protected server flight and client Finished path.  This
  lemma proves the next network event must be the received EncryptedExtensions
  record.
**)
noextract
let client_no_tail_first_protected_receive_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee rest.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

val lemma_client_no_tail_seventh_event_encrypted_extensions_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_first_protected_receive_shape client)

noextract
let client_no_tail_second_protected_receive_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert rest.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

val lemma_client_no_tail_eighth_event_certificate_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_second_protected_receive_shape client)

noextract
let client_no_tail_certificate_validated_shape
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer rest.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      rest /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5

val lemma_client_no_tail_model8_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 e5 ee cert rest4 model8 tail_sent tail_received.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            e5 ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            }) ::
            rest4 /\
          FStar.List.Tot.length rest4 == 8 /\
          PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
          client_after_certificate_model model8 /\
          CS.conn_events_raw_replay
            model8
            rest4
            tail_sent
            tail_received
            client.CS.cs_model /\
          TLS13.Impl.Driver.PairingNoTailInversion.client_application_progress_rank
            client.CS.cs_model == 0)

val lemma_client_no_tail_ninth_event_validate_certificate_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures client_no_tail_certificate_validated_shape client)

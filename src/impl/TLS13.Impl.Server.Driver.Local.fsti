module TLS13.Impl.Server.Driver.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server_driver_local_status =
  | ServerDriverLocalProcessed
  | ServerDriverLocalStepFailed
  | ServerDriverLocalNotReady
  | ServerDriverLocalUnsupported

type server_driver_local_drain_result = {
  server_driver_local_drain_last: server_driver_local_status;
  server_driver_local_drain_exhausted: bool;
}

fn start_server_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent **
           pure (CM.can_start_server 'st0)
  returns resp:ST.server_response
  ensures DS.server_driver_connected
            d
            (CM.started_server_state 'st0)
            'certificate_chain
            'credential_identity
            'received
            'sent **
           pure ((CM.started_server_state 'st0).CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)

noextract
let server_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists network_out_bytes app_out_bytes.
    ST.server_local_event_end_to_end_correct
      st0
      st1
      resp
      kind
      payload
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append sent (ST.response_network_out resp network_out_bytes))

val lemma_server_driver_local_write_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  : Lemma
      (requires
        ST.server_local_event_end_to_end_correct
          st0
          st1
          resp
          kind
          payload
          network_out_bytes
          app_out_bytes /\
        Seq.equal
          sent'
          (B.append sent (ST.response_network_out resp network_out_bytes)))
      (ensures server_driver_local_write_correct
        st0 st1 resp kind payload sent sent')

val lemma_server_driver_local_write_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires server_driver_local_write_correct st0 st1 resp kind payload sent sent')
      (ensures
          st1.CS.cs_model.CS.model_config ==
            st0.CS.cs_model.CS.model_config)

val lemma_server_driver_local_write_correct_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        server_driver_local_write_correct st0 st1 resp kind payload sent sent' /\
        kind <> ST.LocalSelectServerParameters /\
        kind <> ST.LocalStartServer /\
        kind <> ST.LocalSendServerHello /\
        ST.server_local_event_input_ready_with_credentials
          st0 kind payload certificate_chain credential_identity /\
        DS.server_driver_config_matches_credentials
          st0 certificate_chain credential_identity /\
        DS.server_driver_supported_profile_selection st0 credential_identity)
      (ensures
        DS.server_driver_supported_profile_selection st1 credential_identity)

fn process_local_event_and_write_once
  (d:DS.server_driver)
  (kind:ST.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 kind <> ST.LocalSelectServerParameters /\
                 kind <> ST.LocalStartServer /\
                 kind <> ST.LocalSendServerHello /\
                 ST.server_local_event_input_ready_with_credentials
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes)
                   (Ghost.reveal 'certificate_chain)
                   (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            kind
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)

fn process_empty_local_event_and_write_once
  (d:DS.server_driver)
  (kind:ST.local_event_kind)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             kind
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity) /\
             kind <> ST.LocalSelectServerParameters /\
             kind <> ST.LocalStartServer /\
             kind <> ST.LocalSendServerHello)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            kind
            B.empty
            (Ghost.reveal 'sent)
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config)

fn process_ready_empty_local_action_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent
  returns status:server_driver_local_status
  ensures (match status with
           | ServerDriverLocalProcessed
           | ServerDriverLocalStepFailed ->
             exists* st1 sent'.
               DS.server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 'received
                 sent' **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | _ ->
             DS.server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               'received
               'sent)

fn drain_ready_empty_local_actions
  (d:DS.server_driver)
  (fuel:SZ.t)
  requires DS.server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns result:server_driver_local_drain_result
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config)

fn send_application_data_once
  (d:DS.server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            ST.LocalSendApplicationData
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent')

fn send_close_notify_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready
             'st0
             ST.LocalSendCloseNotify
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pure (server_driver_local_write_correct
            'st0
            st1
            resp
            ST.LocalSendCloseNotify
            B.empty
            (Ghost.reveal 'sent)
            sent')

fn send_certificate_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSendCertificate
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn sign_certificate_verify_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready_with_credentials
             'st0
             ST.LocalSignCertificateVerify
             B.empty
             (Ghost.reveal 'certificate_chain)
             (Ghost.reveal 'credential_identity))
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

fn verify_client_finished_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (ST.server_local_event_input_ready
             'st0
             ST.LocalVerifyClientFinished
             B.empty)
  returns resp:ST.server_response
  ensures exists* st1 sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'

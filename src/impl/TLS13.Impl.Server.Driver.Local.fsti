module TLS13.Impl.Server.Driver.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

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
            'sent

noextract
val server_driver_local_write_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_response)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop

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
            sent')

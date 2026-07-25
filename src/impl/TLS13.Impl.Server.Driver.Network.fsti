module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CR = TLS13.Impl.ConnectionState.Repr
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

type server_driver_network_loop_result = {
  server_driver_network_loop_last: ST.server_buffer_response;
  server_driver_network_loop_exhausted: bool;
}

type server_driver_client_hello_wait_result = {
  server_driver_client_hello_wait_last: ST.server_buffer_response;
  server_driver_client_hello_wait_ready: bool;
  server_driver_client_hello_wait_exhausted: bool;
}

noextract
let server_driver_network_process_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists input network_out_bytes app_out_bytes.
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      resp
      input
      network_out_bytes
      app_out_bytes /\
    ST.server_network_consumed_input_projection
      st0
      st1
      resp
      input
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append
        sent
        (ST.response_network_out resp.ST.response network_out_bytes))

noextract
let server_driver_network_process_correct_for_app_out
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  (app_out_bytes:B.bytes)
  : prop =
  exists input network_out_bytes.
    ST.server_network_bytes_end_to_end_correct
      st0
      st1
      resp
      input
      network_out_bytes
      app_out_bytes /\
    ST.server_network_consumed_input_projection
      st0
      st1
      resp
      input
      network_out_bytes
      app_out_bytes /\
    Seq.equal
      sent'
      (B.append
        sent
        (ST.response_network_out resp.ST.response network_out_bytes))

fn process_buffered_network_bytes_compact_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 sent' app_out_bytes.
          DS.server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent'
            app_out_bytes **
          pure (server_driver_network_process_correct
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent' /\
            server_driver_network_process_correct_for_app_out
             'st0
             st1
             resp
             (Ghost.reveal 'sent)
             sent'
             app_out_bytes)

fn process_buffered_or_read_network_once
  (d:DS.server_driver)
  requires DS.server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns resp:ST.server_buffer_response
  ensures exists* st1 received' sent' app_out_bytes.
          DS.server_driver_connected_with_app_out
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out_bytes **
          pure (server_driver_network_process_correct
           'st0
           st1
           resp
           (Ghost.reveal 'sent)
           sent' /\
           server_driver_network_process_correct_for_app_out
            'st0
            st1
            resp
            (Ghost.reveal 'sent)
            sent'
            app_out_bytes)

fn server_driver_control_snapshot
  (d:DS.server_driver)
  requires DS.server_driver_connected
           d
           'st0
           'certificate_chain
           'credential_identity
           'received
           'sent
  returns snapshot:CR.control_snapshot
  ensures DS.server_driver_connected
           d
           'st0
           'certificate_chain
           'credential_identity
           'received
           'sent **
          pure (CR.control_snapshot_matches snapshot 'st0)

fn read_process_network_until_ready_into
  (d:DS.server_driver)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  (fuel:SZ.t)
  requires DS.server_driver_connected_with_output
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
             app_out
             app_out_len
             'old_app_out
  returns result:server_driver_network_loop_result
  ensures exists* st1 received' sent' app_out_bytes.
          DS.server_driver_connected_with_output
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out
           app_out_len
           app_out_bytes **
          pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config /\
            (result.server_driver_network_loop_exhausted == true ==>
              st1 == 'st0 /\
              Seq.equal sent' (Ghost.reveal 'sent)) /\
            (result.server_driver_network_loop_exhausted == false ==>
            result.server_driver_network_loop_last.ST.response.ST.status <>
              ST.NeedMoreInput /\
            server_driver_network_process_correct
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent' /\
            server_driver_network_process_correct_for_app_out
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent'
              app_out_bytes))

fn read_process_network_until_ready
  (d:DS.server_driver)
  (fuel:SZ.t)
  requires DS.server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_network_loop_result
  ensures exists* st1 received' sent' app_out_bytes.
          DS.server_driver_connected_with_app_out
           d
           st1
           'certificate_chain
           'credential_identity
           received'
           sent'
           app_out_bytes **
          pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config /\
            (result.server_driver_network_loop_exhausted == true ==>
              st1 == 'st0 /\
              Seq.equal sent' (Ghost.reveal 'sent)) /\
            (result.server_driver_network_loop_exhausted == false ==>
            result.server_driver_network_loop_last.ST.response.ST.status <>
              ST.NeedMoreInput /\
            server_driver_network_process_correct
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent' /\
            server_driver_network_process_correct_for_app_out
              'st0
              st1
              result.server_driver_network_loop_last
              (Ghost.reveal 'sent)
              sent'
              app_out_bytes))

fn read_until_client_hello_received
  (d:DS.server_driver)
  (fuel:SZ.t)
  requires DS.server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            'received
            'sent
  returns result:server_driver_client_hello_wait_result
  ensures exists* st1 received' sent'.
          DS.server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config /\
           (result.server_driver_client_hello_wait_ready == true ==>
            st1.CS.cs_model.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config))

val lemma_server_driver_network_process_correct_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes)))
      (ensures server_driver_network_process_correct
        st0 st1 resp sent sent')

val lemma_server_driver_network_process_correct_for_app_out_intro
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out_bytes:B.bytes)
  (app_out_bytes:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 resp input network_out_bytes app_out_bytes /\
        ST.server_network_consumed_input_projection
          st0 st1 resp input network_out_bytes app_out_bytes /\
        Seq.equal
          sent'
          (B.append
            sent
            (ST.response_network_out resp.ST.response network_out_bytes)))
      (ensures server_driver_network_process_correct_for_app_out
        st0 st1 resp sent sent' app_out_bytes)

val lemma_server_driver_network_process_need_more_stutter
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires
        server_driver_network_process_correct st0 st1 resp sent sent' /\
        resp.ST.response.ST.status == ST.NeedMoreInput)
      (ensures
        st1 == st0 /\
        Seq.equal sent' sent)

val lemma_server_driver_network_process_correct_preserves_config
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  : Lemma
      (requires server_driver_network_process_correct st0 st1 resp sent sent')
      (ensures
        st1.CS.cs_model.CS.model_config ==
          st0.CS.cs_model.CS.model_config)

val lemma_server_driver_network_process_correct_preserves_supported_profile_selection
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:ST.server_buffer_response)
  (sent:B.bytes)
  (sent':B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        server_driver_network_process_correct st0 st1 resp sent sent' /\
        DS.server_driver_supported_profile_selection st0 credential_identity)
      (ensures
        DS.server_driver_supported_profile_selection st1 credential_identity)

val lemma_slice_append_full
  (s:B.bytes)
  (n:nat)
  : Lemma
      (requires n <= B.length s)
      (ensures Seq.equal
        (B.append (Seq.slice s 0 n) (Seq.slice s n (B.length s)))
        s)

val lemma_server_network_wire_accounting
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (old_consumed:B.bytes)
  : Lemma
      (requires
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out /\
        TLS13.Impl.Server.Driver.State.logged_received_bytes_accounted
          st0.CS.cs_wire_log.CL.raw_received
          old_consumed)
      (ensures
        SZ.v buffer_resp.ST.response.ST.network_out_len <= B.length network_out /\
        Seq.equal
          st1.CS.cs_wire_log.CL.raw_sent
          (B.append
            st0.CS.cs_wire_log.CL.raw_sent
            (ST.response_network_out buffer_resp.ST.response network_out)) /\
        TLS13.Impl.Server.Driver.State.logged_received_bytes_accounted
          st1.CS.cs_wire_log.CL.raw_received
          (B.append old_consumed
            (ST.server_network_consumed_prefix buffer_resp input)))

val lemma_server_network_logged_received_exact_when_nonfailed
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (buffer_resp:ST.server_buffer_response)
  (input:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  (received:B.bytes)
  (sent:B.bytes)
  (old_consumed:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        DS.server_driver_wire_logs_match_witness
          st0
          received
          sent
          old_consumed
          buffered
          buffered_len /\
        ST.server_network_bytes_end_to_end_correct
          st0 st1 buffer_resp input network_out app_out /\
        ST.server_network_consumed_input_projection
          st0 st1 buffer_resp input network_out app_out)
      (ensures
        ST.server_connection_control_not_failed st1 ==>
          Seq.equal
            st1.CS.cs_wire_log.CL.raw_received
            (B.append old_consumed
              (ST.server_network_consumed_prefix buffer_resp input)))

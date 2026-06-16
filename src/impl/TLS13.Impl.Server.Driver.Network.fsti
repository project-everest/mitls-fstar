module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
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

val pending_after_consumed (buffered_len consumed_len:SZ.t)
  : r:SZ.t {
      (SZ.v consumed_len <= SZ.v buffered_len ==>
        SZ.v r == SZ.v buffered_len - SZ.v consumed_len) /\
      (SZ.v consumed_len <= SZ.v buffered_len ==>
        SZ.v r + SZ.v consumed_len == SZ.v buffered_len)
    }

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))

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

fn read_and_process_network_once
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

val lemma_read_append_buffer_matches_raw_prefix_index
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  (k:nat { k < total_len })
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.index (B.append buffered read_chunk) k ==
      Seq.index (Seq.slice raw_after_read 0 total_len) k)

val lemma_read_append_buffer_matches_raw_prefix
  (raw_after_read raw raw_tail_after buffered read_chunk:B.bytes)
  (current_len read_len total_len:nat)
  : Lemma
    (requires
      B.length buffered == current_len /\
      B.length read_chunk == read_len /\
      B.length raw >= current_len /\
      B.length raw_tail_after >= read_len /\
      B.length raw_after_read >= total_len /\
      total_len == current_len + read_len /\
      Seq.equal buffered (Seq.slice raw 0 current_len) /\
      Seq.equal read_chunk (Seq.slice raw_tail_after 0 read_len) /\
      (forall (i:nat). i < current_len ==>
        Seq.index raw_after_read i == Seq.index raw i) /\
      (forall (i:nat). i < read_len ==>
        Seq.index raw_after_read (current_len + i) ==
        Seq.index raw_tail_after i))
    (ensures
      Seq.equal (B.append buffered read_chunk)
        (Seq.slice raw_after_read 0 total_len))

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

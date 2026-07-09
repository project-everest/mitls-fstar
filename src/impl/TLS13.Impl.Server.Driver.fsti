module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module DL = TLS13.Impl.Server.Driver.Local
module DN = TLS13.Impl.Server.Driver.Network
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module SP = TLS13.Impl.Server.CanonicalProtocol

val server_driver : Type0

noextract
val server_driver_canonical
  (d: server_driver)
  : SP.canonical_server

noextract
val server_driver_canonical_progress
  (d: server_driver)
  (st: CS.connection_state)
  : slprop

noextract
val server_driver_wire_logs_match
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : prop

noextract
val server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
(**
  Owns a connected server driver together with the concrete TCP byte histories
  tracked by Common.TCP. The protocol-level processed wire log is in
  st.cs_wire_log; received may also include bytes retained in the driver's input
  buffer. The predicate includes server_driver_wire_logs_match for that hidden
  retained-byte accounting.
**)
val server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop

noextract
val server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

type server_workflow_status =
  | ServerWorkflowOk
  | ServerWorkflowNeedMoreInput
  | ServerWorkflowStepFailed
  | ServerWorkflowExhausted
  | ServerWorkflowClosed

type server_receive_result = {
  server_receive_status: server_workflow_status;
  server_receive_len: SZ.t;
}

noextract
let server_driver_send_status_correct
  (status:server_workflow_status)
  (resp:ST.server_response)
  : prop =
  if resp.ST.status == ST.StepOk
  then status == ServerWorkflowOk
  else status == ServerWorkflowStepFailed

noextract
let server_driver_send_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (status:server_workflow_status)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  exists resp.
    DL.server_driver_local_write_correct
      st0
      st1
      resp
      ST.LocalSendApplicationData
      payload
      sent
      sent' /\
    server_driver_send_status_correct status resp

noextract
let server_driver_receive_status_correct
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if loop.DN.server_driver_network_loop_exhausted then
    result.server_receive_status == ServerWorkflowExhausted /\
    result.server_receive_len == 0sz
  else
    match loop.DN.server_driver_network_loop_last.ST.response.ST.status with
    | ST.StepOk ->
      if SZ.v loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length out_bytes /\
         SZ.v loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length app_out
      then
        result.server_receive_status == ServerWorkflowOk /\
        result.server_receive_len ==
          loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
      else
        result.server_receive_status == ServerWorkflowStepFailed /\
        result.server_receive_len == 0sz
    | ST.NeedMoreInput ->
      result.server_receive_status == ServerWorkflowNeedMoreInput /\
      result.server_receive_len == 0sz
    | _ ->
      result.server_receive_status == ServerWorkflowStepFailed /\
      result.server_receive_len == 0sz

noextract
let server_driver_receive_copyout_correct
  (result:server_receive_result)
  (resp:ST.server_response)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if result.server_receive_status == ServerWorkflowOk then
    SZ.v result.server_receive_len <= B.length out_bytes /\
    result.server_receive_len == resp.ST.app_out_len /\
    (if SZ.v result.server_receive_len <= B.length out_bytes then
      Seq.equal
        (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
        (ST.response_app_out resp app_out)
     else False)
  else
    True

noextract
let server_driver_receive_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent:B.bytes)
  (sent':B.bytes)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  server_driver_receive_status_correct result loop app_out out_bytes /\
  SZ.v result.server_receive_len <= B.length out_bytes /\
  (loop.DN.server_driver_network_loop_exhausted == false ==>
    DN.server_driver_network_process_correct
      st0
      st1
      loop.DN.server_driver_network_loop_last
      sent
      sent' /\
    DN.server_driver_network_process_correct_for_app_out
      st0
      st1
      loop.DN.server_driver_network_loop_last
      sent
      sent'
      app_out) /\
  (result.server_receive_status == ServerWorkflowOk ==>
    server_driver_receive_copyout_correct
      result
      loop.DN.server_driver_network_loop_last.ST.response
      app_out
      out_bytes)

noextract
let server_driver_application_ready
  (st:CS.connection_state)
  : prop =
  ST.server_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model /\
  CS.stable_server_x25519_key_share_projection st

noextract
let server_driver_sent_log_exact
  (st:CS.connection_state)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

noextract
let server_driver_received_log_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
  (forall b.
    SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b received)

noextract
let server_driver_received_log_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  exists retained.
    Seq.equal received
      (B.append st.CS.cs_wire_log.CL.raw_received retained)

noextract
let server_driver_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

val lemma_server_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures server_driver_received_log_exact_prefix st received)

val lemma_server_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures server_driver_received_no_read_ahead st received)

noextract
let server_driver_close_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (sent:B.bytes)
  : prop =
  exists sent' resp.
    DL.server_driver_local_write_correct
      st0
      st1
      resp
      ST.LocalSendCloseNotify
      B.empty
      sent
      sent'

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               server_driver_canonical_progress
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity) **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity))
           | None ->
             emp)

fn accept
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.RsaPssRsaeSha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed d st1 'certificate_chain 'credential_identity **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | ServerWorkflowOk ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (server_driver_application_ready st1 /\
                     st1.CS.cs_model.CS.model_config ==
                       'st0.CS.cs_model.CS.model_config /\
                     server_driver_sent_log_exact st1 sent /\
                     server_driver_received_log_accounted st1 received /\
                     server_driver_received_log_exact_prefix st1 received /\
                     server_driver_received_no_read_ahead st1 received)
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config))

fn send
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
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
  returns status:server_workflow_status
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_send_correct
            'st0
            st1
            status
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config /\
            server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
            server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
            server_driver_sent_log_exact st1 sent' /\
            server_driver_received_log_accounted st1 (Ghost.reveal 'received))

fn receive
  (d:server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to out 'out_bytes **
           pure (B.length 'out_bytes == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* st1 received' sent' out_bytes.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.server_receive_len <= SZ.v out_len /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                server_driver_sent_log_exact st1 sent' /\
                server_driver_received_log_accounted st1 received' /\
                (exists loop app_out.
                  server_driver_receive_correct
                    'st0
                    st1
                    result
                    loop
                    (Ghost.reveal 'sent)
                    sent'
                    app_out
                    out_bytes))

fn close
  (d:server_driver)
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
            pure (server_driver_application_ready 'st0)
  returns status:server_workflow_status
  ensures exists* st1.
            server_driver_closed d st1 'certificate_chain 'credential_identity **
            pure (status == ServerWorkflowClosed /\
                 st1.CS.cs_model.CS.model_config ==
                   'st0.CS.cs_model.CS.model_config /\
                 server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                 server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                 server_driver_close_correct
                   'st0
                   st1
                   (Ghost.reveal 'sent))

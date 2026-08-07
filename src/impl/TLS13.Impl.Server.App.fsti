module TLS13.Impl.Server.App

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module M = TLS13.Messages
module SM = TLS13.Spec.StateMachine.ClientTrace
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8

type server = CR.connection_state

let connection_exactly (s:server) (st:CS.connection_state) : slprop =
  CR.connection_exactly s st

noextract
let server_app_local_event_input_ready
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  : prop =
  match kind with
  | ST.LocalSendApplicationData ->
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
    B.length payload <= SM.max_application_data_fragment_len
  | ST.LocalSendCloseNotify ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic
  | ST.LocalSendKeyUpdate
  | ST.LocalSendKeyUpdateRequested ->
    Seq.equal payload B.empty /\
    st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
    st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    Some?
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic
  | _ ->
    False

let lemma_server_app_key_update_ready
  (st:CS.connection_state)
  (kind:ST.local_event_kind)
  (payload:B.bytes)
  : Lemma
      (requires
        (kind == ST.LocalSendKeyUpdate \/ kind == ST.LocalSendKeyUpdateRequested) /\
        server_app_local_event_input_ready st kind payload)
      (ensures
        Seq.equal payload B.empty /\
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some?
          st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic)
=
  ()

fn process_send_application_data_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_app_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_application_data_state
                        'st0
                        (Ghost.reveal 'payload_bytes)
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendApplicationData
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_send_close_notify_local_event
  (s:server)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 server_app_local_event_input_ready
                   'st0
                   ST.LocalSendCloseNotify
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.sent_close_notify_state
                        'st0
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  ST.LocalSendCloseNotify
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

fn process_send_key_update_local_event
  (s:server)
  (kind:ST.local_event_kind)
  (req:M.key_update_request)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires connection_exactly s 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len /\
                 ST.server_end_to_end_invariant 'st0 /\
                 ((kind == ST.LocalSendKeyUpdate /\ req == M.UpdateNotRequested) \/
                  (kind == ST.LocalSendKeyUpdateRequested /\ req == M.UpdateRequested)) /\
                 server_app_local_event_input_ready
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp:ST.server_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          connection_exactly s st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                (resp.status == ST.StepOk ==>
                  exists raw_sent.
                    st1 ==
                      CM.server_sent_key_update_state
                        'st0
                        req
                        raw_sent /\
                    Seq.equal
                      raw_sent
                      (ST.response_network_out resp network_out_bytes)) /\
                ST.server_local_event_end_to_end_correct
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)

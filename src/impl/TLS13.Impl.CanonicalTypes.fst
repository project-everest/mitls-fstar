module TLS13.Impl.CanonicalTypes

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CPI = Common.ProtocolImplementation
module CT = TLS13.Impl.Client.Types
module EC = TLS13.Spec.Endpoint.Client
module ET = TLS13.Impl.Endpoint.Types
module ES = TLS13.Spec.Endpoint.Server
module ST = TLS13.Impl.Server.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT

(**
  Role-specific, extraction-facing vocabulary for the canonical
  Common.ProtocolImplementation adapters.

  This module contains only implementation-specific vocabulary: client/server
  wrappers over the C-ABI [local_event_kind] enums, exhaustive projections of
  those wrappers into the core semantic endpoint-event vocabularies, and
  conversions from extraction-facing endpoint responses into
  [CPI.process_result].  Core definitions are imported explicitly; this module
  does not re-export them.
 **)

type client_api_event = {
  client_local_kind: CT.local_event_kind;
  client_local_payload: B.bytes;
}

noeq
type client_local_event =
  | ClientAPI: event:client_api_event -> client_local_event
  | ClientValidateCertificate: payload:Ghost.erased B.bytes -> client_local_event

let client_local_event_kind
  (ev:client_local_event)
  : CT.local_event_kind =
  match ev with
  | ClientAPI api -> api.client_local_kind
  | ClientValidateCertificate _ -> CT.LocalValidateCertificate

let client_local_event_api
  (ev:client_local_event)
  : GTot client_api_event =
  match ev with
  | ClientAPI api -> api
  | ClientValidateCertificate payload ->
    {
      client_local_kind = CT.LocalValidateCertificate;
      client_local_payload = Ghost.reveal payload;
    }

noextract
let client_api_event_semantic
  (api:client_api_event)
  : EC.local_event =
  match api.client_local_kind with
  | CT.LocalStartHandshake ->
      EC.ClientStartHandshake
  | CT.LocalDeriveSharedSecret ->
      EC.ClientDeriveSharedSecret
  | CT.LocalInstallClientHandshakeTrafficKeys ->
      EC.ClientInstallClientHandshakeTrafficKeys
  | CT.LocalInstallServerHandshakeTrafficKeys ->
      EC.ClientInstallServerHandshakeTrafficKeys
  | CT.LocalInstallClientApplicationTrafficKeys ->
      EC.ClientInstallClientApplicationTrafficKeys
  | CT.LocalInstallServerApplicationTrafficKeys ->
      EC.ClientInstallServerApplicationTrafficKeys
  | CT.LocalValidateCertificate ->
      EC.ClientValidateCertificate api.client_local_payload
  | CT.LocalVerifyCertificateSignature ->
      EC.ClientVerifyCertificateSignature
  | CT.LocalVerifyFinished ->
      EC.ClientVerifyFinished
  | CT.LocalDeliverApplicationData ->
      EC.ClientDeliverApplicationData api.client_local_payload
  | CT.LocalSendClientHello ->
      EC.ClientSendClientHello
  | CT.LocalSendClientFinished ->
      EC.ClientSendClientFinished
  | CT.LocalSendApplicationData ->
      EC.ClientSendApplicationData api.client_local_payload
  | CT.LocalSendKeyUpdate ->
      EC.ClientSendKeyUpdate
  | CT.LocalSendCloseNotify ->
      EC.ClientSendCloseNotify
  | CT.LocalFail ->
      EC.ClientFail
  | CT.LocalProcessPendingHandshake ->
      EC.ClientProcessPendingHandshake

noextract
let client_local_event_semantic
  (ev:client_local_event)
  : GTot EC.local_event =
  client_api_event_semantic (client_local_event_api ev)

noextract
let client_api_event_matches
  (st:TLS13.Spec.StateMachine.connection_state)
  (api:client_api_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : prop =
  EC.client_local_event_matches st (client_api_event_semantic api) ev

let lemma_client_api_event_semantic_exact
  (st:TLS13.Spec.StateMachine.connection_state)
  (api:client_api_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : Lemma
      (ensures
        (client_api_event_matches st api ev <==>
         CT.local_event_kind_matches
           st
           api.client_local_kind
           api.client_local_payload
           ev))
=
  match api.client_local_kind with
  | CT.LocalStartHandshake
  | CT.LocalDeriveSharedSecret
  | CT.LocalInstallClientHandshakeTrafficKeys
  | CT.LocalInstallServerHandshakeTrafficKeys
  | CT.LocalInstallClientApplicationTrafficKeys
  | CT.LocalInstallServerApplicationTrafficKeys
  | CT.LocalValidateCertificate
  | CT.LocalVerifyCertificateSignature
  | CT.LocalVerifyFinished
  | CT.LocalDeliverApplicationData
  | CT.LocalSendClientHello
  | CT.LocalSendClientFinished
  | CT.LocalSendApplicationData
  | CT.LocalSendKeyUpdate
  | CT.LocalSendCloseNotify
  | CT.LocalFail ->
      ()
  | CT.LocalProcessPendingHandshake ->
      ()

noextract
let client_local_event_matches
  (st:TLS13.Spec.StateMachine.connection_state)
  (input:client_local_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : prop =
  let api = client_local_event_api input in
  CT.local_event_kind_matches
    st
    api.client_local_kind
    api.client_local_payload
    ev

let lemma_client_local_event_semantic_exact
  (st:TLS13.Spec.StateMachine.connection_state)
  (input:client_local_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : Lemma
      (client_local_event_matches st input ev <==>
       EC.client_local_event_matches
         st
         (client_local_event_semantic input)
         ev)
=
  lemma_client_api_event_semantic_exact st (client_local_event_api input) ev

noextract
instance client_event_representation
  : EC.client_event_representation client_local_event =
  {
    EC.client_event_semantic = client_local_event_semantic;
    EC.client_representation_matches = client_local_event_matches;
    EC.client_representation_exact = lemma_client_local_event_semantic_exact;
  }

type server_api_event = {
  server_local_kind: ST.local_event_kind;
  server_local_payload: B.bytes;
}

noeq
type server_local_event =
  | ServerAPI: event:server_api_event -> server_local_event
  | ServerPayload:
      kind:ST.local_event_kind ->
      payload:Ghost.erased B.bytes ->
        server_local_event

let server_local_event_kind
  (ev:server_local_event)
  : ST.local_event_kind =
  match ev with
  | ServerAPI api -> api.server_local_kind
  | ServerPayload kind _ -> kind

let server_local_event_api
  (ev:server_local_event)
  : GTot server_api_event =
  match ev with
  | ServerAPI api -> api
  | ServerPayload kind payload ->
    {
      server_local_kind = kind;
      server_local_payload = Ghost.reveal payload;
    }

noextract
let server_api_event_semantic
  (api:server_api_event)
  : ES.local_event =
  match api.server_local_kind with
  | ST.LocalStartServer ->
      ES.ServerStart
  | ST.LocalSelectServerParameters ->
      ES.ServerSelectParameters
  | ST.LocalDeriveSharedSecret ->
      ES.ServerDeriveSharedSecret
  | ST.LocalInstallClientHandshakeTrafficKeys ->
      ES.ServerInstallClientHandshakeTrafficKeys
  | ST.LocalInstallServerHandshakeTrafficKeys ->
      ES.ServerInstallServerHandshakeTrafficKeys
  | ST.LocalInstallClientApplicationTrafficKeys ->
      ES.ServerInstallClientApplicationTrafficKeys
  | ST.LocalInstallServerApplicationTrafficKeys ->
      ES.ServerInstallServerApplicationTrafficKeys
  | ST.LocalSignCertificateVerify ->
      ES.ServerSignCertificateVerify
  | ST.LocalVerifyClientFinished ->
      ES.ServerVerifyClientFinished
  | ST.LocalDeliverApplicationData ->
      ES.ServerDeliverApplicationData api.server_local_payload
  | ST.LocalSendServerHello ->
      ES.ServerSendServerHello
  | ST.LocalSendEncryptedExtensions ->
      ES.ServerSendEncryptedExtensions
  | ST.LocalSendCertificate ->
      ES.ServerSendCertificate
  | ST.LocalSendCertificateVerify ->
      ES.ServerSendCertificateVerify
  | ST.LocalSendServerFinished ->
      ES.ServerSendServerFinished
  | ST.LocalSendApplicationData ->
      ES.ServerSendApplicationData api.server_local_payload
  | ST.LocalSendCloseNotify ->
      ES.ServerSendCloseNotify
  | ST.LocalFail ->
      ES.ServerFail

noextract
let server_local_event_semantic
  (ev:server_local_event)
  : GTot ES.local_event =
  server_api_event_semantic (server_local_event_api ev)

noextract
let server_api_event_matches
  (api:server_api_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : prop =
  ES.server_local_event_matches (server_api_event_semantic api) ev

let lemma_server_api_event_semantic_exact
  (api:server_api_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : Lemma
      (ensures
        (server_api_event_matches api ev <==>
         ST.local_event_kind_matches
           api.server_local_kind
           api.server_local_payload
           ev))
=
  match api.server_local_kind with
  | ST.LocalStartServer
  | ST.LocalSelectServerParameters
  | ST.LocalDeriveSharedSecret
  | ST.LocalInstallClientHandshakeTrafficKeys
  | ST.LocalInstallServerHandshakeTrafficKeys
  | ST.LocalInstallClientApplicationTrafficKeys
  | ST.LocalInstallServerApplicationTrafficKeys
  | ST.LocalSignCertificateVerify
  | ST.LocalVerifyClientFinished
  | ST.LocalDeliverApplicationData
  | ST.LocalSendServerHello
  | ST.LocalSendEncryptedExtensions
  | ST.LocalSendCertificate
  | ST.LocalSendCertificateVerify
  | ST.LocalSendServerFinished
  | ST.LocalSendApplicationData
  | ST.LocalSendCloseNotify
  | ST.LocalFail ->
      ()

noextract
let server_local_event_matches
  (input:server_local_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : prop =
  let api = server_local_event_api input in
  ST.local_event_kind_matches
    api.server_local_kind
    api.server_local_payload
    ev

let lemma_server_local_event_semantic_exact
  (input:server_local_event)
  (ev:TLS13.Spec.StateMachine.conn_event)
  : Lemma
      (server_local_event_matches input ev <==>
       ES.server_local_event_matches
         (server_local_event_semantic input)
         ev)
=
  lemma_server_api_event_semantic_exact (server_local_event_api input) ev

noextract
instance server_event_representation
  : ES.server_event_representation server_local_event =
  {
    ES.server_event_semantic = server_local_event_semantic;
    ES.server_representation_matches = server_local_event_matches;
    ES.server_representation_exact = lemma_server_local_event_semantic_exact;
  }

let endpoint_status_to_process_status
  (status:ET.endpoint_status)
  : CPI.process_status =
  match status with
  | ET.StepOk -> CPI.StepOk
  | ET.NeedMoreInput -> CPI.NeedMoreInput
  | ET.DecodeError -> CPI.DecodeError
  | ET.IllegalTransition -> CPI.IllegalTransition
  | ET.OutputBufferTooSmall -> CPI.OutputBufferTooSmall
  | ET.ConnectionFailed -> CPI.ConnectionFailed

let process_result_of_endpoint
  (consumed_len:SZ.t)
  (response:ET.endpoint_response)
  : CPI.process_result =
  {
    CPI.process_status =
      endpoint_status_to_process_status response.ET.status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = response.ET.network_out_len;
    CPI.process_app_len = response.ET.app_out_len;
  }

let client_process_result
  (response:CT.client_buffer_response)
  : CPI.process_result =
  process_result_of_endpoint response.CT.consumed_len response.CT.response

let client_local_process_result
  (response:CT.client_response)
  : CPI.process_result =
  process_result_of_endpoint 0sz response

let server_process_result
  (response:ST.server_buffer_response)
  : CPI.process_result =
  process_result_of_endpoint response.ST.consumed_len response.ST.response

let server_local_process_result
  (response:ST.server_response)
  : CPI.process_result =
  process_result_of_endpoint 0sz response

let app_out_written
  (response:ET.endpoint_response)
  (app_out:B.bytes)
  (app_bytes:B.bytes)
  : prop =
  SZ.v response.ET.app_out_len == B.length app_bytes /\
  SZ.v response.ET.app_out_len <= B.length app_out /\
  Seq.equal
    (Seq.slice app_out 0 (SZ.v response.ET.app_out_len))
    app_bytes

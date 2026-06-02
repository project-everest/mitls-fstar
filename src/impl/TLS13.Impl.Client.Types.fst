module TLS13.Impl.Client.Types

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types

(**
  Extraction-facing client step shapes.  The concrete driver supplies buffers
  and machine-sized lengths; the TLS connection delta remains a ghost proof
  artifact connecting a concrete response to the rich specification state.
**)

type client_status =
  | StepOk
  | NeedMoreInput
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed

type client_response = {
  network_out_len: SZ.t;
  app_out_len: SZ.t;
  status: client_status;
}

let tls_decode_error : T.tls_error = T.AlertError T.DecodeError

type local_event_kind =
  | LocalStartHandshake
  | LocalDeriveSharedSecret
  | LocalInstallTrafficKeys
  | LocalValidateCertificate
  | LocalVerifyCertificateSignature
  | LocalVerifyFinished
  | LocalDeliverApplicationData
  | LocalSendClientHello
  | LocalSendClientFinished
  | LocalSendApplicationData
  | LocalSendCloseNotify
  | LocalFail

let response_wf
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  SZ.v resp.network_out_len <= B.length network_out /\
  SZ.v resp.app_out_len <= B.length app_out

let response_network_out (resp:client_response) (network_out:B.bytes) : B.bytes =
  if SZ.v resp.network_out_len <= B.length network_out
  then Seq.slice network_out 0 (SZ.v resp.network_out_len)
  else B.empty

let response_app_out (resp:client_response) (app_out:B.bytes) : B.bytes =
  if SZ.v resp.app_out_len <= B.length app_out
  then Seq.slice app_out 0 (SZ.v resp.app_out_len)
  else B.empty

let legal_delta
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : prop =
  CS.legal_connection_delta
    st0
    {
      CS.delta_event = ev;
      CS.delta_raw_sent = raw_sent;
      CS.delta_raw_received = raw_received;
    }
    st1

let legal_response_for_event
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  response_wf resp network_out app_out /\
  Seq.equal raw_sent (response_network_out resp network_out) /\
  legal_delta st0 st1 ev raw_sent raw_received

let some_legal_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  exists ev raw_sent raw_received.
    legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out

let legal_received_tls_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg })
    B.empty
    raw_received
    network_out
    app_out

let local_event_kind_matches
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  : prop =
  match kind, ev with
  | LocalDeliverApplicationData, CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes) ->
    Seq.equal bytes payload
  | LocalSendApplicationData, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes -> Seq.equal bytes payload
     | _ -> False)
  | LocalSendClientHello, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.ClientHello _) -> True
     | _ -> False)
  | LocalSendClientFinished, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    (match msg.CL.message_value with
     | M.TlsHandshake (M.Finished _) -> True
     | _ -> False)
  | LocalSendCloseNotify, CS.ConnNetworkEvent msg ->
    msg.CL.message_direction == CL.Sent /\
    msg.CL.message_value == M.TlsAlert T.CloseNotify
  | LocalStartHandshake, CS.ConnLocalEvent (CS.LocalStartHandshake _) -> True
  | LocalDeriveSharedSecret, CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) -> True
  | LocalInstallTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
  | LocalValidateCertificate, CS.ConnLocalEvent (CS.LocalValidateCertificate _) -> True
  | LocalVerifyCertificateSignature, CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature _) -> True
  | LocalVerifyFinished, CS.ConnLocalEvent (CS.LocalVerifyFinished _) -> True
  | LocalFail, CS.ConnLocalEvent (CS.LocalFail _) -> True
  | _, _ -> False

let legal_local_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (kind:local_event_kind)
  (payload:B.bytes)
  (ev:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  local_event_kind_matches kind payload ev /\
  legal_response_for_event st0 st1 resp ev raw_sent raw_received network_out app_out

let decode_error_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == DecodeError /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_decode_error))
    B.empty
    B.empty
    network_out
    app_out

module TLS13.Impl.Client.Types

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

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

let tls_unexpected_message_error : T.tls_error = T.AlertError T.UnexpectedMessage

type local_event_kind =
  | LocalStartHandshake
  | LocalDeriveSharedSecret
  | LocalInstallClientHandshakeTrafficKeys
  | LocalInstallServerHandshakeTrafficKeys
  | LocalInstallClientApplicationTrafficKeys
  | LocalInstallServerApplicationTrafficKeys
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

let received_tls_raw_delta_legal
  (st0:CS.connection_state)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  : prop =
  CS.event_raw_delta_legal
    st0.CS.cs_model
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = msg;
    })
    B.empty
    raw_received

let wire_parse_success
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  : prop =
  exists ct.
    L.content_type_matches content_type ct /\
    WS.parse_tls_message ct fragment == Some msg

let wire_parse_failure
  (content_type:U8.t)
  (fragment:B.bytes)
  : prop =
  forall ct.
    L.content_type_matches content_type ct ==>
    WS.parse_tls_message ct fragment == None

let network_input_wf
  (st0:CS.connection_state)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  : prop =
  forall msg.
  wire_parse_success content_type fragment msg ==>
  received_tls_raw_delta_legal st0 msg raw_received

let parsed_message_wire_success
  (content_type:U8.t)
  (fragment:B.bytes)
  (l:L.tls_message)
  : prop =
  match l with
  | L.LTlsChangeCipherSpec ->
  wire_parse_success content_type fragment M.TlsChangeCipherSpec
  | L.LTlsAlert alert_wire ->
  forall alert.
    L.alert_description_matches alert_wire alert ==>
    wire_parse_success content_type fragment (M.TlsAlert alert)
  | L.LTlsHandshake L.LHelloRetryRequest ->
  wire_parse_success content_type fragment (M.TlsHandshake M.HelloRetryRequest)
  | _ ->
  exists msg. wire_parse_success content_type fragment msg

let parsed_message_wire_success_for
  (content_type:U8.t)
  (fragment:B.bytes)
  (l:L.tls_message)
  (msg:M.tls_message)
  : prop =
  wire_parse_success content_type fragment msg /\
  (match l, msg with
  | L.LTlsChangeCipherSpec, M.TlsChangeCipherSpec ->
    True
  | L.LTlsChangeCipherSpec, _ ->
    False
  | L.LTlsAlert alert_wire, M.TlsAlert alert ->
    L.alert_description_matches alert_wire alert
  | L.LTlsAlert _, _ ->
    False
  | L.LTlsHandshake L.LHelloRetryRequest, M.TlsHandshake M.HelloRetryRequest ->
    True
  | L.LTlsHandshake L.LHelloRetryRequest, _ ->
    False
  | L.LTlsHandshake (L.LServerHello _), M.TlsHandshake (M.ServerHello sh) ->
    Seq.equal fragment (WS.serialize_handshake (M.ServerHello sh))
  | L.LTlsHandshake (L.LServerHello _), _ ->
    False
  | L.LTlsHandshake (L.LClientHello _), M.TlsHandshake (M.ClientHello _) ->
    True
  | L.LTlsHandshake (L.LClientHello _), _ ->
    False
  | L.LTlsHandshake (L.LEncryptedExtensions _), M.TlsHandshake (M.EncryptedExtensions _) ->
    True
  | L.LTlsHandshake (L.LEncryptedExtensions _), _ ->
    False
  | L.LTlsHandshake (L.LCertificate _), M.TlsHandshake (M.Certificate _) ->
    True
  | L.LTlsHandshake (L.LCertificate _), _ ->
    False
  | L.LTlsHandshake (L.LCertificateVerify _), M.TlsHandshake (M.CertificateVerify _) ->
    True
  | L.LTlsHandshake (L.LCertificateVerify _), _ ->
    False
  | L.LTlsHandshake (L.LFinished _), M.TlsHandshake (M.Finished _) ->
    True
  | L.LTlsHandshake (L.LFinished _), _ ->
    False
  | L.LTlsApplicationData _, M.TlsApplicationData _ ->
    True
  | L.LTlsApplicationData _, _ ->
    False)

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
  | LocalInstallClientHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficWrite
  | LocalInstallServerHandshakeTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake /\
    install.CS.install_direction == CS.TrafficRead
  | LocalInstallClientApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficWrite
  | LocalInstallServerApplicationTrafficKeys, CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficApplication /\
    install.CS.install_direction == CS.TrafficRead
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

let unexpected_message_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  resp.status == IllegalTransition /\
  legal_response_for_event
    st0
    st1
    resp
    (CS.ConnLocalEvent (CS.LocalFail tls_unexpected_message_error))
    B.empty
    B.empty
    network_out
    app_out

let legal_handled_tls_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  legal_received_tls_response st0 st1 resp msg raw_received network_out app_out \/
  unexpected_message_response st0 st1 resp network_out app_out

let legal_network_response
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : prop =
  (exists msg.
     wire_parse_success content_type fragment msg /\
     legal_handled_tls_response st0 st1 resp msg raw_received network_out app_out) \/
  (wire_parse_failure content_type fragment /\
   decode_error_response st0 st1 resp network_out app_out)

let lemma_legal_network_response_decode_error
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires wire_parse_failure content_type fragment /\
                decode_error_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_unexpected
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (ct:T.content_type)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg /\
                unexpected_message_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_unexpected_from_parse_success
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires (exists ct msg.
                  L.content_type_matches content_type ct /\
                  WS.parse_tls_message ct fragment == Some msg) /\
                unexpected_message_response st0 st1 resp network_out app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_handled
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (ct:T.content_type)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires L.content_type_matches content_type ct /\
                WS.parse_tls_message ct fragment == Some msg /\
                legal_handled_tls_response
                  st0
                  st1
                  resp
                  msg
                  raw_received
                  network_out
                  app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

let lemma_legal_network_response_handled_from_parse_success
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (resp:client_response)
  (content_type:U8.t)
  (fragment:B.bytes)
  (msg:M.tls_message)
  (raw_received:B.bytes)
  (network_out:B.bytes)
  (app_out:B.bytes)
  : Lemma
      (requires wire_parse_success content_type fragment msg /\
                legal_handled_tls_response
                  st0
                  st1
                  resp
                  msg
                  raw_received
                  network_out
                  app_out)
      (ensures legal_network_response
        st0 st1 resp content_type fragment raw_received network_out app_out)
=
  ()

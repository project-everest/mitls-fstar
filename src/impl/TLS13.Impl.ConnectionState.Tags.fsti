module TLS13.Impl.ConnectionState.Tags

#lang-pulse

open Pulse.Lib.Pervasives

module CS = TLS13.Spec.ConnectionState
module IM = TLS13.Impl.Messages
module T = TLS13.Types
module U8 = FStar.UInt8

noextract
let endpoint_role_tag_matches (tag:U8.t) (role:CS.endpoint_role) : prop =
  match role with
  | CS.ClientEndpoint -> U8.v tag == 0
  | CS.ServerEndpoint -> U8.v tag == 1

noextract
let handshake_stage_tag_matches (tag:U8.t) (stage:CS.handshake_stage) : prop =
  match stage with
  | CS.HsNotStarted -> U8.v tag == 0
  | CS.HsStarted -> U8.v tag == 1
  | CS.HsClientHelloSent -> U8.v tag == 2
  | CS.HsServerHelloReceived -> U8.v tag == 3
  | CS.HsEncryptedExtensionsReceived -> U8.v tag == 4
  | CS.HsCertificateReceived -> U8.v tag == 5
  | CS.HsCertificateValidated -> U8.v tag == 6
  | CS.HsCertificateVerifyReceived -> U8.v tag == 7
  | CS.HsCertificateVerifyVerified -> U8.v tag == 8
  | CS.HsServerFinishedReceived -> U8.v tag == 9
  | CS.HsServerFinishedVerified -> U8.v tag == 10
  | CS.HsClientFinishedSent -> U8.v tag == 11

noextract
let alert_tag_matches (tag:U8.t) (alert:T.alert_description) : prop =
  IM.alert_description_matches tag alert

noextract
let tls_error_code_matches
  (code:U8.t)
  (alert:U8.t)
  (err:T.tls_error)
  : prop =
  match err with
  | T.AlertError a -> U8.v code == 0 /\ alert_tag_matches alert a
  | T.UnsupportedCipherSuite -> U8.v code == 1
  | T.UnsupportedNamedGroup -> U8.v code == 2
  | T.UnsupportedSignature -> U8.v code == 3
  | T.HelloRetryRequestRejected -> U8.v code == 4
  | T.BadCertificate -> U8.v code == 5
  | T.BadCertificateVerify -> U8.v code == 6
  | T.BadFinished -> U8.v code == 7
  | T.BadRecordTag -> U8.v code == 8
  | T.OutputBufferTooSmall -> U8.v code == 9
  | T.IoError -> U8.v code == 10

noextract
let failure_option_matches
  (present:bool)
  (code:U8.t)
  (alert:U8.t)
  (failure:option T.tls_error)
  : prop =
  if present then
    match failure with
    | Some err -> tls_error_code_matches code alert err
    | None -> False
  else
    failure == None

noextract
let control_state_matches
  (control_tag:U8.t)
  (stage_tag:U8.t)
  (failure_present:bool)
  (failure_code:U8.t)
  (failure_alert:U8.t)
  (control:CS.connection_control_state)
  : prop =
  match control with
  | CS.ControlNew ->
    U8.v control_tag == 0 /\ not failure_present
  | CS.ControlHandshaking stage ->
    U8.v control_tag == 1 /\
    handshake_stage_tag_matches stage_tag stage /\
    not failure_present
  | CS.ControlApplicationData ->
    U8.v control_tag == 2 /\ not failure_present
  | CS.ControlClosing ->
    U8.v control_tag == 3 /\ not failure_present
  | CS.ControlClosed ->
    U8.v control_tag == 4 /\ not failure_present
  | CS.ControlFailed err ->
    U8.v control_tag == 5 /\
    failure_present /\
    tls_error_code_matches failure_code failure_alert err

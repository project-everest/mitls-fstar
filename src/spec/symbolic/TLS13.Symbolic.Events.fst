module TLS13.Symbolic.Events

module B = TLS13.Bytes
module DY = DY.Core
module Terms = TLS13.Symbolic.Terms

type event_kind =
  | ClientSessionStarted
  | ServerSessionStarted
  | ClientHelloSent
  | ClientHelloAccepted
  | ServerHelloSent
  | ServerHelloAccepted
  | ServerCertificateVerifySigned
  | ServerCertificateVerifyAccepted
  | ServerFinishedSent
  | ServerFinishedAccepted
  | ClientFinishedSent
  | ClientFinishedAccepted
  | HandshakeTrafficSecretInstalled
  | ApplicationTrafficSecretInstalled
  | HandshakeComplete
  | ProtectedRecordSent
  | ProtectedRecordAccepted
  | ApplicationDataSent
  | ApplicationDataAccepted

let event_tag (kind:event_kind) : string =
  match kind with
  | ClientSessionStarted -> "TLS13.ClientSessionStarted"
  | ServerSessionStarted -> "TLS13.ServerSessionStarted"
  | ClientHelloSent -> "TLS13.ClientHelloSent"
  | ClientHelloAccepted -> "TLS13.ClientHelloAccepted"
  | ServerHelloSent -> "TLS13.ServerHelloSent"
  | ServerHelloAccepted -> "TLS13.ServerHelloAccepted"
  | ServerCertificateVerifySigned -> "TLS13.ServerCertificateVerifySigned"
  | ServerCertificateVerifyAccepted -> "TLS13.ServerCertificateVerifyAccepted"
  | ServerFinishedSent -> "TLS13.ServerFinishedSent"
  | ServerFinishedAccepted -> "TLS13.ServerFinishedAccepted"
  | ClientFinishedSent -> "TLS13.ClientFinishedSent"
  | ClientFinishedAccepted -> "TLS13.ClientFinishedAccepted"
  | HandshakeTrafficSecretInstalled ->
    "TLS13.HandshakeTrafficSecretInstalled"
  | ApplicationTrafficSecretInstalled ->
    "TLS13.ApplicationTrafficSecretInstalled"
  | HandshakeComplete -> "TLS13.HandshakeComplete"
  | ProtectedRecordSent -> "TLS13.ProtectedRecordSent"
  | ProtectedRecordAccepted -> "TLS13.ProtectedRecordAccepted"
  | ApplicationDataSent -> "TLS13.ApplicationDataSent"
  | ApplicationDataAccepted -> "TLS13.ApplicationDataAccepted"

type record_direction =
  | ClientToServer
  | ServerToClient

type record_epoch =
  | HandshakeEpoch
  | ApplicationEpoch

let encode_record_direction (direction:record_direction) : DY.bytes =
  match direction with
  | ClientToServer -> Terms.public_bytes (B.singleton 0uy)
  | ServerToClient -> Terms.public_bytes (B.singleton 1uy)

let encode_record_epoch (epoch:record_epoch) : DY.bytes =
  match epoch with
  | HandshakeEpoch -> Terms.public_bytes (B.singleton 0uy)
  | ApplicationEpoch -> Terms.public_bytes (B.singleton 1uy)

let handshake_event_content
  (context:Terms.session_context)
  (details:DY.bytes)
  : DY.bytes =
  DY.Concat (Terms.encode_session_context context) details

let record_event_details
  (direction:record_direction)
  (epoch:record_epoch)
  (sequence_number plaintext protected_record:DY.bytes)
  : DY.bytes =
  DY.Concat
    (encode_record_direction direction)
    (DY.Concat
      (encode_record_epoch epoch)
      (DY.Concat
        sequence_number
        (DY.Concat plaintext protected_record)))

let record_event_content
  (context:Terms.session_context)
  (direction:record_direction)
  (epoch:record_epoch)
  (sequence_number plaintext protected_record:DY.bytes)
  : DY.bytes =
  handshake_event_content
    context
    (record_event_details
      direction epoch sequence_number plaintext protected_record)

let event_entry
  (principal:DY.principal)
  (kind:event_kind)
  (content:DY.bytes)
  : DY.trace_entry =
  DY.Event principal (event_tag kind) content

let handshake_event_entry
  (principal:DY.principal)
  (kind:event_kind)
  (context:Terms.session_context)
  (details:DY.bytes)
  : DY.trace_entry =
  event_entry principal kind (handshake_event_content context details)

let record_event_entry
  (principal:DY.principal)
  (kind:event_kind)
  (context:Terms.session_context)
  (direction:record_direction)
  (epoch:record_epoch)
  (sequence_number plaintext protected_record:DY.bytes)
  : DY.trace_entry =
  event_entry
    principal
    kind
    (record_event_content
      context direction epoch sequence_number plaintext protected_record)

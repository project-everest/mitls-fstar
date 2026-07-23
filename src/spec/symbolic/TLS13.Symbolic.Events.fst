module TLS13.Symbolic.Events

(*
 * TLS-specific protocol events recorded in the DY trace.
 *
 * This module defines only event syntax and unambiguous encodings.  Constructing
 * an Event term does not prove that it occurred: Product controls which honest
 * transitions append entries, and Invariant assigns their origin meaning.
 *)

module B = TLS13.Bytes
module DY = DY.Core
module Terms = TLS13.Symbolic.Terms

(*
 * All protocol milestones represented by the symbolic product.
 *
 * Sent/accepted variants are distinct.  The security-critical origin events
 * used by authentication are CertificateVerifySigned, ServerFinishedSent, and
 * ClientFinishedSent; record events carry the complete protected-record tuple.
 *)
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

(*
 * Map each event constructor to a globally distinct trace tag.
 *
 * Lemmas.event_tag_injective later proves that equality of these strings
 * identifies the original event kind.
 *)
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

(* Direction of a TLS record relative to the client and server roles. *)
type record_direction =
  | ClientToServer
  | ServerToClient

(* Key-schedule epoch under which a protected record is processed. *)
type record_epoch =
  | HandshakeEpoch
  | ApplicationEpoch

(* Encode record direction as a public, constructor-distinct one-byte literal. *)
let encode_record_direction (direction:record_direction) : DY.bytes =
  match direction with
  | ClientToServer -> Terms.public_bytes (B.singleton 0uy)
  | ServerToClient -> Terms.public_bytes (B.singleton 1uy)

(* Encode handshake/application epoch as a public one-byte literal. *)
let encode_record_epoch (epoch:record_epoch) : DY.bytes =
  match epoch with
  | HandshakeEpoch -> Terms.public_bytes (B.singleton 0uy)
  | ApplicationEpoch -> Terms.public_bytes (B.singleton 1uy)

(*
 * Prefix event-specific details with the complete symbolic session context.
 *
 * This makes transcript and algorithm parameters part of the event identity.
 *)
let handshake_event_content
  (context:Terms.session_context)
  (details:DY.bytes)
  : DY.bytes =
  DY.Concat (Terms.encode_session_context context) details

(*
 * Encode the security-relevant protected-record tuple.
 *
 * The nested concatenation fixes direction, epoch, sequence token, plaintext,
 * and the complete symbolic AEAD record in a constructor-injective order.
 *)
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

(* Combine a session context with the encoded protected-record tuple. *)
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

(* Construct a raw DY Event entry from a principal, tag, and content term. *)
let event_entry
  (principal:DY.principal)
  (kind:event_kind)
  (content:DY.bytes)
  : DY.trace_entry =
  DY.Event principal (event_tag kind) content

(* Construct a context-bound handshake event entry. *)
let handshake_event_entry
  (principal:DY.principal)
  (kind:event_kind)
  (context:Terms.session_context)
  (details:DY.bytes)
  : DY.trace_entry =
  event_entry principal kind (handshake_event_content context details)

(* Construct a context-bound protected-record event entry. *)
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

module TLS13.StateMachine

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module R = TLS13.Record.Spec
module T = TLS13.Types
module Tr = TLS13.Transcript
module X = TLS13.X509.Spec

type role =
  | Client

type phase =
  | Start
  | ClientHelloSent
  | ServerHelloReceived
  | EncryptedExtensionsReceived
  | CertificateReceived
  | CertificateVerified
  | ServerFinishedVerified
  | ClientFinishedSent
  | ApplicationData
  | Closing
  | Closed
  | Failed

type conn_state = {
  role: role;
  phase: phase;
  transcript: Tr.transcript;
  read_state: R.direction_state;
  write_state: R.direction_state;
  peer: option X.peer_identity;
  failure: option T.tls_error;
}

type event =
  | SendClientHello of H.client_hello
  | RecvServerHello of H.server_hello
  | RecvEncryptedExtensions of H.encrypted_extensions
  | RecvCertificate of H.certificate_msg
  | RecvCertificateVerify of H.certificate_verify
  | RecvServerFinished of H.finished
  | SendClientFinished of H.finished
  | SendApplicationData of B.bytes
  | RecvApplicationData of B.bytes
  | SendCloseNotify
  | RecvCloseNotify
  | Fail of T.tls_error

let initial : conn_state =
  {
    role = Client;
    phase = Start;
    transcript = Tr.empty;
    read_state = R.initial_direction_state;
    write_state = R.initial_direction_state;
    peer = None;
    failure = None;
  }

let fail (s:conn_state) (e:T.tls_error) : conn_state =
  { s with phase = Failed; failure = Some e }

let step (s:conn_state) (e:event) : option conn_state =
  match s.phase, e with
  | Start, SendClientHello _ ->
    Some { s with phase = ClientHelloSent }
  | ClientHelloSent, RecvServerHello sh ->
    if H.is_supported_cipher_suite sh.H.cipher_suite
    then Some { s with phase = ServerHelloReceived }
    else Some (fail s T.UnsupportedCipherSuite)
  | ServerHelloReceived, RecvEncryptedExtensions _ ->
    Some { s with phase = EncryptedExtensionsReceived }
  | EncryptedExtensionsReceived, RecvCertificate _ ->
    Some { s with phase = CertificateReceived }
  | CertificateReceived, RecvCertificateVerify _ ->
    Some { s with phase = CertificateVerified }
  | CertificateVerified, RecvServerFinished _ ->
    Some { s with phase = ServerFinishedVerified }
  | ServerFinishedVerified, SendClientFinished _ ->
    Some { s with phase = ApplicationData }
  | ApplicationData, SendApplicationData _ ->
    Some s
  | ApplicationData, RecvApplicationData _ ->
    Some s
  | ApplicationData, SendCloseNotify ->
    Some { s with phase = Closing }
  | Closing, RecvCloseNotify ->
    Some { s with phase = Closed }
  | _, Fail err ->
    Some (fail s err)
  | _, _ ->
    None

let rec step_many (s:conn_state) (events:list event)
  : Tot (option conn_state)
        (decreases events)
  =
  match events with
  | [] -> Some s
  | e :: rest ->
    (match step s e with
     | None -> None
     | Some s' -> step_many s' rest)

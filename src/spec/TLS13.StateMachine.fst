module TLS13.StateMachine

(**
  Lightweight client-only abstract trace automaton.

  TLS13.Spec.ConnectionState is the main audit-facing state model. This module
  remains as a compact trace/state-machine vocabulary used by ConnectionLog and
  a few implementation proof projections. It is not the authoritative concrete
  connection-state spec; future server work should either generalize this small
  automaton by role or retire it behind the role-parametric ConnectionState
  model.
**)

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module T = TLS13.Types
module Tr = TLS13.Transcript
module X = TLS13.X509.Spec
module Sem = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished

type role =
  | Client

type phase =
  | Start
  | ClientHelloSent
  | ServerHelloReceived
  | EncryptedExtensionsReceived
  | CertificateReceived
  | CertificateValidated
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
  | SendClientHello of GCH.clientHello
  | RecvServerHello of GSH.serverHello
  | RecvEncryptedExtensions of GEE.encryptedExtensions
  | RecvCertificate of GCert.certificate
  | ValidateCertificate of X.peer_identity
  | RecvCertificateVerify of GCV.certificateVerify
  | RecvServerFinished of GFin.finished
  | SendClientFinished of GFin.finished
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

let with_phase (s:conn_state) (p:phase) : conn_state =
  { s with phase = p }

let with_validated_peer (s:conn_state) (peer:X.peer_identity) : conn_state =
  { s with phase = CertificateValidated; peer = Some peer }

let advance_write_record (s:conn_state) : conn_state =
  { s with write_state = R.next_seq s.write_state }

let max_application_data_fragment_len : nat = 16384

let rec application_data_record_count_len (len:nat) : Tot nat (decreases len) =
  if len <= max_application_data_fragment_len then 1
  else 1 + application_data_record_count_len (len - max_application_data_fragment_len)

let application_data_record_count (bytes:B.bytes) : nat =
  application_data_record_count_len (B.length bytes)

let rec advance_write_records (s:conn_state) (n:nat) : Tot conn_state (decreases n) =
  if n = 0 then s
  else advance_write_record (advance_write_records s (n - 1))

let lemma_application_data_record_count_len_small (len:nat)
  : Lemma
      (requires len <= max_application_data_fragment_len)
      (ensures application_data_record_count_len len == 1)
  =
  ()

let rec lemma_application_data_record_count_len_positive (len:nat)
  : Lemma
      (ensures 1 <= application_data_record_count_len len)
      (decreases len)
  =
  if len <= max_application_data_fragment_len then ()
  else lemma_application_data_record_count_len_positive (len - max_application_data_fragment_len)

let lemma_application_data_record_count_len_step (len:nat)
  : Lemma
      (requires max_application_data_fragment_len < len)
      (ensures application_data_record_count_len len ==
               1 + application_data_record_count_len (len - max_application_data_fragment_len))
  =
  ()

let lemma_advance_write_records_one (s:conn_state)
  : Lemma (advance_write_records s 1 == advance_write_record s)
  =
  ()

let lemma_advance_write_records_succ (s:conn_state) (n:nat)
  : Lemma (advance_write_records s (n + 1) == advance_write_record (advance_write_records s n))
  =
  ()

let rec lemma_advance_write_records_write_seq (s:conn_state) (n:nat)
  : Lemma
      (ensures (advance_write_records s n).write_state.R.seq == s.write_state.R.seq + n)
      (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_write_records_write_seq s (n - 1)

let rec lemma_advance_write_records_preserves_phase (s:conn_state) (n:nat)
  : Lemma (ensures (advance_write_records s n).phase == s.phase)
          (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_write_records_preserves_phase s (n - 1)

let rec lemma_advance_write_records_preserves_read_state (s:conn_state) (n:nat)
  : Lemma (ensures (advance_write_records s n).read_state == s.read_state)
          (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_write_records_preserves_read_state s (n - 1)

let advance_read_record (s:conn_state) : conn_state =
  { s with read_state = R.next_seq s.read_state }

let rec advance_read_records (s:conn_state) (n:nat) : Tot conn_state (decreases n) =
  if n = 0 then s
  else advance_read_record (advance_read_records s (n - 1))

let lemma_advance_read_records_one (s:conn_state)
  : Lemma (advance_read_records s 1 == advance_read_record s)
  =
  ()

let lemma_advance_read_records_succ (s:conn_state) (n:nat)
  : Lemma (advance_read_records s (n + 1) == advance_read_record (advance_read_records s n))
  =
  ()

let rec lemma_advance_read_records_after_one (s:conn_state) (n:nat)
  : Lemma
      (ensures advance_read_records (advance_read_record s) n == advance_read_records s (n + 1))
          (decreases n)
  =
  if n = 0 then lemma_advance_read_records_one s
  else lemma_advance_read_records_after_one s (n - 1)

let rec lemma_advance_read_records_append (s:conn_state) (n:nat) (m:nat)
  : Lemma
      (ensures advance_read_records (advance_read_records s n) m ==
               advance_read_records s (n + m))
      (decreases m)
  =
  if m = 0 then ()
  else
    let m1:nat = m - 1 in
    let nm1:nat = n + m1 in
    lemma_advance_read_records_append s n m1;
    lemma_advance_read_records_succ s nm1;
    assert (nm1 + 1 == n + m)

let rec lemma_advance_read_records_read_seq (s:conn_state) (n:nat)
  : Lemma
      (ensures (advance_read_records s n).read_state.R.seq == s.read_state.R.seq + n)
      (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_read_records_read_seq s (n - 1)

let rec lemma_advance_read_records_preserves_phase (s:conn_state) (n:nat)
  : Lemma (ensures (advance_read_records s n).phase == s.phase)
          (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_read_records_preserves_phase s (n - 1)

let rec lemma_advance_read_records_preserves_write_state (s:conn_state) (n:nat)
  : Lemma (ensures (advance_read_records s n).write_state == s.write_state)
          (decreases n)
  =
  if n = 0 then ()
  else lemma_advance_read_records_preserves_write_state s (n - 1)

let send_close_state (s:conn_state) : conn_state =
  { advance_write_record s with phase = Closing }

let recv_close_state (s:conn_state) : conn_state =
  { advance_read_record s with phase = Closed }

let step (s:conn_state) (e:event) : option conn_state =
  match s.phase, e with
  | Start, SendClientHello _ ->
    Some { s with phase = ClientHelloSent }
  | ClientHelloSent, RecvServerHello sh ->
    (match Sem.serverHello_cipher_suite sh with
     | Some cs ->
       if H.is_supported_cipher_suite cs
       then Some { s with phase = ServerHelloReceived }
       else Some (fail s T.UnsupportedCipherSuite)
     | None -> Some (fail s T.UnsupportedCipherSuite))
  | ServerHelloReceived, RecvEncryptedExtensions _ ->
    Some { s with phase = EncryptedExtensionsReceived }
  | EncryptedExtensionsReceived, RecvCertificate _ ->
    Some { s with phase = CertificateReceived }
  | CertificateReceived, ValidateCertificate peer ->
    Some (with_validated_peer s peer)
  | CertificateValidated, RecvCertificateVerify _ ->
    (match s.peer with
     | Some _ -> Some { s with phase = CertificateVerified }
     | None -> Some (fail s T.BadCertificate))
  | CertificateVerified, RecvServerFinished _ ->
    Some { s with phase = ServerFinishedVerified }
  | ServerFinishedVerified, SendClientFinished _ ->
    Some { s with phase = ApplicationData }
  | ApplicationData, SendApplicationData bytes ->
    Some (advance_write_records s (application_data_record_count bytes))
  | ApplicationData, RecvApplicationData _ ->
    Some (advance_read_record s)
  | ApplicationData, SendCloseNotify ->
    Some (send_close_state s)
  | ApplicationData, RecvCloseNotify
  | Closing, RecvCloseNotify ->
    Some (recv_close_state s)
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

let state_single_step : RTC.binrel conn_state =
  fun s0 s1 -> exists e. step s0 e == Some s1

let conn_evolves : RTC.preorder conn_state =
  RTC.closure state_single_step

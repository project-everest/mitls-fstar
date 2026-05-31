module TLS13.StateMachine.Lemmas

module H = TLS13.Handshake.Spec
module S = TLS13.StateMachine
module T = TLS13.Types
module B = TLS13.Bytes
module X = TLS13.X509.Spec

let lemma_initial_phase ()
  : Lemma (S.initial.S.phase == S.Start /\
           S.initial.S.failure == None)
  = ()

let lemma_fail_shape (s:S.conn_state) (err:T.tls_error)
  : Lemma ((S.fail s err).S.phase == S.Failed /\
           (S.fail s err).S.failure == Some err)
  = ()

let lemma_step_many_nil (s:S.conn_state)
  : Lemma (S.step_many s [] == Some s)
  = ()

let lemma_step_many_cons (s:S.conn_state) (e:S.event) (events:list S.event)
  : Lemma (S.step_many s (e :: events) ==
           (match S.step s e with
            | None -> None
            | Some s' -> S.step_many s' events))
  = ()

let lemma_send_client_hello_progress (ch:H.client_hello)
  : Lemma (match S.step S.initial (S.SendClientHello ch) with
           | Some s -> s.S.phase == S.ClientHelloSent /\ s.S.failure == None
           | None -> False)
  = ()

let lemma_server_hello_supported_progress (s:S.conn_state) (sh:H.server_hello)
  : Lemma (requires (s.S.phase == S.ClientHelloSent /\
                     H.is_supported_cipher_suite sh.H.cipher_suite == true))
          (ensures (match S.step s (S.RecvServerHello sh) with
                    | Some s' -> s'.S.phase == S.ServerHelloReceived /\ s'.S.failure == s.S.failure
                    | None -> False))
  = ()

let controlled_handshake_events
  (ch:H.client_hello)
  (sh:H.server_hello)
  (ee:H.encrypted_extensions)
  (cert:H.certificate_msg)
  (peer:X.peer_identity)
  (cv:H.certificate_verify)
  (sf:H.finished)
  (cf:H.finished)
  : list S.event =
  [
    S.SendClientHello ch;
    S.RecvServerHello sh;
    S.RecvEncryptedExtensions ee;
    S.RecvCertificate cert;
    S.ValidateCertificate peer;
    S.RecvCertificateVerify cv;
    S.RecvServerFinished sf;
    S.SendClientFinished cf
  ]

let lemma_controlled_handshake_reaches_application_data
  (ch:H.client_hello)
  (sh:H.server_hello)
  (ee:H.encrypted_extensions)
  (cert:H.certificate_msg)
  (peer:X.peer_identity)
  (cv:H.certificate_verify)
  (sf:H.finished)
  (cf:H.finished)
  : Lemma (requires H.is_supported_cipher_suite sh.H.cipher_suite == true)
          (ensures (match S.step_many S.initial
                            (controlled_handshake_events ch sh ee cert peer cv sf cf) with
                    | Some s -> s.S.phase == S.ApplicationData /\ s.S.failure == None
                    | None -> False))
  =
  assert_norm (match S.step_many S.initial
                       (controlled_handshake_events ch sh ee cert peer cv sf cf) with
               | Some s -> s.S.phase == S.ApplicationData /\ s.S.failure == None
               | None -> False)

let lemma_application_data_send_stays_application (s:S.conn_state) (bytes:TLS13.Bytes.bytes)
  : Lemma (requires s.S.phase == S.ApplicationData)
          (ensures (match S.step s (S.SendApplicationData bytes) with
                    | Some s' -> s' == S.advance_write_records s (S.application_data_record_count bytes) /\
                                 s'.S.phase == S.ApplicationData
                    | None -> False))
  =
  S.lemma_advance_write_records_preserves_phase s (S.application_data_record_count bytes)

let lemma_send_close_notify_progress (s:S.conn_state)
  : Lemma (requires s.S.phase == S.ApplicationData)
          (ensures (match S.step s S.SendCloseNotify with
                    | Some s' -> s' == S.send_close_state s /\
                                 s'.S.phase == S.Closing
                    | None -> False))
  = ()

let lemma_recv_close_notify_progress (s:S.conn_state)
  : Lemma (requires s.S.phase == S.ApplicationData \/ s.S.phase == S.Closing)
          (ensures (match S.step s S.RecvCloseNotify with
                    | Some s' -> s' == S.recv_close_state s /\
                                 s'.S.phase == S.Closed
                    | None -> False))
  = ()

let lemma_application_data_recv_stays_application (s:S.conn_state) (bytes:TLS13.Bytes.bytes)
  : Lemma (requires s.S.phase == S.ApplicationData)
          (ensures (match S.step s (S.RecvApplicationData bytes) with
                    | Some s' -> s' == S.advance_read_record s /\
                                 s'.S.phase == S.ApplicationData
                    | None -> False))
  = ()

module TLS13.StateMachine.Lemmas

module H = TLS13.Handshake.Spec
module S = TLS13.StateMachine
module T = TLS13.Types

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

let lemma_application_data_send_stays_application (s:S.conn_state) (bytes:TLS13.Bytes.bytes)
  : Lemma (requires s.S.phase == S.ApplicationData)
          (ensures (match S.step s (S.SendApplicationData bytes) with
                    | Some s' -> s' == s
                    | None -> False))
  = ()

let lemma_application_data_recv_stays_application (s:S.conn_state) (bytes:TLS13.Bytes.bytes)
  : Lemma (requires s.S.phase == S.ApplicationData)
          (ensures (match S.step s (S.RecvApplicationData bytes) with
                    | Some s' -> s' == s
                    | None -> False))
  = ()

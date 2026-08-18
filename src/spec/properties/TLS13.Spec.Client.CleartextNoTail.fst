module TLS13.Spec.Client.CleartextNoTail

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

(**
  Why the cleartext receive path needs no internal pipeline.

  The fork this work removes (INTERNAL_EVENT_PLAN.md §1.1) is that one physical
  record had two spec shapes: a chain of [ConnProtectedHandshake] events when it
  coalesced several handshake messages, and a single [ConnNetworkEvent] when it
  did not.  Phases 2--5 unified the *protected* receive path onto the pipeline.

  Phase 6 asks whether the two client-received *cleartext* handshake messages,
  [ServerHello] and [HelloRetryRequest], should join it too.  This module proves
  the answer is no, and that the answer is not a compromise: a cleartext
  handshake record cannot coalesce, so its [ConnNetworkEvent] description is the
  pipeline's zero-tail degenerate case rather than a competing shape.

  Two facts establish that.
 **)

(**
  A handshake message recovered from a record fragment occupies that fragment
  *exactly*.

  [W.parse_tls_message T.Handshake] is a whole-fragment parser: it succeeds only
  when the message ends where the fragment does.  So a cleartext handshake
  record can never carry a second message, and there is nothing for an internal
  step to drain.  This is the precise sense in which the cleartext path has no
  tail.
 **)
let lemma_cleartext_handshake_fragment_has_no_tail
  (fragment:B.bytes)
  (hs:M.handshake_msg)
  : Lemma
      (requires
        W.parse_tls_message T.Handshake fragment == Some (M.TlsHandshake hs))
      (ensures
        W.parse_handshake fragment == Some (hs, B.length fragment))
=
  W.lemma_parse_tls_message_handshake_some fragment hs

(**
  The two client-received cleartext handshake messages are exactly [ServerHello]
  and [HelloRetryRequest].

  [M.handshake_msg] has seven constructors.  [ClientHello] is client-*sent*;
  [EncryptedExtensions], [Certificate], [CertificateVerify] and [Finished] are
  precisely [CS.protected_handshake_message_supported], hence already on the
  internal pipeline.  Enumerating the remainder is what bounds Phase 6's scope
  to two messages, and it is checked here rather than asserted in prose.
 **)
let lemma_client_received_cleartext_handshake_messages
  (hs:M.handshake_msg)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Received (M.TlsHandshake hs) /\
        ~ (M.ClientHello? hs))
      (ensures M.ServerHello? hs \/ M.HelloRetryRequest? hs)
=
  match hs with
  | M.ServerHello _ -> ()
  | M.HelloRetryRequest -> ()
  | M.ClientHello _ -> ()
  | _ -> assert False

(**
  A cleartext handshake message is never a protected one, so the two receive
  descriptions are disjoint: no record is describable both ways.  Together with
  the previous lemma this is the formal statement that the cleartext exception
  of §9 S4 is *bounded* -- it covers two messages, neither of which the internal
  pipeline can accept.
 **)
let lemma_client_cleartext_disjoint_from_protected
  (hs:M.handshake_msg)
  : Lemma
      (requires
        CS.network_message_is_cleartext CL.Received (M.TlsHandshake hs))
      (ensures ~ (CS.protected_handshake_message_supported hs))
=
  match hs with
  | M.ServerHello _ -> ()
  | M.HelloRetryRequest -> ()
  | M.ClientHello _ -> ()
  | _ -> assert False

(**
  Internal work outstanding: unprocessed plaintext remains in the pending
  protected-handshake buffer.  This mirrors
  [TLS13.Impl.Client.Drain.internal_pending] at the model level.
 **)
let model_internal_pending (model:CS.connection_model) : prop =
  model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_parsed <
  B.length
    model.CS.model_handshake.CS.hs_buffers.CS.hb_encrypted_server_handshake_bytes

(**
  A record delivered as a [ConnNetworkEvent] leaves the pending buffer exactly
  as it found it.

  [CS.set_pending_protected_handshake] is the only writer of the two pending
  fields other than [CS.initial_buffers], and it is reachable only from
  [CS.step_protected_handshake].  (Other [hs_buffers] fields *are* written by
  handshake steps -- the certificate leaf and the CertificateVerify input --
  which is why the statement names the two pending fields rather than the whole
  record.)  So no [ConnNetworkEvent] -- cleartext or
  single-message protected -- can put the endpoint into a state with internal
  work outstanding.

  This is what Phase 7 needs: after delivering a cleartext record the channel is
  quiescent immediately, with no intervening internal moves, so the ready and
  quiescent clauses of the temporal argument are re-established at the delivery
  step itself.
 **)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_step_handshake_message_preserves_pending_buffer
  (model:CS.connection_model)
  (model1:CS.connection_model)
  (dir:CL.direction)
  (hsm:M.handshake_msg)
  : Lemma
      (requires CS.step_handshake_message model dir hsm == Some model1)
      (ensures
        model1.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes ==
          model.CS.model_handshake.CS.hs_buffers
            .CS.hb_encrypted_server_handshake_bytes /\
        model1.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed ==
          model.CS.model_handshake.CS.hs_buffers
            .CS.hb_encrypted_server_handshake_parsed)
=
  match dir, hsm, model.CS.model_control with
  | CL.Sent, M.ClientHello _, CS.ControlHandshaking CS.HsStarted -> ()
  | CL.Received, M.ClientHello _, CS.ControlHandshaking CS.HsAwaitingClientHello -> ()
  | CL.Received, M.ServerHello _, CS.ControlHandshaking CS.HsClientHelloSent -> ()
  | CL.Sent, M.ServerHello _, CS.ControlHandshaking CS.HsClientHelloReceived -> ()
  | CL.Sent, M.EncryptedExtensions _, CS.ControlHandshaking CS.HsServerHelloSent -> ()
  | CL.Sent, M.Certificate _, CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> ()
  | CL.Sent, M.CertificateVerify _, CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> ()
  | CL.Sent, M.Finished _, CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> ()
  | CL.Received, M.EncryptedExtensions _, CS.ControlHandshaking CS.HsServerHelloReceived -> ()
  | CL.Received, M.Certificate _, CS.ControlHandshaking CS.HsEncryptedExtensionsReceived -> ()
  | CL.Received, M.CertificateVerify _, CS.ControlHandshaking CS.HsCertificateValidated -> ()
  | CL.Received, M.Finished _, CS.ControlHandshaking CS.HsCertificateVerifyVerified -> ()
  | CL.Received, M.Finished _, CS.ControlHandshaking CS.HsServerFinishedSent -> ()
  | CL.Sent, M.Finished _, CS.ControlHandshaking CS.HsServerFinishedVerified -> ()
  | CL.Received, M.HelloRetryRequest, CS.ControlHandshaking CS.HsClientHelloSent -> ()
  | _, _, _ -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_network_event_preserves_pending_buffer
  (model:CS.connection_model)
  (model1:CS.connection_model)
  (tm:CL.directed_message M.tls_message)
  : Lemma
      (requires CS.step_model model (CS.ConnNetworkEvent tm) == Some model1)
      (ensures
        model1.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_bytes ==
          model.CS.model_handshake.CS.hs_buffers
            .CS.hb_encrypted_server_handshake_bytes /\
        model1.CS.model_handshake.CS.hs_buffers
          .CS.hb_encrypted_server_handshake_parsed ==
          model.CS.model_handshake.CS.hs_buffers
            .CS.hb_encrypted_server_handshake_parsed)
=
  match tm.CL.message_value, model.CS.model_control with
  | M.TlsHandshake hsm, _ ->
    lemma_step_handshake_message_preserves_pending_buffer
      model model1 tm.CL.message_direction hsm
  | M.TlsApplicationData _, CS.ControlApplicationData -> ()
  | M.TlsIgnoredPostHandshake _, CS.ControlApplicationData -> ()
  | M.TlsKeyUpdate _, CS.ControlApplicationData -> ()
  | _, _ -> ()
#pop-options

let lemma_network_event_preserves_quiescence
  (model:CS.connection_model)
  (model1:CS.connection_model)
  (tm:CL.directed_message M.tls_message)
  : Lemma
      (requires
        CS.step_model model (CS.ConnNetworkEvent tm) == Some model1 /\
        ~ (model_internal_pending model))
      (ensures ~ (model_internal_pending model1))
=
  lemma_network_event_preserves_pending_buffer model model1 tm

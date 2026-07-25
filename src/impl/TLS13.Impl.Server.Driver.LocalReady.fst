module TLS13.Impl.Server.Driver.LocalReady

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module M = TLS13.Messages
module SCQ = TLS13.Impl.Server.CanonicalQueries
module SS = TLS13.Impl.Server.Send
module ST = TLS13.Impl.Server.Types
module W = TLS13.Wire.Spec

let lemma_sign_certificate_verify_ready
  (st:CS.connection_state)
  (action:ST.next_local_action)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.next_local_action_sound st action /\
        action.ST.next_local_ready == true /\
        action.ST.next_local_kind == ST.LocalSignCertificateVerify /\
        Some? st.CS.cs_model.CS.model_config.CS.config_server /\
        (Some?.v st.CS.cs_model.CS.model_config.CS.config_server)
          .CS.server_certificate_chain == certificate_chain /\
        (Some?.v st.CS.cs_model.CS.model_config.CS.config_server)
          .CS.server_credential_identity == credential_identity /\
        DS.server_driver_supported_profile_selection st credential_identity)
      (ensures
        ST.server_local_event_input_ready st action.ST.next_local_kind B.empty /\
        ST.server_local_event_input_ready_with_credentials
          st
          action.ST.next_local_kind
          B.empty
          certificate_chain
          credential_identity)
=
  assert (st.CS.cs_model.CS.model_control ==
    CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (Some? st.CS.cs_model.CS.model_handshake.CS.hs_server_selection);
  let selection =
    Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_server_selection in
  assert (selection.CS.server_selected_signature_scheme ==
    TLS13.Types.Rsa_pss_rsae_sha256);
  assert (selection.CS.server_selected_credential == credential_identity);
  assert (ST.server_local_event_input_ready
    st action.ST.next_local_kind B.empty);
  ST.server_local_event_input_ready_with_state_credentials
    st
    action.ST.next_local_kind
    B.empty
    certificate_chain
    credential_identity

let lemma_internal_action_ready_with_credentials
  (st:CS.connection_state)
  (action:ST.next_local_action)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : Lemma
      (requires
        ST.next_local_action_sound st action /\
        action.ST.next_local_ready == true /\
        Some? st.CS.cs_model.CS.model_config.CS.config_server /\
        (Some?.v st.CS.cs_model.CS.model_config.CS.config_server)
          .CS.server_certificate_chain == certificate_chain /\
        (Some?.v st.CS.cs_model.CS.model_config.CS.config_server)
          .CS.server_credential_identity == credential_identity)
      (ensures
        (match action.ST.next_local_kind with
         | ST.LocalSelectServerParameters
         | ST.LocalDeriveSharedSecret
         | ST.LocalSendServerHello
         | ST.LocalSignCertificateVerify ->
           True
         | _ ->
           ST.server_local_event_input_ready
             st
             action.ST.next_local_kind
             B.empty /\
           ST.server_local_event_input_ready_with_credentials
             st
             action.ST.next_local_kind
             B.empty
             certificate_chain
             credential_identity))
=
  SCQ.server_internal_ready_implies_kind_ready st action;
  match action.ST.next_local_kind with
  | ST.LocalSelectServerParameters -> ()
  | ST.LocalDeriveSharedSecret -> ()
  | ST.LocalSendServerHello -> ()
  | ST.LocalSignCertificateVerify -> ()
  | _ ->
    ST.server_local_event_input_ready_with_state_credentials
      st
      action.ST.next_local_kind
      B.empty
      certificate_chain
      credential_identity

let lemma_send_certificate_verify_transcript_bound
  (st:CS.connection_state)
  : Lemma
      (requires
        ST.server_local_event_input_ready
          st
          ST.LocalSendCertificateVerify
          B.empty)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify /\
        (let cv =
           Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
         B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript +
           B.length (W.serialize_handshake (M.CertificateVerify cv)) <=
           Bounds.max_transcript_len))
=
  assert (Some? st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
  let cv =
    Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify in
  SS.lemma_serialize_handshake_certificate_verify_len cv

let lemma_can_verify_client_finished
  (st:CS.connection_state)
  : Lemma
      (requires
        ST.server_local_event_input_ready
          st
          ST.LocalVerifyClientFinished
          B.empty)
      (ensures
        Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished /\
        B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
          Bounds.max_transcript_len /\
        CM.can_verify_client_finished
          st
          (Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished))
=
  assert (Some? st.CS.cs_model.CS.model_handshake.CS.hs_client_finished);
  let fin =
    Some?.v st.CS.cs_model.CS.model_handshake.CS.hs_client_finished in
  SS.lemma_serialize_handshake_finished_len fin;
  assert (B.length st.CS.cs_model.CS.model_handshake.CS.hs_transcript + 36 <=
    Bounds.max_transcript_len);
  assert (CM.can_verify_client_finished st fin)

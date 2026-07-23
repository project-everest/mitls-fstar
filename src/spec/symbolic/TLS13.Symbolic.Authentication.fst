module TLS13.Symbolic.Authentication

module DY = DY.Core
module Bridge = TLS13.Symbolic.Bridge
module C = TLS13.Crypto.Spec
module Events = TLS13.Symbolic.Events
module Invariant = TLS13.Symbolic.Invariant
module Labels = TLS13.Symbolic.Labels
module M = TLS13.Messages
module Product = TLS13.Symbolic.Product
module SM = TLS13.Spec.StateMachine
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages
module Sem = TLS13.Wire.Semantics
module X = TLS13.X509.Spec

let client_accepts_server
  (state:Product.product_state)
  (shadow:Product.endpoint_shadow)
  (context:Terms.session_context)
  (verification_key:DY.bytes)
  : prop =
  Product.endpoint_member shadow state.Product.product_endpoints /\
  shadow.Product.shadow_session.Terms.session_role ==
    Terms.SymbolicClient /\
  shadow.Product.shadow_context == Some context /\
  shadow.Product.shadow_authenticated_server_key ==
    Some verification_key /\
  shadow.Product.shadow_certificate_verify_accepted == true /\
  shadow.Product.shadow_server_finished_accepted == true

let server_accepts_anonymous_client
  (state:Product.product_state)
  (shadow:Product.endpoint_shadow)
  (context:Terms.session_context)
  : prop =
  Product.endpoint_member shadow state.Product.product_endpoints /\
  shadow.Product.shadow_session.Terms.session_role ==
    Terms.SymbolicServer /\
  shadow.Product.shadow_context == Some context /\
  shadow.Product.shadow_client_finished_accepted == true

let trusted_server_matches_acceptance
  (state:Product.product_state)
  (client_shadow:Product.endpoint_shadow)
  (context:Terms.session_context)
  (verification_key:DY.bytes)
  (server:Bridge.trusted_server)
  : prop =
  Bridge.registered_server state.Product.product_registry server /\
  context.Terms.context_server.Terms.session_principal ==
    server.Bridge.trusted_server_principal /\
  verification_key == server.Bridge.trusted_server_symbolic_key /\
  client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_config.SM.config_server_name ==
    server.Bridge.trusted_server_name

let context_parameters_agree
  (left right:Terms.session_context)
  : prop =
  left.Terms.context_client == right.Terms.context_client /\
  left.Terms.context_server == right.Terms.context_server /\
  left.Terms.context_server_name == right.Terms.context_server_name /\
  left.Terms.context_cipher_suite == right.Terms.context_cipher_suite /\
  left.Terms.context_named_group == right.Terms.context_named_group /\
  left.Terms.context_signature_scheme == right.Terms.context_signature_scheme /\
  left.Terms.context_client_random == right.Terms.context_client_random /\
  left.Terms.context_server_random == right.Terms.context_server_random /\
  left.Terms.context_client_key_share == right.Terms.context_client_key_share /\
  left.Terms.context_server_key_share == right.Terms.context_server_key_share

let client_acceptance_transcript_evidence
  (state:Product.product_state)
  (client_shadow:Product.endpoint_shadow)
  (acceptance_context signature_context finished_context:Terms.session_context)
  (certificate_verify_message server_finished_message:DY.bytes)
  (certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify)
  (server_finished:TLS13.Wire.Generated.Finished.finished)
  (signature server_finished_tag:DY.bytes)
  : prop =
  context_parameters_agree acceptance_context signature_context /\
  context_parameters_agree acceptance_context finished_context /\
  client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_certificate_verify ==
    Some certificate_verify /\
  client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_server_finished ==
    Some server_finished /\
  Bridge.serialized_handshake_represents
    state.Product.product_representation
    (M.CertificateVerify certificate_verify)
    certificate_verify_message /\
  Bridge.serialized_handshake_represents
    state.Product.product_representation
    (M.Finished server_finished)
    server_finished_message /\
  Bridge.represents
    state.Product.product_representation
    (Sem.certificateVerify_signature_bytes certificate_verify)
    signature /\
  Bridge.represents
    state.Product.product_representation
    (Sem.finished_verify_data server_finished)
    server_finished_tag /\
  finished_context.Terms.context_transcript ==
    Terms.extend_transcript
      signature_context.Terms.context_transcript
      certificate_verify_message /\
  acceptance_context.Terms.context_transcript ==
    Terms.extend_transcript
      finished_context.Terms.context_transcript
      server_finished_message

let server_acceptance_transcript_evidence
  (state:Product.product_state)
  (server_shadow:Product.endpoint_shadow)
  (acceptance_context finished_context:Terms.session_context)
  (client_finished_message:DY.bytes)
  (client_finished:TLS13.Wire.Generated.Finished.finished)
  (client_finished_tag:DY.bytes)
  : prop =
  context_parameters_agree acceptance_context finished_context /\
  server_shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_client_finished ==
    Some client_finished /\
  Bridge.serialized_handshake_represents
    state.Product.product_representation
    (M.Finished client_finished)
    client_finished_message /\
  Bridge.represents
    state.Product.product_representation
    (Sem.finished_verify_data client_finished)
    client_finished_tag /\
  acceptance_context.Terms.context_transcript ==
    Terms.extend_transcript
      finished_context.Terms.context_transcript
      client_finished_message

let concrete_server_signature_bridge
  (state:Product.product_state)
  (client_shadow:Product.endpoint_shadow)
  (acceptance_context signature_context:Terms.session_context)
  (server:Bridge.trusted_server)
  (certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify)
  (verification_key signature:DY.bytes)
  (credential_label:DY.label)
  (concrete_signing_key:TLS13.Bytes.bytes)
  (signing_key signing_nonce:DY.bytes)
  : prop =
  context_parameters_agree acceptance_context signature_context /\
  Bridge.registered_server state.Product.product_registry server /\
  acceptance_context.Terms.context_server.Terms.session_principal ==
    server.Bridge.trusted_server_principal /\
  verification_key == server.Bridge.trusted_server_symbolic_key /\
  client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_config.SM.config_server_name ==
    server.Bridge.trusted_server_name /\
  verification_key == Terms.verification_key signing_key /\
  signature ==
    Terms.certificate_verify
      signing_key signing_nonce signature_context.Terms.context_transcript /\
  Terms.session_context_in_profile signature_context /\
  DY.bytes_invariant state.Product.product_trace verification_key /\
  DY.bytes_invariant
    state.Product.product_trace
    (Terms.certificate_verify_input signature_context.Terms.context_transcript) /\
  DY.bytes_invariant state.Product.product_trace signature /\
  verification_key `DY.has_signkey_usage state.Product.product_trace`
    Usages.signing_key_usage
      signature_context.Terms.context_server.Terms.session_principal
      verification_key /\
  DY.get_signkey_label state.Product.product_trace verification_key ==
    credential_label /\
  (match
     client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_validated_peer,
     client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_buffers.SM.hb_certificate_verify_input
   with
   | Some peer, Some concrete_input ->
     Bridge.x509_identity_bridge
       state.Product.product_representation
       state.Product.product_registry
       server
       client_shadow.Product.shadow_concrete.SM.cs_model.SM.model_config.SM.config_server_name
       peer.X.leaf_public_key /\
     Bridge.signature_bridge
       state.Product.product_representation
       concrete_signing_key
       peer.X.leaf_public_key
       signing_key
       signing_nonce
       (Terms.certificate_verify_input
         signature_context.Terms.context_transcript)
       concrete_input
       (Sem.certificateVerify_signature_bytes certificate_verify)
   | _, _ -> False)

let concrete_finished_bridge
  (state:Product.product_state)
  (context:Terms.session_context)
  (is_server:bool)
  (finished:TLS13.Wire.Generated.Finished.finished)
  (concrete_key concrete_message:C.secret)
  (traffic_secret finished_key finished_tag:DY.bytes)
  (traffic_label:DY.label)
  : prop =
  Terms.session_context_in_profile context /\
  finished_key == Terms.finished_key traffic_secret /\
  finished_tag ==
    Terms.finished_verify_data traffic_secret context.Terms.context_transcript /\
  Sem.finished_verify_data finished ==
    C.hmac_sha256 concrete_key concrete_message /\
  Bridge.hmac_bridge
    state.Product.product_representation
    concrete_key concrete_message
    finished_key
    (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.bytes_invariant state.Product.product_trace finished_key /\
  DY.bytes_invariant
    state.Product.product_trace
    (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.bytes_invariant state.Product.product_trace finished_tag /\
  finished_key `DY.has_usage state.Product.product_trace`
    (if is_server
     then DY.MacKey
       "TLS13.ServerFinishedKey"
       (Terms.transcript_hash context.Terms.context_transcript)
     else DY.MacKey
       "TLS13.ClientFinishedKey"
       (Terms.transcript_hash context.Terms.context_transcript)) /\
  DY.get_label state.Product.product_trace finished_key == traffic_label

let server_signature_verification
  (tr:DY.trace)
  (context:Terms.session_context)
  (verification_key signature:DY.bytes)
  (credential_label:DY.label)
  : prop =
  Terms.session_context_in_profile context /\
  DY.bytes_invariant tr verification_key /\
  DY.bytes_invariant
    tr
    (Terms.certificate_verify_input context.Terms.context_transcript) /\
  DY.bytes_invariant tr signature /\
  verification_key `DY.has_signkey_usage tr`
    Usages.signing_key_usage
      context.Terms.context_server.Terms.session_principal
      verification_key /\
  DY.verify
    verification_key
    (Terms.certificate_verify_input context.Terms.context_transcript)
    signature /\
  DY.get_signkey_label tr verification_key == credential_label

let server_finished_verification
  (tr:DY.trace)
  (context:Terms.session_context)
  (finished_key finished_tag:DY.bytes)
  (traffic_label:DY.label)
  : prop =
  Terms.session_context_in_profile context /\
  DY.bytes_invariant tr finished_key /\
  DY.bytes_invariant
    tr (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.bytes_invariant tr finished_tag /\
  finished_key `DY.has_usage tr`
    DY.MacKey
      "TLS13.ServerFinishedKey"
      (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.mac_verify
    finished_key
    (Terms.transcript_hash context.Terms.context_transcript)
    finished_tag /\
  DY.get_label tr finished_key == traffic_label

let client_finished_verification
  (tr:DY.trace)
  (context:Terms.session_context)
  (finished_key finished_tag:DY.bytes)
  (traffic_label:DY.label)
  : prop =
  Terms.session_context_in_profile context /\
  DY.bytes_invariant tr finished_key /\
  DY.bytes_invariant
    tr (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.bytes_invariant tr finished_tag /\
  finished_key `DY.has_usage tr`
    DY.MacKey
      "TLS13.ClientFinishedKey"
      (Terms.transcript_hash context.Terms.context_transcript) /\
  DY.mac_verify
    finished_key
    (Terms.transcript_hash context.Terms.context_transcript)
    finished_tag /\
  DY.get_label tr finished_key == traffic_label

val concrete_server_signature_bridge_implies_verification:
  state:Product.product_state ->
  client_shadow:Product.endpoint_shadow ->
  acceptance_context:Terms.session_context ->
  signature_context:Terms.session_context ->
  server:Bridge.trusted_server ->
  certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify ->
  verification_key:DY.bytes ->
  signature:DY.bytes ->
  credential_label:DY.label ->
  concrete_signing_key:TLS13.Bytes.bytes ->
  signing_key:DY.bytes ->
  signing_nonce:DY.bytes ->
  Lemma
    (requires
      concrete_server_signature_bridge
        state client_shadow acceptance_context signature_context server
        certificate_verify verification_key signature credential_label
        concrete_signing_key signing_key signing_nonce)
    (ensures
      trusted_server_matches_acceptance
        state client_shadow acceptance_context verification_key server /\
      server_signature_verification
        state.Product.product_trace
        signature_context verification_key signature credential_label)
let concrete_server_signature_bridge_implies_verification
  state client_shadow acceptance_context signature_context server
  certificate_verify verification_key signature credential_label
  concrete_signing_key signing_key signing_nonce =
  norm_spec
    [zeta; iota;
     delta_only
       [`%concrete_server_signature_bridge;
        `%trusted_server_matches_acceptance;
        `%Bridge.x509_identity_bridge]]
    (concrete_server_signature_bridge
      state client_shadow acceptance_context signature_context server
      certificate_verify verification_key signature credential_label
      concrete_signing_key signing_key signing_nonce);
  assert (trusted_server_matches_acceptance
    state client_shadow acceptance_context verification_key server);
  reveal_opaque (`%DY.verify) DY.verify

val concrete_finished_bridge_implies_verification:
  state:Product.product_state ->
  context:Terms.session_context ->
  is_server:bool ->
  finished:TLS13.Wire.Generated.Finished.finished ->
  concrete_key:C.secret ->
  concrete_message:C.secret ->
  traffic_secret:DY.bytes ->
  finished_key:DY.bytes ->
  finished_tag:DY.bytes ->
  traffic_label:DY.label ->
  Lemma
    (requires
      concrete_finished_bridge
        state context is_server finished concrete_key concrete_message
        traffic_secret finished_key finished_tag traffic_label)
    (ensures (
      if is_server
      then server_finished_verification
        state.Product.product_trace
        context finished_key finished_tag traffic_label
      else client_finished_verification
        state.Product.product_trace
        context finished_key finished_tag traffic_label))
let concrete_finished_bridge_implies_verification
  state context is_server finished concrete_key concrete_message
  traffic_secret finished_key finished_tag traffic_label =
  reveal_opaque (`%DY.mac_verify) DY.mac_verify;
  assert (match is_server with
    | true ->
        server_finished_verification
          state.Product.product_trace context
          finished_key finished_tag traffic_label
    | false ->
        client_finished_verification
          state.Product.product_trace context
          finished_key finished_tag traffic_label)

val client_acceptance_reflects_concrete_state:
  state:Product.product_state ->
  shadow:Product.endpoint_shadow ->
  context:Terms.session_context ->
  verification_key:DY.bytes ->
  Lemma
    (requires
      Product.product_well_formed state /\
      client_accepts_server state shadow context verification_key)
    (ensures
      shadow.Product.shadow_concrete.SM.cs_model.SM.model_config.SM.config_role ==
        SM.ClientEndpoint /\
      shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_certificate_verify_verified ==
        true /\
      shadow.Product.shadow_concrete.SM.cs_model.SM.model_handshake.SM.hs_server_finished_verified ==
        true)
let client_acceptance_reflects_concrete_state
  state shadow context verification_key =
  Product.endpoint_member_refines
    state.Product.product_representation
    state.Product.product_endpoints
    shadow

val server_acceptance_reflects_concrete_state:
  state:Product.product_state ->
  shadow:Product.endpoint_shadow ->
  context:Terms.session_context ->
  Lemma
    (requires
      Product.product_well_formed state /\
      server_accepts_anonymous_client state shadow context)
    (ensures
      shadow.Product.shadow_concrete.SM.cs_model.SM.model_config.SM.config_role ==
        SM.ServerEndpoint /\
      shadow.Product.shadow_concrete.SM.cs_model.SM.model_control ==
        SM.ControlApplicationData)
let server_acceptance_reflects_concrete_state state shadow context =
  Product.endpoint_member_refines
    state.Product.product_representation
    state.Product.product_endpoints
    shadow

val verified_server_signature_has_origin:
  tr:DY.trace ->
  context:Terms.session_context ->
  verification_key:DY.bytes ->
  signature:DY.bytes ->
  credential_label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant tr /\
      server_signature_verification
        tr context verification_key signature credential_label)
    (ensures
      DY.is_corrupt tr credential_label \/
      exists origin_context.
        Terms.session_context_in_profile origin_context /\
        origin_context.Terms.context_server.Terms.session_principal ==
          context.Terms.context_server.Terms.session_principal /\
        origin_context.Terms.context_transcript ==
          context.Terms.context_transcript /\
        DY.event_triggered
          tr
          origin_context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerCertificateVerifySigned)
          (Invariant.signature_origin_content
            origin_context
            verification_key
            (Terms.certificate_verify_input
              context.Terms.context_transcript)))
let verified_server_signature_has_origin
  tr context verification_key signature credential_label =
  let usage =
    Usages.signing_key_usage
      context.Terms.context_server.Terms.session_principal
      verification_key in
  DY.bytes_invariant_verify
    tr
    verification_key
    usage
    (Terms.certificate_verify_input context.Terms.context_transcript)
    signature;
  DY.flow_to_public_eq tr credential_label;
  if DY.is_corrupt tr credential_label
  then ()
  else Invariant.signature_origin
    tr
    usage
    verification_key
    (Terms.certificate_verify_input context.Terms.context_transcript)

val verified_server_finished_has_origin:
  tr:DY.trace ->
  context:Terms.session_context ->
  finished_key:DY.bytes ->
  finished_tag:DY.bytes ->
  traffic_label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant tr /\
      server_finished_verification
        tr context finished_key finished_tag traffic_label)
    (ensures
      DY.is_corrupt tr traffic_label \/
      exists origin_context.
        Terms.session_context_in_profile origin_context /\
        origin_context.Terms.context_transcript ==
          context.Terms.context_transcript /\
        DY.event_triggered
          tr
          origin_context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerFinishedSent)
          (Invariant.finished_origin_content
            origin_context
            finished_key
            (Terms.transcript_hash context.Terms.context_transcript)))
let verified_server_finished_has_origin
  tr context finished_key finished_tag traffic_label =
  let usage =
    DY.MacKey
      "TLS13.ServerFinishedKey"
      (Terms.transcript_hash context.Terms.context_transcript) in
  DY.bytes_invariant_mac_verify
    tr
    finished_key
    usage
    (Terms.transcript_hash context.Terms.context_transcript)
    finished_tag;
  DY.flow_to_public_eq tr traffic_label;
  if DY.is_corrupt tr traffic_label
  then ()
  else Invariant.finished_origin
    tr
    usage
    finished_key
    (Terms.transcript_hash context.Terms.context_transcript)

val verified_client_finished_has_origin:
  tr:DY.trace ->
  context:Terms.session_context ->
  finished_key:DY.bytes ->
  finished_tag:DY.bytes ->
  traffic_label:DY.label ->
  Lemma
    (requires
      DY.trace_invariant tr /\
      client_finished_verification
        tr context finished_key finished_tag traffic_label)
    (ensures
      DY.is_corrupt tr traffic_label \/
      exists origin_context.
        Terms.session_context_in_profile origin_context /\
        origin_context.Terms.context_transcript ==
          context.Terms.context_transcript /\
        DY.event_triggered
          tr
          origin_context.Terms.context_client.Terms.session_principal
          (Events.event_tag Events.ClientFinishedSent)
          (Invariant.finished_origin_content
            origin_context
            finished_key
            (Terms.transcript_hash context.Terms.context_transcript)))
let verified_client_finished_has_origin
  tr context finished_key finished_tag traffic_label =
  let usage =
    DY.MacKey
      "TLS13.ClientFinishedKey"
      (Terms.transcript_hash context.Terms.context_transcript) in
  DY.bytes_invariant_mac_verify
    tr
    finished_key
    usage
    (Terms.transcript_hash context.Terms.context_transcript)
    finished_tag;
  DY.flow_to_public_eq tr traffic_label;
  if DY.is_corrupt tr traffic_label
  then ()
  else Invariant.finished_origin
    tr
    usage
    finished_key
    (Terms.transcript_hash context.Terms.context_transcript)

let fresh_server_finished_origin
  (tr:DY.trace)
  (context:Terms.session_context)
  (finished_key:DY.bytes)
  : prop =
  forall left right.
    DY.event_triggered_at
      tr left
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerFinishedSent)
      (Invariant.finished_origin_content
        context finished_key
        (Terms.transcript_hash context.Terms.context_transcript)) /\
    DY.event_triggered_at
      tr right
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerFinishedSent)
      (Invariant.finished_origin_content
        context finished_key
        (Terms.transcript_hash context.Terms.context_transcript))
    ==> left == right

val server_finished_origin_is_fresh:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  state:Product.product_state ->
  context:Terms.session_context ->
  finished_key:DY.bytes ->
  Lemma
    (requires
      Invariant.securely_reachable_product_state
        initial transitions state)
    (ensures
      fresh_server_finished_origin
        state.Product.product_trace context finished_key)
let server_finished_origin_is_fresh
  initial transitions state context finished_key =
  Invariant.secure_product_execution_is_structural
    initial transitions state;
  Product.reachable_product_state_has_unique_security_events
    initial transitions state

val injective_server_agreement:
  initial:Product.product_state ->
  transitions:list Product.product_transition ->
  state:Product.product_state ->
  context:Terms.session_context ->
  finished_key:DY.bytes ->
  Lemma
    (requires
      Invariant.securely_reachable_product_state
        initial transitions state /\
      DY.event_triggered
        state.Product.product_trace
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (Invariant.finished_origin_content
          context finished_key
          (Terms.transcript_hash context.Terms.context_transcript)))
    (ensures
      exists unique_time.
        DY.event_triggered_at
          state.Product.product_trace unique_time
          context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerFinishedSent)
          (Invariant.finished_origin_content
            context finished_key
            (Terms.transcript_hash context.Terms.context_transcript)) /\
        forall other_time.
          DY.event_triggered_at
            state.Product.product_trace other_time
            context.Terms.context_server.Terms.session_principal
            (Events.event_tag Events.ServerFinishedSent)
            (Invariant.finished_origin_content
              context finished_key
              (Terms.transcript_hash context.Terms.context_transcript))
          ==> other_time == unique_time)
let injective_server_agreement
  initial transitions state context finished_key =
  server_finished_origin_is_fresh
    initial transitions state context finished_key;
  eliminate exists time.
    DY.event_triggered_at
      state.Product.product_trace time
      context.Terms.context_server.Terms.session_principal
      (Events.event_tag Events.ServerFinishedSent)
      (Invariant.finished_origin_content
        context finished_key
        (Terms.transcript_hash context.Terms.context_transcript))
  returns
    exists unique_time.
      DY.event_triggered_at
        state.Product.product_trace unique_time
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (Invariant.finished_origin_content
          context finished_key
          (Terms.transcript_hash context.Terms.context_transcript)) /\
      forall other_time.
        DY.event_triggered_at
          state.Product.product_trace other_time
          context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerFinishedSent)
          (Invariant.finished_origin_content
            context finished_key
            (Terms.transcript_hash context.Terms.context_transcript))
        ==> other_time == unique_time
  with _.
    introduce exists unique_time.
      DY.event_triggered_at
        state.Product.product_trace unique_time
        context.Terms.context_server.Terms.session_principal
        (Events.event_tag Events.ServerFinishedSent)
        (Invariant.finished_origin_content
          context finished_key
          (Terms.transcript_hash context.Terms.context_transcript)) /\
      forall other_time.
        DY.event_triggered_at
          state.Product.product_trace other_time
          context.Terms.context_server.Terms.session_principal
          (Events.event_tag Events.ServerFinishedSent)
          (Invariant.finished_origin_content
            context finished_key
            (Terms.transcript_hash context.Terms.context_transcript))
        ==> other_time == unique_time
    with time and ()

val concrete_client_acceptance_authenticates_named_server:
  state:Product.product_state ->
  client_shadow:Product.endpoint_shadow ->
  acceptance_context:Terms.session_context ->
  signature_context:Terms.session_context ->
  finished_context:Terms.session_context ->
  server:Bridge.trusted_server ->
  certificate_verify_message:DY.bytes ->
  server_finished_message:DY.bytes ->
  certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify ->
  server_finished:TLS13.Wire.Generated.Finished.finished ->
  verification_key:DY.bytes ->
  signature:DY.bytes ->
  credential_label:DY.label ->
  server_finished_key:DY.bytes ->
  server_finished_tag:DY.bytes ->
  server_traffic_label:DY.label ->
  concrete_signing_key:TLS13.Bytes.bytes ->
  signing_key:DY.bytes ->
  signing_nonce:DY.bytes ->
  concrete_server_finished_key:C.secret ->
  concrete_server_finished_message:C.secret ->
  server_traffic_secret:DY.bytes ->
  Lemma
    (requires
      Product.product_well_formed state /\
      DY.trace_invariant state.Product.product_trace /\
      client_accepts_server
        state client_shadow acceptance_context verification_key /\
      client_acceptance_transcript_evidence
        state client_shadow
        acceptance_context signature_context finished_context
        certificate_verify_message server_finished_message
        certificate_verify server_finished
        signature server_finished_tag /\
      concrete_server_signature_bridge
        state client_shadow acceptance_context signature_context server
        certificate_verify verification_key signature credential_label
        concrete_signing_key signing_key signing_nonce /\
      concrete_finished_bridge
        state finished_context true server_finished
        concrete_server_finished_key concrete_server_finished_message
        server_traffic_secret
        server_finished_key server_finished_tag server_traffic_label)
    (ensures
      DY.is_corrupt state.Product.product_trace credential_label \/
      DY.is_corrupt state.Product.product_trace server_traffic_label \/
      ((exists origin_context.
          origin_context.Terms.context_server.Terms.session_principal ==
            server.Bridge.trusted_server_principal /\
          origin_context.Terms.context_transcript ==
            signature_context.Terms.context_transcript /\
          DY.event_triggered
            state.Product.product_trace
            server.Bridge.trusted_server_principal
            (Events.event_tag Events.ServerCertificateVerifySigned)
            (Invariant.signature_origin_content
              origin_context
              verification_key
              (Terms.certificate_verify_input
                signature_context.Terms.context_transcript))) /\
       (exists origin_context.
          origin_context.Terms.context_transcript ==
            finished_context.Terms.context_transcript /\
          DY.event_triggered
            state.Product.product_trace
            origin_context.Terms.context_server.Terms.session_principal
            (Events.event_tag Events.ServerFinishedSent)
            (Invariant.finished_origin_content
              origin_context
              server_finished_key
              (Terms.transcript_hash
                finished_context.Terms.context_transcript)))))
let concrete_client_acceptance_authenticates_named_server
  state client_shadow acceptance_context signature_context finished_context
  server certificate_verify_message server_finished_message
  certificate_verify server_finished verification_key signature
  credential_label server_finished_key server_finished_tag
  server_traffic_label concrete_signing_key signing_key signing_nonce
  concrete_server_finished_key concrete_server_finished_message
  server_traffic_secret =
  client_acceptance_reflects_concrete_state
    state client_shadow acceptance_context verification_key;
  concrete_server_signature_bridge_implies_verification
    state client_shadow acceptance_context signature_context server
    certificate_verify verification_key signature credential_label
    concrete_signing_key signing_key signing_nonce;
  concrete_finished_bridge_implies_verification
    state finished_context true server_finished
    concrete_server_finished_key concrete_server_finished_message
    server_traffic_secret
    server_finished_key server_finished_tag server_traffic_label;
  verified_server_signature_has_origin
    state.Product.product_trace
    signature_context verification_key signature credential_label;
  verified_server_finished_has_origin
    state.Product.product_trace
    finished_context
    server_finished_key server_finished_tag server_traffic_label

val concrete_server_acceptance_confirms_anonymous_client:
  state:Product.product_state ->
  server_shadow:Product.endpoint_shadow ->
  acceptance_context:Terms.session_context ->
  finished_context:Terms.session_context ->
  client_finished_message:DY.bytes ->
  client_finished:TLS13.Wire.Generated.Finished.finished ->
  client_finished_key:DY.bytes ->
  client_finished_tag:DY.bytes ->
  client_traffic_label:DY.label ->
  concrete_client_finished_key:C.secret ->
  concrete_client_finished_message:C.secret ->
  client_traffic_secret:DY.bytes ->
  Lemma
    (requires
      Product.product_well_formed state /\
      DY.trace_invariant state.Product.product_trace /\
      server_accepts_anonymous_client
        state server_shadow acceptance_context /\
      server_acceptance_transcript_evidence
        state server_shadow acceptance_context finished_context
        client_finished_message client_finished client_finished_tag /\
      concrete_finished_bridge
        state finished_context false client_finished
        concrete_client_finished_key concrete_client_finished_message
        client_traffic_secret
        client_finished_key client_finished_tag client_traffic_label)
    (ensures
      DY.is_corrupt state.Product.product_trace client_traffic_label \/
      exists origin_context.
        origin_context.Terms.context_transcript ==
          finished_context.Terms.context_transcript /\
        DY.event_triggered
          state.Product.product_trace
          origin_context.Terms.context_client.Terms.session_principal
          (Events.event_tag Events.ClientFinishedSent)
          (Invariant.finished_origin_content
            origin_context
            client_finished_key
            (Terms.transcript_hash
              finished_context.Terms.context_transcript)))
let concrete_server_acceptance_confirms_anonymous_client
  state server_shadow acceptance_context finished_context
  client_finished_message client_finished
  client_finished_key client_finished_tag client_traffic_label
  concrete_client_finished_key concrete_client_finished_message
  client_traffic_secret =
  server_acceptance_reflects_concrete_state
    state server_shadow acceptance_context;
  concrete_finished_bridge_implies_verification
    state finished_context false client_finished
    concrete_client_finished_key concrete_client_finished_message
    client_traffic_secret
    client_finished_key client_finished_tag client_traffic_label;
  verified_client_finished_has_origin
    state.Product.product_trace
    finished_context
    client_finished_key client_finished_tag client_traffic_label

let full_session_transcript_evidence
  (state:Product.product_state)
  (client_shadow server_shadow:Product.endpoint_shadow)
  (signature_context server_finished_context
   client_finished_context server_acceptance_context:Terms.session_context)
  (certificate_verify_message server_finished_message
   client_finished_message:DY.bytes)
  (certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify)
  (server_finished client_finished:TLS13.Wire.Generated.Finished.finished)
  (signature server_finished_tag client_finished_tag:DY.bytes)
  : prop =
  client_acceptance_transcript_evidence
    state client_shadow
    client_finished_context signature_context server_finished_context
    certificate_verify_message server_finished_message
    certificate_verify server_finished
    signature server_finished_tag /\
  server_acceptance_transcript_evidence
    state server_shadow server_acceptance_context client_finished_context
    client_finished_message client_finished client_finished_tag

val concrete_full_session_agreement:
  state:Product.product_state ->
  client_shadow:Product.endpoint_shadow ->
  server_shadow:Product.endpoint_shadow ->
  signature_context:Terms.session_context ->
  server_finished_context:Terms.session_context ->
  client_finished_context:Terms.session_context ->
  server_acceptance_context:Terms.session_context ->
  server:Bridge.trusted_server ->
  certificate_verify_message:DY.bytes ->
  server_finished_message:DY.bytes ->
  client_finished_message:DY.bytes ->
  certificate_verify:TLS13.Wire.Generated.CertificateVerify.certificateVerify ->
  server_finished:TLS13.Wire.Generated.Finished.finished ->
  client_finished:TLS13.Wire.Generated.Finished.finished ->
  verification_key:DY.bytes ->
  signature:DY.bytes ->
  credential_label:DY.label ->
  server_finished_key:DY.bytes ->
  server_finished_tag:DY.bytes ->
  server_traffic_label:DY.label ->
  client_finished_key:DY.bytes ->
  client_finished_tag:DY.bytes ->
  client_traffic_label:DY.label ->
  concrete_signing_key:TLS13.Bytes.bytes ->
  signing_key:DY.bytes ->
  signing_nonce:DY.bytes ->
  concrete_server_finished_key:C.secret ->
  concrete_server_finished_message:C.secret ->
  server_traffic_secret:DY.bytes ->
  concrete_client_finished_key:C.secret ->
  concrete_client_finished_message:C.secret ->
  client_traffic_secret:DY.bytes ->
  Lemma
    (requires
      Product.product_well_formed state /\
      DY.trace_invariant state.Product.product_trace /\
      client_accepts_server
        state client_shadow client_finished_context verification_key /\
      server_accepts_anonymous_client
        state server_shadow server_acceptance_context /\
      full_session_transcript_evidence
        state client_shadow server_shadow
        signature_context server_finished_context
        client_finished_context server_acceptance_context
        certificate_verify_message server_finished_message
        client_finished_message
        certificate_verify server_finished client_finished
        signature server_finished_tag client_finished_tag /\
      concrete_server_signature_bridge
        state client_shadow client_finished_context signature_context server
        certificate_verify verification_key signature credential_label
        concrete_signing_key signing_key signing_nonce /\
      concrete_finished_bridge
        state server_finished_context true server_finished
        concrete_server_finished_key concrete_server_finished_message
        server_traffic_secret
        server_finished_key server_finished_tag server_traffic_label /\
      concrete_finished_bridge
        state client_finished_context false client_finished
        concrete_client_finished_key concrete_client_finished_message
        client_traffic_secret
        client_finished_key client_finished_tag client_traffic_label)
    (ensures
      DY.is_corrupt state.Product.product_trace credential_label \/
      DY.is_corrupt state.Product.product_trace server_traffic_label \/
      DY.is_corrupt state.Product.product_trace client_traffic_label \/
      ((exists signature_origin_context.
          signature_origin_context.Terms.context_server.Terms.session_principal ==
            server.Bridge.trusted_server_principal /\
          signature_origin_context.Terms.context_transcript ==
            signature_context.Terms.context_transcript /\
          DY.event_triggered
            state.Product.product_trace
            server.Bridge.trusted_server_principal
            (Events.event_tag Events.ServerCertificateVerifySigned)
            (Invariant.signature_origin_content
              signature_origin_context
              verification_key
              (Terms.certificate_verify_input
                signature_context.Terms.context_transcript))) /\
       (exists server_finished_origin_context.
          server_finished_origin_context.Terms.context_transcript ==
            server_finished_context.Terms.context_transcript /\
          DY.event_triggered
            state.Product.product_trace
            server_finished_origin_context.Terms.context_server.Terms.session_principal
            (Events.event_tag Events.ServerFinishedSent)
            (Invariant.finished_origin_content
              server_finished_origin_context
              server_finished_key
              (Terms.transcript_hash
                server_finished_context.Terms.context_transcript))) /\
       (exists client_finished_origin_context.
          client_finished_origin_context.Terms.context_transcript ==
            client_finished_context.Terms.context_transcript /\
          DY.event_triggered
            state.Product.product_trace
            client_finished_origin_context.Terms.context_client.Terms.session_principal
            (Events.event_tag Events.ClientFinishedSent)
            (Invariant.finished_origin_content
              client_finished_origin_context
              client_finished_key
              (Terms.transcript_hash
                client_finished_context.Terms.context_transcript)))))
let concrete_full_session_agreement
  state client_shadow server_shadow
  signature_context server_finished_context
  client_finished_context server_acceptance_context
  server certificate_verify_message server_finished_message
  client_finished_message certificate_verify server_finished client_finished
  verification_key signature credential_label
  server_finished_key server_finished_tag server_traffic_label
  client_finished_key client_finished_tag client_traffic_label
  concrete_signing_key signing_key signing_nonce
  concrete_server_finished_key concrete_server_finished_message
  server_traffic_secret
  concrete_client_finished_key concrete_client_finished_message
  client_traffic_secret =
  concrete_client_acceptance_authenticates_named_server
    state client_shadow client_finished_context
    signature_context server_finished_context server
    certificate_verify_message server_finished_message
    certificate_verify server_finished verification_key signature
    credential_label server_finished_key server_finished_tag
    server_traffic_label concrete_signing_key signing_key signing_nonce
    concrete_server_finished_key concrete_server_finished_message
    server_traffic_secret;
  concrete_server_acceptance_confirms_anonymous_client
    state server_shadow server_acceptance_context client_finished_context
    client_finished_message client_finished
    client_finished_key client_finished_tag client_traffic_label
    concrete_client_finished_key concrete_client_finished_message
    client_traffic_secret

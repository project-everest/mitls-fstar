module TLS13.ConnectionState.HandshakeAgreementNonReady

(* ========================================================================= *)
(* Brick 4 : NON-READY cross-endpoint HANDSHAKE record-material agreement.    *)
(*                                                                            *)
(* Establishes [peer_record_material_agrees (traffic_id TrafficHandshake      *)
(* ClientTraffic) client server] with NO readiness hypothesis on either       *)
(* endpoint, from bare consistency, the client-Finished send controls         *)
(* ([HsServerFinishedVerified] / [HsServerFinishedSent]), cross-endpoint       *)
(* hello / checkpoint correspondence, and MATERIAL-level record-key presence.  *)
(*                                                                            *)
(* ARCHITECTURE -- read before relocating anything:                           *)
(*  * ESTABLISHMENT IS AT THE SEND, CONSUMPTION AT THE DELIVERY.  It CANNOT    *)
(*    be moved to the delivery: the no-CCS shared-secret-presence producer     *)
(*    ([lemma_no_received_ccs_from_pairing_client]) requires BOTH [Seq.equal]   *)
(*    directions of [byte_pairing] -- the [Quiet] form.  At a [ToServer]        *)
(*    pre-state one direction degrades to [cs == sr ++ pl_raw], so that         *)
(*    producer cannot fire at the delivery, and the whole chain never starts.   *)
(*  * THE CARRIED PAIR IS NON-STALE because the server cannot move between the  *)
(*    client send and the delivery: from a [ToServer] state [server_serve] is   *)
(*    DISABLED ([System.fst:750]), so [deliver_to_server] is the only enabled   *)
(*    step -- zero intervening server steps.                                    *)
(*  * MATERIAL GATES ARE SEND-DISCHARGEABLE.  The client's [record_write]        *)
(*    material is present because it is sealing a protected Finished; the        *)
(*    server's [record_read] is a plain presence gate on an already-held field,  *)
(*    readable at the send pre-state.  Where the server read material is absent,  *)
(*    [open_record] returns [None], the [StateMachine.fst:774] flip cannot fire,  *)
(*    and the [AppSeqPairing] conjunct is vacuous.                               *)
(*  * [ControlFailed] LIMITATION: this producer is UNUSABLE at a failed server   *)
(*    (its controls exclude [ControlFailed]).  The application-epoch consumer     *)
(*    must therefore take agreement MONOTONICALLY from [app_material_agreement]    *)
(*    rather than re-deriving it here.                                            *)
(* ========================================================================= *)

module R = TLS13.Record.Spec
module C = TLS13.Crypto.Spec
module Seq = FStar.Seq
module SHSL = TLS13.ConnectionState.ServerHelloSelectionLink

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.WireFormatLemmas
open TLS13.ConnectionState.Lemmas

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* Non-ready [paired_x25519_key_shares] combine: replicates the body of        *)
(* [Pairing.fst:481] but substitutes the Brick-2 consistency-driven stable      *)
(* projections for the readiness-gated [*_application_ready_stable_*] versions.  *)
let lemma_paired_x25519_key_shares_nonready
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        server.cs_model.model_control =!= ControlHandshaking HsClientHelloReceived /\
        ~(ControlFailed? server.cs_model.model_control) /\
        paired_cleartext_hello_key_shares client server)
      (ensures paired_x25519_key_shares client server)
=
  lemma_consistent_shared_secret_stable_client_x25519_projection client;
  lemma_consistent_shared_secret_stable_server_x25519_projection server;
  assert (client_x25519_key_share_projection client);
  assert (server_x25519_key_share_projection server);
  assert (paired_cleartext_hello_key_shares client server);
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_start,
    client_hs.hs_client_hello,
    client_hs.hs_server_hello,
    client_hs.hs_keys.ks_shared_secret,
    server_hs.hs_server_selection,
    server_hs.hs_client_hello,
    server_hs.hs_server_hello,
    server_hs.hs_keys.ks_shared_secret
  with
  | Some start, Some client_ch, Some client_sh, Some client_shared,
    Some selection, Some server_ch, Some server_sh, Some server_shared ->
    (match
       start.start_client_key_share_private,
       selection.server_key_share_private
     with
     | Some client_sk, Some server_sk ->
       assert (client_hello_key_share client_ch ==
         client_hello_key_share server_ch);
       assert (server_hello_key_share client_sh ==
         server_hello_key_share server_sh);
       (match
          client_hello_key_share server_ch,
          server_hello_key_share client_sh
        with
        | Some ch_ks, Some sh_ks ->
          assert (ch_ks == start.start_client_key_share_public);
          assert (sh_ks == selection.server_key_share_public);
          assert (C.x25519_public_from_private client_sk ==
            start.start_client_key_share_public);
          assert (C.x25519_public_from_private server_sk ==
            selection.server_key_share_public);
          assert (C.x25519_shared client_sk sh_ks == Some client_shared);
          assert (C.x25519_shared server_sk ch_ks == Some server_shared)
        | _, _ -> assert False)
     | _, _ -> assert False)
  | _, _, _, _, _, _, _, _ -> assert False

#pop-options

(* ControlFailed-AWARE paired-x25519 combine (Gate 2a generalization).          *)
(* Identical to [lemma_paired_x25519_key_shares_nonready] but drops the server    *)
(* control restrictions [=!= HsClientHelloReceived] and [~ControlFailed?].  The    *)
(* server-side x25519 projection is recovered control-independently via            *)
(* [SHSL.lemma_server_x25519_key_share_projection_of_hello_present]: the load-      *)
(* bearing [x25519_shared server_sk ch_ks == Some shared] survives ControlFailed    *)
(* (server_x25519_reachable_shape's ControlFailed disjunction), and the one extra   *)
(* piece the non-failed proof used --- the sh<->sel link                            *)
(* [server_hello_key_share sh == selection.server_key_share_public] --- is a         *)
(* fail_model-preserved local fact (SHSL.lemma_consistent_server_hello_selection_    *)
(* link).  [paired_cleartext_hello_key_shares] already forces [Some? hs_server_      *)
(* hello], and the link shape then forces [Some? hs_server_selection].              *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_paired_x25519_key_shares_nonready_cf
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        paired_cleartext_hello_key_shares client server)
      (ensures paired_x25519_key_shares client server)
=
  lemma_consistent_shared_secret_stable_client_x25519_projection client;
  (* server-side projection, ControlFailed-robust *)
  SHSL.lemma_consistent_server_hello_selection_link server;
  assert (SHSL.server_hello_selection_link_shape server);
  (* [paired_cleartext_hello_key_shares] forces [Some? server.hs_server_hello]; *)
  (* the link shape's [Some sh, None -> False] arm then forces the selection.   *)
  assert (Some? server.cs_model.model_handshake.hs_server_hello);
  assert (Some? server.cs_model.model_handshake.hs_server_selection);
  SHSL.lemma_server_x25519_key_share_projection_of_hello_present server;
  assert (client_x25519_key_share_projection client);
  assert (server_x25519_key_share_projection server);
  assert (paired_cleartext_hello_key_shares client server);
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_start,
    client_hs.hs_client_hello,
    client_hs.hs_server_hello,
    client_hs.hs_keys.ks_shared_secret,
    server_hs.hs_server_selection,
    server_hs.hs_client_hello,
    server_hs.hs_server_hello,
    server_hs.hs_keys.ks_shared_secret
  with
  | Some start, Some client_ch, Some client_sh, Some client_shared,
    Some selection, Some server_ch, Some server_sh, Some server_shared ->
    (match
       start.start_client_key_share_private,
       selection.server_key_share_private
     with
     | Some client_sk, Some server_sk ->
       assert (client_hello_key_share client_ch ==
         client_hello_key_share server_ch);
       assert (server_hello_key_share client_sh ==
         server_hello_key_share server_sh);
       (match
          client_hello_key_share server_ch,
          server_hello_key_share client_sh
        with
        | Some ch_ks, Some sh_ks ->
          assert (ch_ks == start.start_client_key_share_public);
          assert (sh_ks == selection.server_key_share_public);
          assert (C.x25519_public_from_private client_sk ==
            start.start_client_key_share_public);
          assert (C.x25519_public_from_private server_sk ==
            selection.server_key_share_public);
          assert (C.x25519_shared client_sk sh_ks == Some client_shared);
          assert (C.x25519_shared server_sk ch_ks == Some server_shared)
        | _, _ -> assert False)
     | _, _ -> assert False)
  | _, _, _, _, _, _, _, _ -> assert False
#pop-options

(* Local copy of the internal [Lemmas.fst] slot-agreement bridge (not exposed  *)
(* in the interface): from expected-material match on both endpoints plus       *)
(* peer derived-key agreement, chain [Seq.equal] transitively to conclude the   *)
(* two key-schedule slots carry byte-identical record material.                 *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_local_key_schedule_traffic_record_material_agrees_from_expected
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        peer_derived_key_material_agrees (TrafficKey traffic_id) client server /\
        peer_derived_key_material_agrees (TrafficIV traffic_id) client server /\
        traffic_material_matches_expected_derived_material traffic_id client /\
        traffic_material_matches_expected_derived_material traffic_id server)
      (ensures
        key_schedule_traffic_record_material_agrees traffic_id client server)
=
  match
    traffic_material_for_label
      client.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_derived_key_material (TrafficKey traffic_id) client,
    expected_derived_key_material (TrafficIV traffic_id) client,
    traffic_material_for_label
      server.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_derived_key_material (TrafficKey traffic_id) server,
    expected_derived_key_material (TrafficIV traffic_id) server
  with
  | Some client_material, Some client_key, Some client_iv,
    Some server_material, Some server_key, Some server_iv ->
    assert (Seq.equal client_material.traffic_key client_key);
    assert (Seq.equal client_material.traffic_iv client_iv);
    assert (Seq.equal server_material.traffic_key server_key);
    assert (Seq.equal server_material.traffic_iv server_iv);
    assert (Seq.equal client_key server_key);
    assert (Seq.equal client_iv server_iv);
    Seq.lemma_eq_elim client_material.traffic_key client_key;
    Seq.lemma_eq_elim server_material.traffic_key server_key;
    Seq.lemma_eq_elim client_key server_key;
    Seq.lemma_eq_elim client_material.traffic_iv client_iv;
    Seq.lemma_eq_elim server_material.traffic_iv server_iv;
    Seq.lemma_eq_elim client_iv server_iv;
    assert (Seq.equal client_material.traffic_key server_material.traffic_key);
    assert (Seq.equal client_material.traffic_iv server_material.traffic_iv)
  | _, _, _, _, _, _ ->
    assert False
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_handshake_client_traffic_key_schedule_material_agrees_nonready
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        (server.cs_model.model_control =!= ControlHandshaking HsClientHelloReceived) /\
        (~(ControlFailed? server.cs_model.model_control)) /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        paired_cleartext_hello_key_shares client server /\
        same_key_derivation_checkpoint DeriveHandshakeTraffic client server /\
        Some? client.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic /\
        Some? server.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic)
      (ensures
        key_schedule_traffic_record_material_agrees
          (traffic_id TrafficHandshake ClientTraffic) client server)
=
  let tid = traffic_id TrafficHandshake ClientTraffic in
  assert (tid == traffic_id TrafficHandshake ClientTraffic);
  (* lineage from Brick 3.7 *)
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage client;
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage server;
  (* paired x25519 (non-ready); server control excludes HsClientHelloReceived + ControlFailed *)
  lemma_paired_x25519_key_shares_nonready client server;
  (* derived-key agreement for the record key and iv of tid *)
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficKey tid) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficIV tid) client server;
  (* slots match expected derived material (Brick 3.5) *)
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected client;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected server;
  assert (traffic_material_matches_expected_derived_material tid client);
  assert (traffic_material_matches_expected_derived_material tid server);
  (* slot agreement across endpoints *)
  lemma_local_key_schedule_traffic_record_material_agrees_from_expected tid client server
#pop-options



#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_handshake_client_traffic_peer_record_material_agrees_nonready
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        client.cs_model.model_control == ControlHandshaking HsServerFinishedVerified /\
        server.cs_model.model_control == ControlHandshaking HsServerFinishedSent /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        paired_cleartext_hello_key_shares client server /\
        same_key_derivation_checkpoint DeriveHandshakeTraffic client server /\
        Some? (record_direction_material client.cs_model.model_record.record_write) /\
        Some? (record_direction_material server.cs_model.model_record.record_read))
      (ensures
        peer_record_material_agrees
          (traffic_id TrafficHandshake ClientTraffic) client server)
=
  let tid = traffic_id TrafficHandshake ClientTraffic in
  assert (tid == traffic_id TrafficHandshake ClientTraffic);
  (* record-level key presence extracted from the material gates *)
  assert (Some? client.cs_model.model_record.record_write.R.key);
  assert (Some? server.cs_model.model_record.record_read.R.key);
  (* lineage from Brick 3.7 *)
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage client;
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage server;
  (* paired x25519 (non-ready); server control excludes HsClientHelloReceived + ControlFailed *)
  lemma_paired_x25519_key_shares_nonready client server;
  (* derived-key agreement for the record key and iv of tid *)
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficKey tid) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficIV tid) client server;
  (* record-keys consistency (Brick 3 Part 1) *)
  lemma_connection_state_consistent_record_keys_consistent_for_config_role client;
  lemma_connection_state_consistent_record_keys_consistent_for_config_role server;
  assert (model_record_keys_consistent_for_role ClientEndpoint client.cs_model);
  assert (model_record_keys_consistent_for_role ServerEndpoint server.cs_model);
  (* record epochs == Handshake (Brick 3.6) *)
  lemma_client_finished_verified_write_epoch_handshake client;
  lemma_server_finished_sent_read_epoch_handshake server;
  (* record<->key-schedule material match, both directions (Brick 3 Part 2) *)
  lemma_handshake_record_direction_material_matches_key_schedule_for_role
    ClientEndpoint TrafficWrite client.cs_model;
  lemma_handshake_record_direction_material_matches_key_schedule_for_role
    ServerEndpoint TrafficRead server.cs_model;
  assert (record_direction_material_matches_key_schedule_for_role
            ClientEndpoint TrafficWrite tid client.cs_model);
  assert (record_direction_material_matches_key_schedule_for_role
            ServerEndpoint TrafficRead tid server.cs_model);
  (* the match above forces the handshake traffic slot present on both *)
  assert (Some? client.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic);
  assert (Some? server.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic);
  (* slots match expected derived material (Brick 3.5) *)
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected client;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected server;
  assert (traffic_material_matches_expected_derived_material tid client);
  assert (traffic_material_matches_expected_derived_material tid server);
  (* slot agreement across endpoints *)
  lemma_local_key_schedule_traffic_record_material_agrees_from_expected tid client server;
  assert (key_schedule_traffic_record_material_agrees tid client server);
  (* assemble the inputs and conclude *)
  assert (peer_record_material_inputs_agree tid client server);
  lemma_peer_record_material_agrees tid client server
#pop-options

(* ControlFailed-AWARE slot-level agreement (Gate 2a generalization).           *)
(* Same as [lemma_handshake_client_traffic_key_schedule_material_agrees_nonready] *)
(* but drops the server control restrictions, using the CF-robust paired-x25519   *)
(* combine.  This is what the deliver_to_client flip establishment consumes: at    *)
(* the flip the server may already sit at [ControlFailed] (a protected            *)
(* Close_notify from the encrypted-flight window is legal and count-             *)
(* indistinguishable from a Finished; the crypto model has no INT-CTXT axiom to    *)
(* exclude it), and the SLOT-level agreement is exactly the fact that survives     *)
(* there --- unlike the record-level [peer_record_material_agrees], which epoch-    *)
(* checks record directions and goes blind under [model_record_keys_consistent =    *)
(* True] at ControlFailed. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_handshake_client_traffic_key_schedule_material_agrees_nonready_cf
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        paired_cleartext_hello_key_shares client server /\
        same_key_derivation_checkpoint DeriveHandshakeTraffic client server /\
        Some? client.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic /\
        Some? server.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic)
      (ensures
        key_schedule_traffic_record_material_agrees
          (traffic_id TrafficHandshake ClientTraffic) client server)
=
  let tid = traffic_id TrafficHandshake ClientTraffic in
  assert (tid == traffic_id TrafficHandshake ClientTraffic);
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage client;
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage server;
  (* CF-robust paired x25519: no server control restriction *)
  lemma_paired_x25519_key_shares_nonready_cf client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficKey tid) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficIV tid) client server;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected client;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected server;
  assert (traffic_material_matches_expected_derived_material tid client);
  assert (traffic_material_matches_expected_derived_material tid server);
  lemma_local_key_schedule_traffic_record_material_agrees_from_expected tid client server
#pop-options

(* ControlFailed-AWARE SERVER-traffic slot-level agreement.  Symmetric mirror of *)
(* [lemma_handshake_client_traffic_key_schedule_material_agrees_nonready_cf].     *)
(* Both handshake traffic secrets derive at the same DeriveHandshakeTraffic       *)
(* (TH_SH) checkpoint (Correspondence.derivation_checkpoint_inputs_agree on a     *)
(* TrafficKey reduces to key_checkpoint_for_epoch TrafficHandshake ==            *)
(* DeriveHandshakeTraffic), so the checkpoint hypothesis is unchanged from the    *)
(* client variant.  Only [tid] and the two slot-presence gates flip to           *)
(* ServerTraffic / ks_server_handshake_traffic.  See the .fsti for the consumer.  *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_handshake_server_traffic_key_schedule_material_agrees_nonready_cf
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent client /\
        connection_state_consistent server /\
        client.cs_model.model_config.config_role == ClientEndpoint /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        Some? client.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        paired_cleartext_hello_key_shares client server /\
        same_key_derivation_checkpoint DeriveHandshakeTraffic client server /\
        Some? client.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic /\
        Some? server.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic)
      (ensures
        key_schedule_traffic_record_material_agrees
          (traffic_id TrafficHandshake ServerTraffic) client server)
=
  let tid = traffic_id TrafficHandshake ServerTraffic in
  assert (tid == traffic_id TrafficHandshake ServerTraffic);
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage client;
  lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage server;
  lemma_paired_x25519_key_shares_nonready_cf client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficKey tid) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees (TrafficIV tid) client server;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected client;
  lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected server;
  assert (traffic_material_matches_expected_derived_material tid client);
  assert (traffic_material_matches_expected_derived_material tid server);
  lemma_local_key_schedule_traffic_record_material_agrees_from_expected tid client server
#pop-options

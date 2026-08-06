module TLS13.ConnectionState.HandshakeAgreementNonReady

(* Interface for Brick 4 : NON-READY cross-endpoint HANDSHAKE record-material   *)
(* agreement.  Exposes ONLY the top-level producer; the internal paired-x25519  *)
(* combine and slot-agreement bridge stay hidden.  See the .fst header for the  *)
(* establish-at-send / consume-at-delivery architecture and the ControlFailed   *)
(* limitation. *)

module R = TLS13.Record.Spec

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.WireFormatLemmas

(* From bare consistency, the client-Finished send controls, cross-endpoint     *)
(* hello / handshake-checkpoint correspondence, and MATERIAL-level record-key    *)
(* presence on the client write and server read directions, conclude that the    *)
(* client's write record material and the server's read record material for the  *)
(* handshake ClientTraffic epoch are byte-identical.  No readiness on either      *)
(* endpoint.  The server record-read presence is a plain send-readable gate;      *)
(* where it is absent the delivery's [open_record] fails and the consumer's       *)
(* conjunct is vacuous. *)
(* SLOT-LEVEL variant (Gate 2a): the first half of Brick 4, cut at the           *)
(* key-schedule slot agreement.  Concludes only that the two                      *)
(* [ks_client_handshake_traffic] slots carry byte-identical record material,      *)
(* with NO record-direction material gates and NO fixed client/server controls    *)
(* (only the server exclusion of [HsClientHelloReceived]/[ControlFailed] that     *)
(* [paired_x25519_key_shares_nonready] needs).  Used to establish conjunct 1      *)
(* ([hs_material_agreement]) at the deliver_to_client flip. *)
val lemma_handshake_client_traffic_key_schedule_material_agrees_nonready
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

val lemma_handshake_client_traffic_peer_record_material_agrees_nonready
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

(* ControlFailed-AWARE slot-level variant (Gate 2a): drops the server control    *)
(* restrictions of [lemma_handshake_client_traffic_key_schedule_material_agrees_  *)
(* nonready].  Consumed at the deliver_to_client flip, where the server may       *)
(* already sit at [ControlFailed].  Sound because the SLOT-level agreement        *)
(* depends only on the x25519 key-share projection (which survives ControlFailed  *)
(* via server_x25519_reachable_shape's disjunction + the fail_model-preserved     *)
(* sh<->sel link), NOT on record-key consistency (which goes blind at             *)
(* ControlFailed). *)
val lemma_handshake_client_traffic_key_schedule_material_agrees_nonready_cf
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

(* ControlFailed-AWARE SERVER-traffic slot-level agreement.  The symmetric      *)
(* mirror of [lemma_handshake_client_traffic_key_schedule_material_agrees_       *)
(* nonready_cf], for the TrafficHandshake SERVER direction.  Control-free for    *)
(* the same reason: the SLOT-level agreement depends only on the x25519 key-     *)
(* share projection (which survives ControlFailed via server_x25519_reachable_   *)
(* shape's disjunction), NOT on record-key consistency.  Both handshake traffic  *)
(* secrets derive at the SAME DeriveHandshakeTraffic (TH_SH) checkpoint, so the   *)
(* checkpoint hypothesis is identical to the client-traffic variant --- and it    *)
(* is available pre-flag from CLEARTEXT hello raw bytes alone via                 *)
(* [lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw]         *)
(* (WireFormatLemmas.fsti), not from [paired_handshake_events].                   *)
(*                                                                                *)
(* Consumed to force FAITHFUL DECODE of an in-flight server Finished by the       *)
(* client (client handshake READ material == server handshake WRITE material for  *)
(* ServerTraffic), which excludes the alert-decode arm and is the load-bearing    *)
(* step behind [finished_delivered_appread_coupling]'s server->client half.       *)
(* Reusable for the reverse direction (the mirror flip at StateMachine.fst:738).  *)
val lemma_handshake_server_traffic_key_schedule_material_agrees_nonready_cf
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

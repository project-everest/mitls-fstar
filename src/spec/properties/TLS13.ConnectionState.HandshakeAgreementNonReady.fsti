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

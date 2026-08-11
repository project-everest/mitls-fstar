module TLS13.ConnectionState.ProtectedWireServerFlightInversion.RedundantInstall

(**
  Caution-2 crux, MECHANIZED as a green fact.

  A REDUNDANT handshake traffic-key install at the model reached after the
  server (resp. client) has already installed those keys is:

    * MODEL-NEUTRAL: [step_model M install == Some M].  The record-layer install
      ([R.install_keys]) is a CONSTANT function of (epoch, alg, key, iv) — it ignores
      the prior direction state entirely — so re-installing the SAME material is
      idempotent; and the key-schedule update rewrites a field to the value it
      already holds, hence is identity.  Neither the model control nor any other
      field is touched by an install.

    * LEGAL: a server handshake write install is legal exactly at
      [ControlHandshaking HsServerHelloSent] (the stage the server occupies
      throughout its outgoing encrypted flight, since installs do not advance the
      control stage); the material-matches-key-schedule side condition is carried
      over unchanged.

    * BYTE-NEUTRAL: a [ConnLocalEvent] contributes empty deltas on both raw
      streams, so it may be PREPENDED to a seal / decode replay without changing
      the observable bytes.

  This is the exact fact needed to collapse the Stage-1 install [region] to the
  single write-install (resp. read-install) HEAD demanded by
  [ProtectedWireServerFlight.fsti:1090]:  peel the whole region (byte-neutral,
  via the [Region] helper), landing at the post-region model M, then PREPEND a
  redundant write-install (threading M's ACTUAL current handshake material —
  Caution 2) to expose the [install :: EE :: ...] flight head.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module R = TLS13.Record.Spec
module SMReplay = TLS13.Spec.StateMachine.Replay
module Seq = FStar.Seq

(** The server handshake WRITE key-install event carrying [material]. *)
let server_hs_write_install_event (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = material;
      };
    })

(** The client handshake READ key-install event carrying [material]. *)
let client_hs_read_install_event (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = material;
    })

(** The record-layer "write keys already installed with [material]" side
    condition, phrased as an idempotence equality on [R.install_keys]. *)
let server_write_keys_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_record.CS.record_write ==
    R.install_keys m.CS.model_record.CS.record_write R.Handshake
      material.CS.traffic_alg material.CS.traffic_key material.CS.traffic_iv

let client_read_keys_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_record.CS.record_read ==
    R.install_keys m.CS.model_record.CS.record_read R.Handshake
      material.CS.traffic_alg material.CS.traffic_key material.CS.traffic_iv

(** The material-matches-key-schedule legality side condition (server write). *)
let server_write_material_matches (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint
    m.CS.model_handshake {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material;
    }

(** The material-matches-key-schedule legality side condition (client read). *)
let client_read_material_matches (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  CS.traffic_install_matches_key_schedule_for_role CS.ClientEndpoint
    m.CS.model_handshake {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = material;
    }

(** The full "redundant server write install applies as the identity" bundle. *)
let server_redundant_write_install_ok (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == Some material /\
  server_write_keys_installed m material /\
  server_write_material_matches m material

let client_redundant_read_install_ok (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == Some material /\
  client_read_keys_installed m material /\
  client_read_material_matches m material

(* ------------------------------------------------------------------ *)
(* Model-neutrality + legality of the redundant installs.             *)
(* ------------------------------------------------------------------ *)

(** A redundant server handshake write install is legal and model-neutral. *)
val lemma_redundant_server_hs_write_install_identity
  (m:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires server_redundant_write_install_ok m material)
      (ensures
        CS.legal_event m (server_hs_write_install_event material) /\
        CS.step_model m (server_hs_write_install_event material) == Some m)

(** A redundant client handshake read install is legal and model-neutral. *)
val lemma_redundant_client_hs_read_install_identity
  (m:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires client_redundant_read_install_ok m material)
      (ensures
        CS.legal_event m (client_hs_read_install_event material) /\
        CS.step_model m (client_hs_read_install_event material) == Some m)

(* ------------------------------------------------------------------ *)
(* Byte-neutral prepend of the redundant install to a replay.         *)
(* ------------------------------------------------------------------ *)

(** Prepend a redundant server write install to a sent-seal replay — the
    Caution-2 region-collapse step that produces the [install :: flight] head. *)
val lemma_prepend_redundant_server_hs_write_install_sent
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        server_redundant_write_install_ok m material /\
        SMReplay.conn_events_sent_seal_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_sent_seal_replay
          m (server_hs_write_install_event material :: rest) rs rr final)

(** Prepend a redundant client read install to a received-decode replay. *)
val lemma_prepend_redundant_client_hs_read_install_received
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        client_redundant_read_install_ok m material /\
        SMReplay.conn_events_received_decode_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_received_decode_replay
          m (client_hs_read_install_event material :: rest) rs rr final)

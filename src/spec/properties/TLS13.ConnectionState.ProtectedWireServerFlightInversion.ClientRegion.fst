module TLS13.ConnectionState.ProtectedWireServerFlightInversion.ClientRegion

(**
  Client install-region preservation, MECHANIZED green.

  The client handshake install [region] (all elements are client handshake
  [LocalInstallTrafficKeys], per [ClientCanonicalShape.is_client_hs_install]) is
  replayed from a model already at [ControlHandshaking HsServerHelloReceived].
  We prove:

    * every such install PRESERVES the control stage, the role, and — once the
      read keys are installed — the installed read-key material
      ([client_read_installed]); a WRITE install leaves the read fields untouched,
      a (redundant) READ install re-installs the SAME material (legality forces its
      material to equal [traffic_key_material_for_secret] of the stable expected
      secret, since installs never change [ks_handshake_secret] or [hs_transcript]);
    * a READ install ESTABLISHES [client_read_installed].

  Composed over the whole region (list induction + [PWReplay] head-peel), this
  yields the post-region hypothesis
  [RedundantInstall.client_redundant_read_install_ok M material] required to
  PREPEND the single read-install head demanded by [:1090].
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module R = TLS13.Record.Spec
module RI = TLS13.ConnectionState.ProtectedWireServerFlightInversion.RedundantInstall
module SMReplay = TLS13.Spec.StateMachine.Replay
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq
module L = FStar.List.Tot
module CCShape = TLS13.ConnectionState.ClientCanonicalShape

(** The read-keys-installed post-condition (server handshake traffic material). *)
let client_read_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == Some material /\
  RI.client_read_keys_installed m material /\
  RI.client_read_material_matches m material

(** A client handshake install event (read or write). *)
let client_hs_install_ev (install:CS.traffic_key_install) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)

(* ------------------------------------------------------------------ *)
(* Per-step preservation.                                             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_install_step_preserves
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        CS.legal_event m (client_hs_install_ev install) /\
        CS.step_model m (client_hs_install_ev install) == Some m1 /\
        client_read_installed m material)
      (ensures client_read_installed m1 material /\
               m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived)
=
  ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_read_install_establishes
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        install.CS.install_direction == CS.TrafficRead /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        CS.legal_event m (client_hs_install_ev install) /\
        CS.step_model m (client_hs_install_ev install) == Some m1)
      (ensures client_read_installed m1 install.CS.install_material)
=
  ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_install_step_preserves_control
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        CS.legal_event m (client_hs_install_ev install) /\
        CS.step_model m (client_hs_install_ev install) == Some m1)
      (ensures
        m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived)
=
  ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Extract the install from a client-hs-install event.                *)
(* ------------------------------------------------------------------ *)

let install_of_client_hs (ev:CS.conn_event{CCShape.is_client_hs_install ev == true})
  : (install:CS.traffic_key_install{
      ev == client_hs_install_ev install /\
      install.CS.install_epoch == CS.TrafficHandshake})
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) -> install

(* ------------------------------------------------------------------ *)
(* Region induction: monotone preservation + existence.              *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_region_preserves_read_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        client_read_installed m material /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures client_read_installed final material)
      (decreases region)
=
  match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_client_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns client_read_installed final material
    with _.
    (
      lemma_client_install_step_preserves m install model1 material;
      lemma_client_region_preserves_read_installed model1 rest tail_sent tail_received final material
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_region_read_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        (exists (er:CS.conn_event). L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). client_read_installed final material))
      (decreases region)
=
  match region with
  | [] ->
    (* [exists er. memP er []] is False, so this case is vacuous. *)
    ()
  | ev :: rest ->
    let install = install_of_client_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns (exists (material:CS.traffic_key_material). client_read_installed final material)
    with _.
    (
      if install.CS.install_direction = CS.TrafficRead
      then
        (lemma_client_read_install_establishes m install model1;
         lemma_client_region_preserves_read_installed
           model1 rest tail_sent tail_received final install.CS.install_material)
      else
        (lemma_client_install_step_preserves_control m install model1;
         (* ev is a WRITE install, so the read install lies in [rest]. *)
         eliminate exists (er:CS.conn_event).
           L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er
         returns (exists (er2:CS.conn_event). L.memP er2 rest /\ CCShape.is_client_hs_install_dir CS.TrafficRead er2)
         with _. ();
         lemma_client_region_read_installed model1 rest tail_sent tail_received final)
    )
#pop-options


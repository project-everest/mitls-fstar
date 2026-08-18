module TLS13.ConnectionState.ProtectedWireServerFlightInversion

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CCShape = TLS13.ConnectionState.ClientCanonicalShape
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CNoCcs = TLS13.ConnectionState.ClientNoCcsFromPairing
module CReg = TLS13.ConnectionState.ProtectedWireServerFlightInversion.ClientRegion
module CS = TLS13.Spec.StateMachine
module Corr = TLS13.Spec.StateMachine.Correspondence
module GCH = TLS13.Wire.Generated.ClientHello
module GCV = TLS13.Wire.Generated.CertificateVerify
module GCert = TLS13.Wire.Generated.Certificate
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GFin = TLS13.Wire.Generated.Finished
module GSH = TLS13.Wire.Generated.ServerHello
module Inj = TLS13.Wire.Spec.Reveal.Injective
module KI = TLS13.Spec.StateMachine.KeyIdentifiers
module KM = TLS13.Spec.StateMachine.KeyMaterial
module L = FStar.List.Tot
module Lemmas = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module PB = TLS13.ConnectionState.ProtectedWireBase
module PWBase = TLS13.ConnectionState.ProtectedWireBase
module PWAlign = TLS13.ConnectionState.ProtectedWireRecordAlignment
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module PWSFlight = TLS13.ConnectionState.ProtectedWireServerFlight
module PWHead = TLS13.ConnectionState.ProtectedWireHead
module PWNorm = TLS13.ConnectionState.ProtectedWireNormalize
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Pairing = TLS13.Impl.Driver.Pairing
module R = TLS13.Record.Spec
module RI = TLS13.ConnectionState.ProtectedWireServerFlightInversion.RedundantInstall
module RR = TLS13.Wire.Spec.Reveal.Record
module Region = TLS13.ConnectionState.ProtectedWireServerFlightInversion.Region
module SCShape = TLS13.ConnectionState.ServerCanonicalShape
module SD = TLS13.Impl.Server.Driver
module SMReplay = TLS13.Spec.StateMachine.Replay
module SNoCcs = TLS13.ConnectionState.ServerNoCcsFromPairing
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript
module U8 = FStar.UInt8
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas
module WRD = TLS13.Wire.Spec.RevealDecode
module WS = TLS13.Wire.Spec
module WStep = TLS13.System.WireStep

open TLS13.ConnectionState.ProtectedWireBase

noeq type sysp = { client : CS.connection_state; server : CS.connection_state }

(* ================= inlined from Scratch_GoalA ================= *)


#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_goalA_state (s:sysp)
  : Lemma (requires server_flight_bridge_inputs s.client s.server)
          (ensures (
            match s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
                  s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
            | Some ss, Some cs -> Seq.equal cs ss
            | _ -> False))
  =
    assert (CD.client_driver_application_ready s.client);
    assert (SD.server_driver_application_ready s.server);
    assert (four_hellos_present s.client s.server);
    assert (hks_ok s.client s.server);
    // paired_cleartext_hello_key_shares from hello_key_shares_ok under four_hellos
    assert (TLS13.Spec.WireFormatLemmas.paired_cleartext_hello_key_shares s.client s.server);
    // projection inputs -> paired_x25519_key_shares
    assert (Pairing.client_server_driver_x25519_key_share_projection_inputs s.client s.server);
    Pairing.lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
      s.client s.server;
    assert (Corr.paired_x25519_key_shares s.client s.server);
    // lineage from ready (connection_state_consistent + app keys installed)
    Lemmas.lemma_connection_application_keys_supported_profile_key_schedule_lineage
      CS.ClientEndpoint s.client;
    Lemmas.lemma_connection_application_keys_supported_profile_key_schedule_lineage
      CS.ServerEndpoint s.server;
    assert (Corr.connection_supported_profile_key_schedule_lineage s.client);
    assert (Corr.connection_supported_profile_key_schedule_lineage s.server);
    // base secret agree at HandshakeSecret
    Lemmas.lemma_paired_x25519_key_shares_base_secret_agree KI.HandshakeSecret s.client s.server;
    assert (KM.base_secret_inputs_agree KI.HandshakeSecret s.client s.server);
    ()
#pop-options

(* ================= inlined from Scratch_GoalB ================= *)


#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_front_handshake_record_agree (f1 f2 r1 r2 w:B.bytes)
  : Lemma
      (requires
        B.length f1 <= 16640 /\ B.length f2 <= 16640 /\
        Seq.equal w (B.append (WS.serialize_record T.Handshake f1) r1) /\
        Seq.equal w (B.append (WS.serialize_record T.Handshake f2) r2))
      (ensures Seq.equal f1 f2 /\ Seq.equal r1 r2)
  =
    let d1 = WS.serialize_record T.Handshake f1 in
    let d2 = WS.serialize_record T.Handshake f2 in
    WS.lemma_parse_record_serialize_record T.Handshake f1;
    WS.lemma_parse_record_serialize_record T.Handshake f2;
    assert (B.length d1 == 5 + B.length f1);
    assert (B.length d2 == 5 + B.length f2);
    let h1 = RR.serialize_record_header T.Handshake (B.length f1) in
    let h2 = RR.serialize_record_header T.Handshake (B.length f2) in
    RR.lemma_serialize_record_reveal T.Handshake f1;
    RR.lemma_serialize_record_reveal T.Handshake f2;
    RR.lemma_serialize_handshake_record_header_reveal (B.length f1);
    RR.lemma_serialize_handshake_record_header_reveal (B.length f2);
    // h1, h2 are the length-5 record headers; d_i = h_i ++ f_i
    assert (B.length h1 == 5);
    assert (B.length h2 == 5);
    // headers coincide with the first 5 bytes of w on both sides
    assert (Seq.equal h1 (Seq.slice w 0 5));
    assert (Seq.equal h2 (Seq.slice w 0 5));
    assert (Seq.equal h1 h2);
    // extract the two length bytes (indices 3, 4)
    let l1 = B.length f1 in
    let l2 = B.length f2 in
    assert (Seq.index h1 3 == RR.byte (l1 / 256));
    assert (Seq.index h1 4 == RR.byte l1);
    assert (Seq.index h2 3 == RR.byte (l2 / 256));
    assert (Seq.index h2 4 == RR.byte l2);
    assert (RR.byte (l1 / 256) == RR.byte (l2 / 256));
    assert (RR.byte l1 == RR.byte l2);
    RR.lemma_byte_value l1;
    RR.lemma_byte_value l2;
    RR.lemma_byte_value (l1 / 256);
    RR.lemma_byte_value (l2 / 256);
    assert (l1 % 256 == l2 % 256);
    assert ((l1 / 256) % 256 == (l2 / 256) % 256);
    // l1, l2 <= 16640 < 65536, so l_i / 256 <= 65 < 256
    assert (l1 == l2);
    assert (B.length d1 == B.length d2);
    assert (Seq.equal d1 (Seq.slice w 0 (B.length d1)));
    assert (Seq.equal d2 (Seq.slice w 0 (B.length d2)));
    assert (Seq.equal d1 d2);
    Inj.lemma_serialize_record_injective T.Handshake f1 f2;
    // r1 == r2 from append cancellation
    assert (Seq.equal r1 (Seq.slice w (B.length d1) (B.length w)));
    assert (Seq.equal r2 (Seq.slice w (B.length d2) (B.length w)));
    ()
#pop-options

(* ================= inlined from Scratch_Transcript ================= *)


#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let slice_prefix (a b:B.bytes)
  : Lemma (ensures Seq.equal (Seq.slice (B.append a b) 0 (B.length a)) a)
= ()
#pop-options

(* CH-direction: the server's parsed ClientHello serialize-image equals the
   client's serialized ClientHello, from the paired byte streams. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let lemma_ch_serialize_agree
  (ch_c ch_s:GCH.clientHello)
  (cs sr:B.bytes)
  (client_suffix_sent server_suffix_recv d_ch:B.bytes)
  : Lemma
      (requires
        (let sh_c_ser = W.serialize_handshake (M.ClientHello ch_c) in
         B.length sh_c_ser <= 16640 /\
         Seq.equal cs (B.append (W.serialize_record T.Handshake sh_c_ser) client_suffix_sent) /\
         Seq.equal sr (B.append d_ch server_suffix_recv) /\
         Seq.equal cs sr /\
         CS.received_cleartext_tls_message_raw
           (M.TlsHandshake (M.ClientHello ch_s)) d_ch))
      (ensures
        Seq.equal
          (W.serialize_handshake (M.ClientHello ch_c))
          (W.serialize_handshake (M.ClientHello ch_s)))
=
  let sh_c_ser = W.serialize_handshake (M.ClientHello ch_c) in
  let front_c = W.serialize_record T.Handshake sh_c_ser in
  let l1 = B.length front_c in
  (* parse the client's front record *)
  WFL.lemma_parse_record_wire_serialize_record T.Handshake sh_c_ser;
  (* propositional equalities on the streams *)
  Seq.lemma_eq_elim cs (B.append front_c client_suffix_sent);
  Seq.lemma_eq_elim cs sr;
  Seq.lemma_eq_elim sr (B.append d_ch server_suffix_recv);
  (* front_c is the length-l1 prefix of cs *)
  slice_prefix front_c client_suffix_sent;
  Seq.lemma_eq_elim (Seq.slice cs 0 l1) front_c;
  WRD.lemma_parse_record_wire_from_prefix cs T.Handshake sh_c_ser l1;
  (* unfold the server's received parse property *)
  assert (CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch_s)) d_ch);
  eliminate exists (frag:M.sealed_record).
    W.parse_record_wire d_ch == Some (T.Handshake, frag, B.length d_ch) /\
    W.parse_tls_message T.Handshake frag == Some (M.TlsHandshake (M.ClientHello ch_s))
  with
  (
    let ld = B.length d_ch in
    (* d_ch is the length-ld prefix of cs (via cs == sr == d_ch ++ server_suffix_recv) *)
    slice_prefix d_ch server_suffix_recv;
    Seq.lemma_eq_elim (Seq.slice cs 0 ld) d_ch;
    WRD.lemma_parse_record_wire_from_prefix cs T.Handshake frag ld;
    (* determinism: both parses of cs coincide *)
    assert (W.parse_record_wire cs == Some (T.Handshake, sh_c_ser, l1));
    assert (W.parse_record_wire cs == Some (T.Handshake, frag, ld));
    assert (frag == sh_c_ser);
    W.lemma_parse_tls_message_round_trip T.Handshake sh_c_ser
  )
#pop-options

(* ================= inlined from Scratch_Preserve ================= *)


(* ------------------------------------------------------------------ *)
(* Per-step preservation of the shared / handshake secret.            *)
(* The only step_model clauses that touch ks_shared_secret /          *)
(* ks_handshake_secret are the two LocalDeriveSharedSecret clauses,    *)
(* whose legality forces ks_shared_secret == None, contradicting       *)
(* Some?; every other clause leaves both fields untouched.             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 300"
let lemma_step_preserves_secrets
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        Some? m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        m1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        m1.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? m1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
=
  match ev with
  | CS.ConnProtectedHandshake _ -> ()
  | CS.ConnLocalEvent (CS.LocalDeriveSharedSecret _) -> ()
  | _ -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_sent_replay_preserves_secrets
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m evs rs rr final /\
        Some? m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    with
    (
      lemma_step_preserves_secrets m ev model1;
      lemma_sent_replay_preserves_secrets model1 rest tail_sent tail_received final
    )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_received_replay_preserves_secrets
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m evs rs rr final /\
        Some? m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    with
    (
      lemma_step_preserves_secrets m ev model1;
      lemma_received_replay_preserves_secrets model1 rest tail_sent tail_received final
    )
#pop-options

(* ------------------------------------------------------------------ *)
(* A legal local event at a control stage where no key install is      *)
(* legal is not a record-key install.                                  *)
(*  - server: at HsServerEncryptedFlightSent, a role install requires  *)
(*    stage HsServerHelloSent / HsServerFinishedSent /                 *)
(*    HsClientFinishedReceived, and a non-role install requires the    *)
(*    ClientEndpoint role.                                             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_flight_local_not_install
  (m:CS.connection_model) (ev:CS.local_event)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        CS.legal_event m (CS.ConnLocalEvent ev))
      (ensures PWBase.local_event_does_not_install_record_keys ev)
=
  ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_local_not_install_at
  (m:CS.connection_model) (ev:CS.local_event) (stage:CS.handshake_stage)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking stage /\
        (~(stage == CS.HsServerHelloReceived)) /\
        (~(stage == CS.HsServerFinishedVerified)) /\
        CS.legal_event m (CS.ConnLocalEvent ev))
      (ensures PWBase.local_event_does_not_install_record_keys ev)
=
  ()
#pop-options

(* ================= inlined from Scratch_ServerRegion ================= *)


(** The write-keys-installed post-condition (server handshake traffic material). *)
let server_write_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == Some material /\
  RI.server_write_keys_installed m material /\
  RI.server_write_material_matches m material

(** A server handshake install event (read or write). *)
let server_hs_install_ev (install:CS.role_traffic_key_install) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole install)

(* ------------------------------------------------------------------ *)
(* Per-step preservation.                                             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_install_step_preserves
  (m:CS.connection_model) (install:CS.role_traffic_key_install)
  (m1:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        install.CS.install_role == CS.ServerEndpoint /\
        install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
        CS.legal_event m (server_hs_install_ev install) /\
        CS.step_model m (server_hs_install_ev install) == Some m1 /\
        server_write_installed m material)
      (ensures server_write_installed m1 material /\
               m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent)
=
  ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_write_install_establishes
  (m:CS.connection_model) (install:CS.role_traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_role == CS.ServerEndpoint /\
        install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
        install.CS.install_payload.CS.install_direction == CS.TrafficWrite /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        CS.legal_event m (server_hs_install_ev install) /\
        CS.step_model m (server_hs_install_ev install) == Some m1)
      (ensures server_write_installed m1 install.CS.install_payload.CS.install_material)
=
  ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_server_install_step_preserves_control
  (m:CS.connection_model) (install:CS.role_traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_role == CS.ServerEndpoint /\
        install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        CS.legal_event m (server_hs_install_ev install) /\
        CS.step_model m (server_hs_install_ev install) == Some m1)
      (ensures
        m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent)
=
  ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Extract the install from a server-hs-install event.                *)
(* ------------------------------------------------------------------ *)

let install_of_server_hs (ev:CS.conn_event{SCShape.is_server_hs_install ev == true})
  : (install:CS.role_traffic_key_install{
      ev == server_hs_install_ev install /\
      install.CS.install_role == CS.ServerEndpoint /\
      install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake})
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole install) -> install

(* ------------------------------------------------------------------ *)
(* Region induction: monotone preservation + existence.              *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_region_preserves_write_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        server_write_installed m material /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures server_write_installed final material)
      (decreases region)
=
  match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    with
    (
      lemma_server_install_step_preserves m install model1 material;
      lemma_server_region_preserves_write_installed model1 rest tail_sent tail_received final material
    )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_server_region_write_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        (exists (ew:CS.conn_event). L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew) /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). server_write_installed final material))
      (decreases region)
=
  match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    with
    (
      if install.CS.install_payload.CS.install_direction = CS.TrafficWrite
      then
        (lemma_server_write_install_establishes m install model1;
         lemma_server_region_preserves_write_installed
           model1 rest tail_sent tail_received final install.CS.install_payload.CS.install_material)
      else
        (lemma_server_install_step_preserves_control m install model1;
         eliminate exists (ew:CS.conn_event).
           L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew
         with ();
         lemma_server_region_write_installed model1 rest tail_sent tail_received final)
    )
#pop-options

(* ================= inlined from Scratch_Prefix ================= *)


let server_prefix_transcript (ch:GCH.clientHello) (sh:GSH.serverHello) : GTot B.bytes =
  Tr.append
    (Tr.append Tr.empty (W.serialize_handshake (M.ClientHello ch)))
    (W.serialize_handshake (M.ServerHello sh))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_server_prefix_model
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ServerEndpoint /\
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model cfg)
          (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
          ps pr p)
      (ensures
        p.CS.model_config == cfg /\
        p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
        p.CS.model_handshake.CS.hs_server_hello == Some sh /\
        p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let r1 = [e1; e2; e3; e4] in
  let r2 = [e2; e3; e4] in
  let r3 = [e3; e4] in
  let r4 = [e4] in
  PWReplay.lemma_conn_events_sent_seal_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m0 e0 ds1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_sent_seal_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 r4 ts4 tr4 p
        with
        (
          PWReplay.lemma_conn_events_sent_seal_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m4 e4 ds5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_sent_seal_replay m5 [] ts5 tr5 p
          with ()
        )
      )
    )
  )
#pop-options

#restart-solver
let is_key_install_ev (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> true
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> true
  | _ -> false

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_install_step_preserves_transcript
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires is_key_install_ev ev /\ CS.step_model m ev == Some m1)
      (ensures m1.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
               m1.CS.model_handshake.CS.hs_server_hello == m.CS.model_handshake.CS.hs_server_hello)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_install_step_preserves_protected_buffer_empty
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        is_key_install_ev ev /\
        CS.protected_handshake_buffer_empty m /\
        CS.step_model m ev == Some m1)
      (ensures CS.protected_handshake_buffer_empty m1)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_region_preserves_transcript_sent
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        L.for_all is_key_install_ev evs /\
        SMReplay.conn_events_sent_seal_replay m evs rs rr final)
      (ensures final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
               final.CS.model_handshake.CS.hs_server_hello == m.CS.model_handshake.CS.hs_server_hello)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev ds dr /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev ds /\
      Seq.equal rs (B.append ds ts) /\ Seq.equal rr (B.append dr tr) /\
      SMReplay.conn_events_sent_seal_replay model1 rest ts tr final
    with
    (
      lemma_install_step_preserves_transcript m ev model1;
      lemma_region_preserves_transcript_sent model1 rest ts tr final
    )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_region_preserves_transcript_received
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        L.for_all is_key_install_ev evs /\
        SMReplay.conn_events_received_decode_replay m evs rs rr final)
      (ensures final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
               final.CS.model_handshake.CS.hs_server_hello == m.CS.model_handshake.CS.hs_server_hello)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev ds dr /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev dr /\
      Seq.equal rs (B.append ds ts) /\ Seq.equal rr (B.append dr tr) /\
      SMReplay.conn_events_received_decode_replay model1 rest ts tr final
    with
    (
      lemma_install_step_preserves_transcript m ev model1;
      lemma_region_preserves_transcript_received model1 rest ts tr final
    )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_region_preserves_protected_buffer_empty_received
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        L.for_all is_key_install_ev evs /\
        CS.protected_handshake_buffer_empty m /\
        SMReplay.conn_events_received_decode_replay m evs rs rr final)
      (ensures CS.protected_handshake_buffer_empty final)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev ds dr /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev dr /\
      Seq.equal rs (B.append ds ts) /\ Seq.equal rr (B.append dr tr) /\
      SMReplay.conn_events_received_decode_replay model1 rest ts tr final
    with
    (
      lemma_install_step_preserves_protected_buffer_empty m ev model1;
      lemma_region_preserves_protected_buffer_empty_received model1 rest ts tr final
    )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_client_prefix_model
  (cfg:CS.connection_config)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model cfg)
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
          ps pr p)
      (ensures
        p.CS.model_config == cfg /\
        p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
        p.CS.model_handshake.CS.hs_server_hello == Some sh /\
        p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh /\
        CS.protected_handshake_buffer_empty p)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  let r1 = [e1; e2; e3] in
  let r2 = [e2; e3] in
  let r3 = [e3] in
  PWReplay.lemma_conn_events_received_decode_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m0 e0 dr1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_received_decode_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 [] ts4 tr4 p
        with ()
      )
    )
  )
#pop-options

(* ================= inlined from Scratch_PrefixBytes ================= *)


(* ------------------------------------------------------------------ *)
(* Bound-extraction helpers from event legality.                       *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_sent_sh_bound (m:CS.connection_model) (sh:GSH.serverHello)
  : Lemma
      (requires
        CS.legal_event m
          (CS.ConnNetworkEvent { CL.message_direction = CL.Sent;
                                 CL.message_value = M.TlsHandshake (M.ServerHello sh) }))
      (ensures B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_recv_sh_bound (m:CS.connection_model) (sh:GSH.serverHello)
  : Lemma
      (requires
        CS.legal_event m
          (CS.ConnNetworkEvent { CL.message_direction = CL.Received;
                                 CL.message_value = M.TlsHandshake (M.ServerHello sh) }))
      (ensures B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 4 --z3rlimit 40"
let lemma_sent_ch_bound (m:CS.connection_model) (ch:GCH.clientHello)
  : Lemma
      (requires
        CS.legal_event m
          (CS.ConnNetworkEvent { CL.message_direction = CL.Sent;
                                 CL.message_value = M.TlsHandshake (M.ClientHello ch) }))
      (ensures B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640)
= ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Append/empty helpers.                                               *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let app_empty_r (a b:B.bytes)
  : Lemma (requires Seq.equal b B.empty) (ensures Seq.equal (B.append a b) a)
= ()

let app_empty_l (a b:B.bytes)
  : Lemma (requires Seq.equal a B.empty) (ensures Seq.equal (B.append a b) b)
= ()
#pop-options

(* ------------------------------------------------------------------ *)
(* H1: server prefix SENT bytes = serialize_record(H, SH).             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80"
let lemma_server_prefix_sent_bytes
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ServerEndpoint /\
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model cfg)
          (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
          ps pr p)
      (ensures
        Seq.equal ps
          (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) /\
        B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let r1 = [e1; e2; e3; e4] in
  let r2 = [e2; e3; e4] in
  let r3 = [e3; e4] in
  let r4 = [e4] in
  let goal = Seq.equal ps
               (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) /\
             B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640 in
  PWReplay.lemma_conn_events_sent_seal_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m0 e0 ds1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_sent_seal_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 r4 ts4 tr4 p
        with
        (
          PWReplay.lemma_conn_events_sent_seal_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m4 e4 ds5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_sent_seal_replay m5 [] ts5 tr5 p
          with
          (
            W.lemma_serialize_tls_message_handshake (M.ServerHello sh);
            lemma_sent_sh_bound m4 sh;
            let recsh = W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh)) in
            assert (Seq.equal ds5 recsh);
            app_empty_r ds5 ts5;
            assert (Seq.equal ts4 recsh);
            app_empty_l ds4 ts4;
            assert (Seq.equal ts3 ts4);
            app_empty_l ds3 ts3;
            assert (Seq.equal ts2 ts3);
            app_empty_l ds2 ts2;
            assert (Seq.equal ts1 ts2);
            app_empty_l ds1 ts1;
            assert (Seq.equal ps ts1);
            assert (Seq.equal ps recsh)
          )
        )
      )
    )
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* H1: server prefix RECEIVED bytes = parse-form ClientHello.          *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
let lemma_server_prefix_received_bytes
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ServerEndpoint /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model cfg)
          (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
          ps pr p)
      (ensures
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) pr)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let r1 = [e1; e2; e3; e4] in
  let r2 = [e2; e3; e4] in
  let r3 = [e3; e4] in
  let r4 = [e4] in
  let goal = CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) pr in
  PWReplay.lemma_conn_events_received_decode_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m0 e0 dr1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_received_decode_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 r4 ts4 tr4 p
        with
        (
          PWReplay.lemma_conn_events_received_decode_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m4 e4 dr5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_received_decode_replay m5 [] ts5 tr5 p
          with
          (
            app_empty_l dr5 tr5;    (* tr4 == tr5 == empty *)
            app_empty_l dr4 tr4;    (* tr3 == tr4 == empty *)
            app_empty_l dr3 tr3;    (* tr2 == tr3 == empty *)
            app_empty_r dr2 tr2;    (* tr1 == dr2 *)
            app_empty_l dr1 tr1;    (* pr == tr1 == dr2 *)
            Seq.lemma_eq_elim pr dr2
          )
        )
      )
    )
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* H1: client prefix SENT bytes = serialize_record(H, CH).             *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
let lemma_client_prefix_sent_bytes
  (cfg:CS.connection_config)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model cfg)
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
          ps pr p)
      (ensures
        Seq.equal ps
          (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) /\
        B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  let r1 = [e1; e2; e3] in
  let r2 = [e2; e3] in
  let r3 = [e3] in
  let goal = Seq.equal ps
               (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) /\
             B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640 in
  PWReplay.lemma_conn_events_sent_seal_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m0 e0 ds1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_sent_seal_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 [] ts4 tr4 p
        with
        (
          W.lemma_serialize_tls_message_handshake (M.ClientHello ch);
          lemma_sent_ch_bound m1 ch;
          let recch = W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch)) in
          assert (Seq.equal ds2 recch);
          app_empty_l ds4 ts4;    (* ts3 == ts4 *)
          app_empty_l ds3 ts3;    (* ts2 == ts3 == ts4 *)
          app_empty_r ds2 ts2;    (* ts1 == ds2 == recch  (ds3 branch: ts2 empty) *)
          app_empty_l ds1 ts1;    (* ps == ts1 *)
          assert (Seq.equal ts4 B.empty);
          assert (Seq.equal ts2 B.empty);
          assert (Seq.equal ts1 recch);
          assert (Seq.equal ps recch)
        )
      )
    )
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* H1: client prefix RECEIVED bytes = serialize_record(H, SH).         *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
let lemma_client_prefix_received_bytes
  (cfg:CS.connection_config)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (ps pr:B.bytes) (p:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model cfg)
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
          ps pr p)
      (ensures
        Seq.equal pr
          (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) /\
        B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640)
=
  let m0 = CS.initial_model cfg in
  let e0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                                  CL.message_value = M.TlsHandshake (M.ClientHello ch) }) in
  let e2 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                                  CL.message_value = M.TlsHandshake (M.ServerHello sh) }) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  let r1 = [e1; e2; e3] in
  let r2 = [e2; e3] in
  let r3 = [e3] in
  let goal = Seq.equal pr
               (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) /\
             B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640 in
  PWReplay.lemma_conn_events_received_decode_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m0 e0 dr1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_received_decode_replay m1 r1 ts1 tr1 p
  with
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    with
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      with
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 [] ts4 tr4 p
        with
        (
          W.lemma_serialize_tls_message_handshake (M.ServerHello sh);
          lemma_recv_sh_bound m2 sh;
          let recsh = W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh)) in
          assert (Seq.equal dr3 recsh);
          app_empty_l dr4 tr4;    (* tr3 == tr4 *)
          app_empty_r dr3 tr3;    (* tr2 == dr3 == recsh  (tr3 empty) *)
          app_empty_l dr2 tr2;    (* tr1 == tr2 == recsh *)
          app_empty_l dr1 tr1;    (* pr == tr1 == recsh *)
          assert (Seq.equal tr4 B.empty);
          assert (Seq.equal tr3 B.empty);
          assert (Seq.equal tr2 recsh);
          assert (Seq.equal pr recsh)
        )
      )
    )
  )
#pop-options

(* ================= inlined from Scratch_SrvFlight ================= *)



(* ------------------------------------------------------------------ *)
(* Pointwise: a server-hs-install event is byte-neutral on the sent    *)
(* stream and is a key-install event.                                  *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
#restart-solver
let lemma_install_empty_sent (e:CS.conn_event)
  : Lemma (requires SCShape.is_server_hs_install e == true)
          (ensures Region.is_empty_sent_ev e == true)
  = ()

let lemma_install_key (e:CS.conn_event)
  : Lemma (requires SCShape.is_server_hs_install e == true)
          (ensures is_key_install_ev e == true)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_forall_install_empty_sent (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true))
      (ensures L.for_all Region.is_empty_sent_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> Region.is_empty_sent_ev x == true
    with (introduce L.memP x region ==> Region.is_empty_sent_ev x == true
          with lemma_install_empty_sent x);
    L.for_all_mem Region.is_empty_sent_ev region

let lemma_forall_install_key (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true))
      (ensures L.for_all is_key_install_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> is_key_install_ev x == true
    with (introduce L.memP x region ==> is_key_install_ev x == true
          with lemma_install_key x);
    L.for_all_mem is_key_install_ev region
#pop-options

(* ------------------------------------------------------------------ *)
(* The server flight event list (post-region).                        *)
(* ------------------------------------------------------------------ *)

let sent_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                         CL.message_value = M.TlsHandshake msg })

let server_flight_events
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
  (tail:list CS.conn_event) : list CS.conn_event =
  sent_ev (M.EncryptedExtensions ee) ::
  sent_ev (M.Certificate cert) ::
  CS.ConnLocalEvent cv_local ::
  sent_ev (M.CertificateVerify cv) ::
  sent_ev (M.Finished sf) ::
  tail

(* The producer-shaped result predicate for the server side. *)
let server_flight_result
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (sh:GSH.serverHello)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
  (tail:list CS.conn_event)
  (ss:B.bytes) (final:CS.connection_model)
  (mid:CS.connection_model) (material:CS.traffic_key_material)
  (fl_sent fl_recv:B.bytes) : prop =
  SMReplay.conn_events_sent_seal_replay
    mid
    (RI.server_hs_write_install_event material ::
     server_flight_events ee cert cv_local cv sf tail)
    fl_sent fl_recv final /\
  Some? mid.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  mid.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  mid.CS.model_handshake.CS.hs_server_hello == Some sh /\
  mid.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh /\
  Seq.equal ss (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) fl_sent) /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640

(* ------------------------------------------------------------------ *)
(* Server flight helper.                                              *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_server_flight
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
  (region:list CS.conn_event) (tail:list CS.conn_event)
  (ss sr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ServerEndpoint /\
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        (exists (ew:CS.conn_event). L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew) /\
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model cfg)
          (L.append (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
                    (L.append region (server_flight_events ee cert cv_local cv sf tail)))
          ss sr final)
      (ensures
        (exists (mid:CS.connection_model) (material:CS.traffic_key_material)
           (fl_sent fl_recv:B.bytes).
           server_flight_result cfg ch sh ee cert cv_local cv sf tail ss final
             mid material fl_sent fl_recv))
  =
  let prefix = PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh in
  let sflight = server_flight_events ee cert cv_local cv sf tail in
  let m0 = CS.initial_model cfg in
  let goal =
    (exists (mid:CS.connection_model) (material:CS.traffic_key_material)
       (fl_sent fl_recv:B.bytes).
       server_flight_result cfg ch sh ee cert cv_local cv sf tail ss final
         mid material fl_sent fl_recv) in
  PWReplay.lemma_conn_events_sent_seal_replay_append_split
    m0 prefix (L.append region sflight) ss sr final;
  eliminate exists (ps:CS.connection_model)
                   (ps_sent ps_recv suf_sent suf_recv:B.bytes).
    Seq.equal ss (B.append ps_sent suf_sent) /\
    Seq.equal sr (B.append ps_recv suf_recv) /\
    SMReplay.conn_events_sent_seal_replay m0 prefix ps_sent ps_recv ps /\
    SMReplay.conn_events_sent_seal_replay ps (L.append region sflight) suf_sent suf_recv final
  with
  (
    lemma_server_prefix_model cfg ch selection server_shared sh ps_sent ps_recv ps;
    lemma_server_prefix_sent_bytes cfg ch selection server_shared sh ps_sent ps_recv ps;
    // ps: control HsServerHelloSent, ks_shared_secret Some server_shared,
    //     transcript = server_prefix_transcript ch sh
    // ps_sent == serialize_record H (ser SH)
    PWReplay.lemma_conn_events_sent_seal_replay_append_split
      ps region sflight suf_sent suf_recv final;
    eliminate exists (ms:CS.connection_model)
                     (rg_sent rg_recv fl_sent fl_recv:B.bytes).
      Seq.equal suf_sent (B.append rg_sent fl_sent) /\
      Seq.equal suf_recv (B.append rg_recv fl_recv) /\
      SMReplay.conn_events_sent_seal_replay ps region rg_sent rg_recv ms /\
      SMReplay.conn_events_sent_seal_replay ms sflight fl_sent fl_recv final
    with
    (
      lemma_forall_install_empty_sent region;
      Region.lemma_empty_sent_tail_collapses ps region rg_sent rg_recv ms;
      // rg_sent == empty
      lemma_server_region_write_installed ps region rg_sent rg_recv ms;
      eliminate exists (material:CS.traffic_key_material). server_write_installed ms material
      with
      (
        // secrets
        lemma_sent_replay_preserves_secrets ps region rg_sent rg_recv ms;
        lemma_sent_replay_preserves_secrets ms sflight fl_sent fl_recv final;
        // transcript preservation
        lemma_forall_install_key region;
        lemma_region_preserves_transcript_sent ps region rg_sent rg_recv ms;
        // RI prepend  (server_write_installed ms material == server_redundant_write_install_ok ms material)
        RI.lemma_prepend_redundant_server_hs_write_install_sent ms material sflight fl_sent fl_recv final;
        // byte accounting: ss == record(SH) ++ fl_sent
        Seq.lemma_eq_elim rg_sent B.empty;
        Seq.append_empty_l fl_sent;
        Seq.lemma_eq_elim suf_sent fl_sent;
        Seq.lemma_eq_elim ps_sent
          (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh)));
        Seq.lemma_eq_elim ss (B.append ps_sent suf_sent);
        introduce exists (mid:CS.connection_model) (material2:CS.traffic_key_material)
                    (a b:B.bytes).
           server_flight_result cfg ch sh ee cert cv_local cv sf tail ss final
             mid material2 a b
        with ms material fl_sent fl_recv
        and ()
      )
    )
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* Server received-CH helper (for the CH-direction agreement).        *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_server_received_ch
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (suffix:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ServerEndpoint /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model cfg)
          (L.append (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
                    suffix)
          rs rr final)
      (ensures
        (exists (d_ch rest:B.bytes).
          CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) d_ch /\
          Seq.equal rr (B.append d_ch rest)))
  =
  let prefix = PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh in
  let m0 = CS.initial_model cfg in
  let goal =
    (exists (d_ch rest:B.bytes).
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) d_ch /\
      Seq.equal rr (B.append d_ch rest)) in
  PWReplay.lemma_conn_events_received_decode_replay_append_split
    m0 prefix suffix rs rr final;
  eliminate exists (ps:CS.connection_model)
                   (ps_sent ps_recv suf_sent suf_recv:B.bytes).
    Seq.equal rs (B.append ps_sent suf_sent) /\
    Seq.equal rr (B.append ps_recv suf_recv) /\
    SMReplay.conn_events_received_decode_replay m0 prefix ps_sent ps_recv ps /\
    SMReplay.conn_events_received_decode_replay ps suffix suf_sent suf_recv final
  with
  (
    lemma_server_prefix_received_bytes cfg ch selection server_shared sh ps_sent ps_recv ps;
    introduce exists (d_ch rest:B.bytes).
       CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) d_ch /\
       Seq.equal rr (B.append d_ch rest)
    with ps_recv suf_recv
    and ()
  )
#pop-options

(* ================= inlined from Scratch_CltFlight ================= *)



(* ------------------------------------------------------------------ *)
(* Pointwise: a client-hs-install event is byte-neutral on the        *)
(* received stream and is a key-install event.                        *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_install_empty_recv (e:CS.conn_event)
  : Lemma (requires CCShape.is_client_hs_install e == true)
          (ensures Region.is_empty_recv_ev e == true)
  = ()

let lemma_install_key_c (e:CS.conn_event)
  : Lemma (requires CCShape.is_client_hs_install e == true)
          (ensures is_key_install_ev e == true)
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_forall_install_empty_recv (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true))
      (ensures L.for_all Region.is_empty_recv_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> Region.is_empty_recv_ev x == true
    with (introduce L.memP x region ==> Region.is_empty_recv_ev x == true
          with lemma_install_empty_recv x);
    L.for_all_mem Region.is_empty_recv_ev region

let lemma_forall_install_key_c (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true))
      (ensures L.for_all is_key_install_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> is_key_install_ev x == true
    with (introduce L.memP x region ==> is_key_install_ev x == true
          with lemma_install_key_c x);
    L.for_all_mem is_key_install_ev region
#pop-options

(* ------------------------------------------------------------------ *)
(* The client (received) flight event list (post-region).             *)
(* ------------------------------------------------------------------ *)

let recv_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                         CL.message_value = M.TlsHandshake msg })

let client_flight_events
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event) (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event) (sf:GFin.finished)
  (tail:list CS.conn_event) : list CS.conn_event =
  recv_ev (M.EncryptedExtensions ee) ::
  recv_ev (M.Certificate cert) ::
  CS.ConnLocalEvent cv_validate ::
  recv_ev (M.CertificateVerify cv) ::
  CS.ConnLocalEvent cv_verify ::
  recv_ev (M.Finished sf) ::
  tail

let client_flight_result
  (cfg:CS.connection_config)
  (ch:GCH.clientHello) (sh:GSH.serverHello)
  (raw_flight:list CS.conn_event)
  (cr:B.bytes) (final:CS.connection_model)
  (mid:CS.connection_model) (material:CS.traffic_key_material)
  (fl_sent fl_recv:B.bytes) : prop =
  SMReplay.conn_events_received_decode_replay
    mid
    (RI.client_hs_read_install_event material ::
     raw_flight)
    fl_sent fl_recv final /\
  Some? mid.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  CS.protected_handshake_buffer_empty mid /\
  mid.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  mid.CS.model_handshake.CS.hs_server_hello == Some sh /\
  mid.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh /\
  Seq.equal cr (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) fl_recv) /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640

(* ------------------------------------------------------------------ *)
(* Client flight helper.                                              *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let lemma_client_flight
  (cfg:CS.connection_config)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (region raw_flight:list CS.conn_event)
  (cs cr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        (exists (er:CS.conn_event). L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model cfg)
          (L.append (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
                    (L.append region raw_flight))
          cs cr final)
      (ensures
        (exists (mid:CS.connection_model) (material:CS.traffic_key_material)
           (fl_sent fl_recv:B.bytes).
           client_flight_result cfg ch sh raw_flight cr final
             mid material fl_sent fl_recv))
  =
  let prefix = PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared in
  let cflight = raw_flight in
  let m0 = CS.initial_model cfg in
  let goal =
    (exists (mid:CS.connection_model) (material:CS.traffic_key_material)
       (fl_sent fl_recv:B.bytes).
       client_flight_result cfg ch sh raw_flight cr final
         mid material fl_sent fl_recv) in
  PWReplay.lemma_conn_events_received_decode_replay_append_split
    m0 prefix (L.append region cflight) cs cr final;
  eliminate exists (ps:CS.connection_model)
                   (ps_sent ps_recv suf_sent suf_recv:B.bytes).
    Seq.equal cs (B.append ps_sent suf_sent) /\
    Seq.equal cr (B.append ps_recv suf_recv) /\
    SMReplay.conn_events_received_decode_replay m0 prefix ps_sent ps_recv ps /\
    SMReplay.conn_events_received_decode_replay ps (L.append region cflight) suf_sent suf_recv final
  with
  (
    lemma_client_prefix_model cfg start ch sh client_shared ps_sent ps_recv ps;
    lemma_client_prefix_received_bytes cfg start ch sh client_shared ps_sent ps_recv ps;
    // ps: control HsServerHelloReceived, ks_shared_secret Some client_shared,
    //     transcript = server_prefix_transcript ch sh; ps_recv == record(SH)
    PWReplay.lemma_conn_events_received_decode_replay_append_split
      ps region cflight suf_sent suf_recv final;
    eliminate exists (ms:CS.connection_model)
                     (rg_sent rg_recv fl_sent fl_recv:B.bytes).
      Seq.equal suf_sent (B.append rg_sent fl_sent) /\
      Seq.equal suf_recv (B.append rg_recv fl_recv) /\
      SMReplay.conn_events_received_decode_replay ps region rg_sent rg_recv ms /\
      SMReplay.conn_events_received_decode_replay ms cflight fl_sent fl_recv final
    with
    (
      lemma_forall_install_empty_recv region;
      Region.lemma_empty_recv_tail_collapses ps region rg_sent rg_recv ms;
      // rg_recv == empty
      CReg.lemma_client_region_read_installed ps region rg_sent rg_recv ms;
      eliminate exists (material:CS.traffic_key_material). CReg.client_read_installed ms material
      with
      (
        lemma_received_replay_preserves_secrets ps region rg_sent rg_recv ms;
        lemma_received_replay_preserves_secrets ms cflight fl_sent fl_recv final;
        lemma_forall_install_key_c region;
        lemma_region_preserves_transcript_received ps region rg_sent rg_recv ms;
        lemma_region_preserves_protected_buffer_empty_received
          ps region rg_sent rg_recv ms;
        RI.lemma_prepend_redundant_client_hs_read_install_received ms material cflight fl_sent fl_recv final;
        // byte accounting: cr == record(SH) ++ fl_recv
        Seq.lemma_eq_elim rg_recv B.empty;
        Seq.append_empty_l fl_recv;
        Seq.lemma_eq_elim suf_recv fl_recv;
        Seq.lemma_eq_elim ps_recv
          (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh)));
        Seq.lemma_eq_elim cr (B.append ps_recv suf_recv);
        introduce exists (mid:CS.connection_model) (material2:CS.traffic_key_material)
                    (a b:B.bytes).
           client_flight_result cfg ch sh raw_flight cr final
             mid material2 a b
        with ms material fl_sent fl_recv
        and ()
      )
    )
  )
#pop-options

(* ------------------------------------------------------------------ *)
(* Client sent-CH helper (for the CH-direction agreement).            *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_client_sent_ch
  (cfg:CS.connection_config)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (suffix:list CS.conn_event)
  (cs cr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        cfg.CS.config_role == CS.ClientEndpoint /\
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model cfg)
          (L.append (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
                    suffix)
          cs cr final)
      (ensures
        (exists (rest:B.bytes).
          Seq.equal cs
            (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) rest) /\
          B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640))
  =
  let prefix = PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared in
  let m0 = CS.initial_model cfg in
  let goal =
    (exists (rest:B.bytes).
      Seq.equal cs
        (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) rest) /\
      B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640) in
  PWReplay.lemma_conn_events_sent_seal_replay_append_split
    m0 prefix suffix cs cr final;
  eliminate exists (ps:CS.connection_model)
                   (ps_sent ps_recv suf_sent suf_recv:B.bytes).
    Seq.equal cs (B.append ps_sent suf_sent) /\
    Seq.equal cr (B.append ps_recv suf_recv) /\
    SMReplay.conn_events_sent_seal_replay m0 prefix ps_sent ps_recv ps /\
    SMReplay.conn_events_sent_seal_replay ps suffix suf_sent suf_recv final
  with
  (
    lemma_client_prefix_sent_bytes cfg start ch sh client_shared ps_sent ps_recv ps;
    // ps_sent == record(CH)
    Seq.lemma_eq_elim ps_sent
      (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch)));
    Seq.lemma_eq_elim cs (B.append ps_sent suf_sent);
    introduce exists (rest:B.bytes).
       Seq.equal cs
         (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) rest) /\
       B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640
    with suf_sent
    and ()
  )
#pop-options

(* ================= inlined from Scratch_OneProjPair ================= *)






(* ================================================================== *)
(* Small unfolding helpers.                                           *)
(* ================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_server_replays (s:sysp)
  : Lemma (requires SD.server_driver_application_ready s.server)
          (ensures
            SMReplay.connection_state_sent_seal_replay_consistent s.server /\
            SMReplay.connection_state_received_decode_replay_consistent s.server)
  = ()

let lemma_client_replays (s:sysp)
  : Lemma (requires CD.client_driver_application_ready s.client)
          (ensures
            SMReplay.connection_state_sent_seal_replay_consistent s.client /\
            SMReplay.connection_state_received_decode_replay_consistent s.client)
  = ()

let lemma_appdata_server (st:CS.connection_state)
  : Lemma (requires SD.server_driver_application_ready st)
          (ensures st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
  = ()

let lemma_appdata_client (st:CS.connection_state)
  : Lemma (requires CD.client_driver_application_ready st)
          (ensures st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_byte_pairing_quiet (s:sysp)
  : Lemma (requires
            Seq.equal s.client.CS.cs_wire_log.CL.raw_sent
                      s.server.CS.cs_wire_log.CL.raw_received /\
            Seq.equal s.server.CS.cs_wire_log.CL.raw_sent
                      s.client.CS.cs_wire_log.CL.raw_received)
          (ensures
            Seq.equal s.client.CS.cs_wire_log.CL.raw_sent
                      s.server.CS.cs_wire_log.CL.raw_received /\
            Seq.equal s.server.CS.cs_wire_log.CL.raw_sent
                      s.client.CS.cs_wire_log.CL.raw_received)
  = ()
#pop-options

(* ================================================================== *)
(* Server-side package.                                                *)
(* ================================================================== *)

let server_side_package (s:sysp)
  (ms:CS.connection_model) (material_s:CS.traffic_key_material)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (d_ch_s rest_sr:B.bytes) : prop =
  SMReplay.conn_events_sent_seal_replay
    ms
    (RI.server_hs_write_install_event material_s ::
     server_flight_events ee_s cert_s cv_local_s cv_s sf_s tail_s)
    fl_sent_s fl_recv_s s.server.CS.cs_model /\
  Some? ms.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  ms.CS.model_handshake.CS.hs_server_hello == Some sh_s /\
  ms.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch_s sh_s /\
  Seq.equal s.server.CS.cs_wire_log.CL.raw_sent
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh_s))) fl_sent_s) /\
  B.length (W.serialize_handshake (M.ServerHello sh_s)) <= 16640 /\
  CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch_s)) d_ch_s /\
  Seq.equal s.server.CS.cs_wire_log.CL.raw_received (B.append d_ch_s rest_sr)

let server_side_exists (s:sysp) : prop =
  exists (ms:CS.connection_model) (material_s:CS.traffic_key_material)
    (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
    (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
    (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
    (d_ch_s rest_sr:B.bytes).
    server_side_package s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
      fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_server_side (s:sysp)
  : Lemma (requires server_flight_bridge_inputs s.client s.server)
          (ensures server_side_exists s)
  =
  let cfg_s = s.server.CS.cs_model.CS.model_config in
  let ss = s.server.CS.cs_wire_log.CL.raw_sent in
  let sr = s.server.CS.cs_wire_log.CL.raw_received in
  let final = s.server.CS.cs_model in
  lemma_server_replays s;
  SNoCcs.lemma_no_received_ccs_from_pairing s.client s.server;
  lemma_appdata_server s.server;
  assert (WStep.server_reachable (CS.initial cfg_s) s.server);
  assert (cfg_s.CS.config_role == CS.ServerEndpoint);
  assert (SCShape.log_has_no_received_ccs s.server.CS.cs_event_log);
  SCShape.lemma_server_canonical_appdata_exact_spine cfg_s s.server;
  eliminate exists (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
                   (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
                   (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                   (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
                   (region:list CS.conn_event) (tail:list CS.conn_event).
    (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
    (exists (ew:CS.conn_event). L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew) /\
    (exists (er:CS.conn_event). L.memP er region /\ SCShape.is_server_hs_install_dir CS.TrafficRead er) /\
    s.server.CS.cs_event_log ==
      L.append
        (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
        (L.append region
           (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
            CS.ConnLocalEvent cv_local ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
            tail))
  with
  (
    let prefix = PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh in
    let sflight = server_flight_events ee cert cv_local cv sf tail in
    let suffix = L.append region sflight in
    assert (s.server.CS.cs_event_log == L.append prefix suffix);
    lemma_server_flight cfg_s ch selection server_shared sh ee cert cv_local cv sf
      region tail ss sr final;
    eliminate exists (ms:CS.connection_model) (material:CS.traffic_key_material)
                     (fl_sent fl_recv:B.bytes).
      server_flight_result cfg_s ch sh ee cert cv_local cv sf tail ss final
        ms material fl_sent fl_recv
    with
    (
      lemma_server_received_ch cfg_s ch selection server_shared sh suffix ss sr final;
      eliminate exists (d_ch rest:B.bytes).
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) d_ch /\
        Seq.equal sr (B.append d_ch rest)
      with
      (
        introduce exists (ms0:CS.connection_model) (material_s:CS.traffic_key_material)
          (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
          (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
          (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
          (d_ch_s rest_sr:B.bytes).
          server_side_package s ms0 material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
            fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr
        with ms material ee cert cv_local cv sf tail fl_sent fl_recv ch sh d_ch rest
        and ()
      )
    )
  )
#pop-options

(* ================================================================== *)
(* Client-side package.                                                *)
(* ================================================================== *)

#restart-solver
let client_raw_prefix_package
  (s:sysp) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (raw_flight:list CS.conn_event) : prop =
  exists (start:CS.handshake_start)
         (client_shared:C.x25519_shared_secret)
         (region:list CS.conn_event).
    (forall (e:CS.conn_event).
      L.memP e region ==> CCShape.is_client_hs_install e == true) /\
    (exists (er:CS.conn_event).
      L.memP er region /\
      CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
    (exists (ew:CS.conn_event).
      L.memP ew region /\
      CCShape.is_client_hs_install_dir CS.TrafficWrite ew) /\
    s.client.CS.cs_event_log ==
      L.append
        (PWSeg.client_cleartext_handshake_prefix_events
          start ch sh client_shared)
        (L.append region raw_flight)

let client_side_package (s:sysp)
  (mc:CS.connection_model) (material_c:CS.traffic_key_material)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate_c:CS.local_event)
  (cv_c:GCV.certificateVerify) (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
  (tail_c raw_flight_c:list CS.conn_event)
  (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (rest_cs:B.bytes) : prop =
  SMReplay.conn_events_received_decode_replay
    mc
    (RI.client_hs_read_install_event material_c ::
     raw_flight_c)
    fl_sent_c fl_recv_c s.client.CS.cs_model /\
  CCShape.raw_flight_spine
    raw_flight_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c tail_c /\
  client_raw_prefix_package s ch_c sh_c raw_flight_c /\
  Some? mc.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  CS.protected_handshake_buffer_empty mc /\
  mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  mc.CS.model_handshake.CS.hs_server_hello == Some sh_c /\
  mc.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch_c sh_c /\
  Seq.equal s.client.CS.cs_wire_log.CL.raw_received
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh_c))) fl_recv_c) /\
  B.length (W.serialize_handshake (M.ServerHello sh_c)) <= 16640 /\
  Seq.equal s.client.CS.cs_wire_log.CL.raw_sent
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch_c))) rest_cs) /\
  B.length (W.serialize_handshake (M.ClientHello ch_c)) <= 16640

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_client_side_package_has_raw_prefix
  (s:sysp)
  (mc:CS.connection_model) (material_c:CS.traffic_key_material)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate)
  (cv_validate_c:CS.local_event) (cv_c:GCV.certificateVerify)
  (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
  (tail_c raw_flight_c:list CS.conn_event)
  (fl_sent_c fl_recv_c:B.bytes)
  (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (rest_cs:B.bytes)
  : Lemma
      (requires
        client_side_package s mc material_c ee_c cert_c cv_validate_c
          cv_c cv_verify_c sf_c tail_c raw_flight_c fl_sent_c fl_recv_c
          ch_c sh_c rest_cs)
      (ensures client_raw_prefix_package s ch_c sh_c raw_flight_c)
  = ()
#pop-options

let client_side_exists (s:sysp) : prop =
  exists (mc:CS.connection_model) (material_c:CS.traffic_key_material)
    (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate_c:CS.local_event)
    (cv_c:GCV.certificateVerify) (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
    (tail_c raw_flight_c:list CS.conn_event)
    (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
    (rest_cs:B.bytes).
    client_side_package s mc material_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
      tail_c raw_flight_c
      fl_sent_c fl_recv_c ch_c sh_c rest_cs

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_client_side (s:sysp)
  : Lemma (requires server_flight_bridge_inputs s.client s.server)
          (ensures client_side_exists s)
  =
  let cfg_c = s.client.CS.cs_model.CS.model_config in
  let cs = s.client.CS.cs_wire_log.CL.raw_sent in
  let cr = s.client.CS.cs_wire_log.CL.raw_received in
  let final = s.client.CS.cs_model in
  lemma_client_replays s;
  CNoCcs.lemma_no_received_ccs_from_pairing_client s.client s.server;
  lemma_appdata_client s.client;
  assert (WStep.client_reachable (CS.initial cfg_c) s.client);
  assert (cfg_c.CS.config_role == CS.ClientEndpoint);
  assert (CCShape.log_has_no_received_ccs s.client.CS.cs_event_log);
  CCShape.lemma_client_canonical_appdata_exact_spine cfg_c s.client;
  eliminate exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
                   (client_shared:C.x25519_shared_secret)
                   (region:list CS.conn_event)
                   (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                   (cv_validate:CS.local_event) (cv:GCV.certificateVerify)
                   (cv_verify:CS.local_event) (sf:GFin.finished)
                   (tail:list CS.conn_event).
    (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
    (exists (er:CS.conn_event). L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
    (exists (ew:CS.conn_event). L.memP ew region /\ CCShape.is_client_hs_install_dir CS.TrafficWrite ew) /\
    (exists (raw_suffix:list CS.conn_event).
      s.client.CS.cs_event_log ==
        L.append
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
          (L.append region raw_suffix)) /\
    CCShape.canonical_log s.client.CS.cs_event_log ==
      L.append
        (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
        (L.append region
           (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
            CS.ConnLocalEvent cv_validate ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
            CS.ConnLocalEvent cv_verify ::
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
            tail))
  with
  (
    eliminate exists (raw_suffix:list CS.conn_event).
      s.client.CS.cs_event_log ==
        L.append
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
          (L.append region raw_suffix)
    with
    (
      CCShape.lemma_client_raw_suffix_flight_spine
        start ch sh client_shared region raw_suffix s.client.CS.cs_event_log
        ee cert cv_validate cv cv_verify sf tail;
      let prefix = PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared in
      let suffix = L.append region raw_suffix in
      lemma_client_flight cfg_c start ch sh client_shared
        region raw_suffix cs cr final;
      eliminate exists (mc:CS.connection_model) (material:CS.traffic_key_material)
                       (fl_sent fl_recv:B.bytes).
        client_flight_result cfg_c ch sh raw_suffix cr final
          mc material fl_sent fl_recv
      with
      (
        lemma_client_sent_ch cfg_c start ch sh client_shared suffix cs cr final;
        eliminate exists (rest:B.bytes).
          Seq.equal cs
            (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) rest) /\
          B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640
        with
        (
          introduce exists (mc0:CS.connection_model) (material_c:CS.traffic_key_material)
            (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate_c:CS.local_event)
            (cv_c:GCV.certificateVerify) (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
            (tail_c raw_flight_c:list CS.conn_event)
            (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
            (rest_cs:B.bytes).
            client_side_package s mc0 material_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
              tail_c raw_flight_c fl_sent_c fl_recv_c ch_c sh_c rest_cs
          with mc material ee cert cv_validate cv cv_verify sf tail raw_suffix
               fl_sent fl_recv ch sh rest
          and (assert (CCShape.raw_flight_spine
                         raw_suffix ee cert cv_validate cv cv_verify sf tail);
               assert (client_raw_prefix_package s ch sh raw_suffix);
               assert (SMReplay.conn_events_received_decode_replay mc
                         (RI.client_hs_read_install_event material :: raw_suffix)
                         fl_sent fl_recv s.client.CS.cs_model))
        )
      )
    )
  )
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let lemma_replay_cong_sent
  (m:CS.connection_model) (l1 l2:list CS.conn_event) (a b:B.bytes) (f:CS.connection_model)
  : Lemma
      (requires l1 == l2 /\ SMReplay.conn_events_sent_seal_replay m l1 a b f)
      (ensures SMReplay.conn_events_sent_seal_replay m l2 a b f)
  = ()

let lemma_replay_cong_recv
  (m:CS.connection_model) (l1 l2:list CS.conn_event) (a b:B.bytes) (f:CS.connection_model)
  : Lemma
      (requires l1 == l2 /\ SMReplay.conn_events_received_decode_replay m l1 a b f)
      (ensures SMReplay.conn_events_received_decode_replay m l2 a b f)
  = ()
#pop-options

(* Transcript congruence: the prefix transcript depends only on the CH/SH
   serializations, so equal serializations give equal transcripts. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let lemma_transcript_cong
  (ch_s ch_c:GCH.clientHello) (sh_s sh_c:GSH.serverHello)
  : Lemma
      (requires
        Seq.equal (W.serialize_handshake (M.ClientHello ch_c))
                  (W.serialize_handshake (M.ClientHello ch_s)) /\
        Seq.equal (W.serialize_handshake (M.ServerHello sh_s))
                  (W.serialize_handshake (M.ServerHello sh_c)))
      (ensures
        Seq.equal (server_prefix_transcript ch_s sh_s)
                  (server_prefix_transcript ch_c sh_c))
  = Seq.lemma_eq_elim (W.serialize_handshake (M.ClientHello ch_c))
                      (W.serialize_handshake (M.ClientHello ch_s));
    Seq.lemma_eq_elim (W.serialize_handshake (M.ServerHello sh_s))
                      (W.serialize_handshake (M.ServerHello sh_c))
#pop-options

(* Secret-agreement direction swap (Seq.equal is symmetric). *)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 20"
let lemma_secret_swap (a b:option C.secret)
  : Lemma
      (requires (match a, b with Some x, Some y -> Seq.equal y x | _ -> False))
      (ensures  (match a, b with Some x, Some y -> Seq.equal x y | _ -> False))
  = match a, b with
    | Some x, Some y -> Seq.lemma_eq_elim y x; Seq.lemma_eq_intro x y
    | _ -> ()
#pop-options

(* ================= ported stage infrastructure ================= *)

let after_fin_server (m:CS.connection_model) : prop =
  m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent \/
  m.CS.model_control == CS.ControlApplicationData \/
  m.CS.model_control == CS.ControlClosing \/
  m.CS.model_control == CS.ControlClosed \/
  CS.ControlFailed? m.CS.model_control

let server_fields_eq (a b:CS.connection_model) : prop =
  a.CS.model_handshake.CS.hs_encrypted_extensions == b.CS.model_handshake.CS.hs_encrypted_extensions /\
  a.CS.model_handshake.CS.hs_certificate == b.CS.model_handshake.CS.hs_certificate /\
  a.CS.model_handshake.CS.hs_certificate_verify == b.CS.model_handshake.CS.hs_certificate_verify /\
  a.CS.model_handshake.CS.hs_server_finished == b.CS.model_handshake.CS.hs_server_finished

#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_server_field_step (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        after_fin_server m)
      (ensures after_fin_server m1 /\ server_fields_eq m1 m /\
               m1.CS.model_config == m.CS.model_config)
  =
  match ev with
  | CS.ConnLocalEvent local -> ()
  | CS.ConnNetworkEvent msg -> ()
  | CS.ConnProtectedHandshake step -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_sent_replay_preserves_server_fields
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m evs rs rr final /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        after_fin_server m)
      (ensures after_fin_server final /\ server_fields_eq final m)
      (decreases evs)
  =
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    with
    (
      lemma_server_field_step m ev model1;
      lemma_sent_replay_preserves_server_fields model1 rest tail_sent tail_received final
    )
#pop-options

(* ---- client AfterFin control set ---- *)
let after_fin_client (m:CS.connection_model) : prop =
  m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified \/
  m.CS.model_control == CS.ControlApplicationData \/
  m.CS.model_control == CS.ControlClosing \/
  m.CS.model_control == CS.ControlClosed \/
  CS.ControlFailed? m.CS.model_control

#push-options "--fuel 2 --ifuel 3 --z3rlimit 60"
let lemma_client_field_step (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        after_fin_client m)
      (ensures after_fin_client m1 /\ server_fields_eq m1 m /\
               m1.CS.model_config == m.CS.model_config)
  =
  match ev with
  | CS.ConnLocalEvent local -> ()
  | CS.ConnNetworkEvent msg -> ()
  | CS.ConnProtectedHandshake step -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_received_replay_preserves_client_fields
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m evs rs rr final /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        after_fin_client m)
      (ensures after_fin_client final /\ server_fields_eq final m)
      (decreases evs)
  =
  match evs with
  | [] -> ()
  | ev :: rest ->
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    with
    (
      lemma_client_field_step m ev model1;
      lemma_received_replay_preserves_client_fields model1 rest tail_sent tail_received final
    )
#pop-options

(* ---- config preservation over replays ---- *)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_step_preserves_config (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma (requires CS.step_model m ev == Some m1)
          (ensures m1.CS.model_config == m.CS.model_config)
  = match ev with
    | CS.ConnLocalEvent local -> ()
    | CS.ConnNetworkEvent msg -> ()
    | CS.ConnProtectedHandshake step -> ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec lemma_sent_replay_preserves_config
  (m:CS.connection_model) (evs:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma (requires SMReplay.conn_events_sent_seal_replay m evs rs rr final)
          (ensures final.CS.model_config == m.CS.model_config)
          (decreases evs)
  = match evs with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model)
                       (delta_sent delta_received tail_sent tail_received:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev delta_sent delta_received /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
        Seq.equal rs (B.append delta_sent tail_sent) /\
        Seq.equal rr (B.append delta_received tail_received) /\
        SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
      with
      ( lemma_step_preserves_config m ev model1;
        lemma_sent_replay_preserves_config model1 rest tail_sent tail_received final )

let rec lemma_received_replay_preserves_config
  (m:CS.connection_model) (evs:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma (requires SMReplay.conn_events_received_decode_replay m evs rs rr final)
          (ensures final.CS.model_config == m.CS.model_config)
          (decreases evs)
  = match evs with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model)
                       (delta_sent delta_received tail_sent tail_received:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev delta_sent delta_received /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m ev delta_received /\
        Seq.equal rs (B.append delta_sent tail_sent) /\
        Seq.equal rr (B.append delta_received tail_received) /\
        SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
      with
      ( lemma_step_preserves_config m ev model1;
        lemma_received_replay_preserves_config model1 rest tail_sent tail_received final )
#pop-options

(* ---- field-read primitives after a concrete sent step ---- *)


#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_read_ee (m m1:CS.connection_model) (ee:GEE.encryptedExtensions)
  : Lemma (requires CS.legal_event m (sent_ev (M.EncryptedExtensions ee)) /\
                    CS.step_model m (sent_ev (M.EncryptedExtensions ee)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
                   m1.CS.model_record.CS.record_write ==
                     R.next_seq m.CS.model_record.CS.record_write /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
  = ()

let lemma_read_cert (m m1:CS.connection_model) (cert:GCert.certificate)
  : Lemma (requires CS.legal_event m (sent_ev (M.Certificate cert)) /\
                    CS.step_model m (sent_ev (M.Certificate cert)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_certificate == Some cert /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_record.CS.record_write ==
                     R.next_seq m.CS.model_record.CS.record_write /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
  = ()

let lemma_read_cv (m m1:CS.connection_model) (cv:GCV.certificateVerify)
  : Lemma (requires CS.legal_event m (sent_ev (M.CertificateVerify cv)) /\
                    CS.step_model m (sent_ev (M.CertificateVerify cv)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate /\
                   m1.CS.model_record.CS.record_write ==
                     R.next_seq m.CS.model_record.CS.record_write /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
  = ()

let lemma_read_sf (m m1:CS.connection_model) (sf:GFin.finished)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                    CS.legal_event m (sent_ev (M.Finished sf)) /\
                    CS.step_model m (sent_ev (M.Finished sf)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_server_finished == Some sf /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate /\
                   m1.CS.model_handshake.CS.hs_certificate_verify ==
                     m.CS.model_handshake.CS.hs_certificate_verify /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
  = ()

(* local event: no local arm sets hs_ee or hs_cert, so both are preserved generically *)
let lemma_local_pres_server (m m1:CS.connection_model) (local:CS.local_event)
  : Lemma (requires CS.step_model m (CS.ConnLocalEvent local) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate)
  = ()
#pop-options

(* ---- client-side field-read primitives after concrete recv steps ---- *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_read_recv_ee (m m1:CS.connection_model) (ee:GEE.encryptedExtensions)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    CS.legal_event m (recv_ev (M.EncryptedExtensions ee)) /\
                    CS.step_model m (recv_ev (M.EncryptedExtensions ee)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
                   m1.CS.model_record.CS.record_read ==
                     R.next_seq m.CS.model_record.CS.record_read /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)
  = ()

let lemma_read_recv_cert (m m1:CS.connection_model) (cert:GCert.certificate)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    CS.legal_event m (recv_ev (M.Certificate cert)) /\
                    CS.step_model m (recv_ev (M.Certificate cert)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_certificate == Some cert /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_record.CS.record_read ==
                     R.next_seq m.CS.model_record.CS.record_read /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived)
  = ()

let lemma_read_recv_cv (m m1:CS.connection_model) (cv:GCV.certificateVerify)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    CS.legal_event m (recv_ev (M.CertificateVerify cv)) /\
                    CS.step_model m (recv_ev (M.CertificateVerify cv)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate /\
                   m1.CS.model_record.CS.record_read ==
                     R.next_seq m.CS.model_record.CS.record_read /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived)
  = ()

let lemma_read_recv_sf (m m1:CS.connection_model) (sf:GFin.finished)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    CS.legal_event m (recv_ev (M.Finished sf)) /\
                    CS.step_model m (recv_ev (M.Finished sf)) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_server_finished == Some sf /\
                   m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate /\
                   m1.CS.model_handshake.CS.hs_certificate_verify ==
                     m.CS.model_handshake.CS.hs_certificate_verify /\
                   m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified)
  = ()

(* client local event: preserves hs_ee, hs_cert, and hs_cv (LocalVerifyCertificateSignature
   re-sets hs_cv to the stored value; LocalSign is server-only) *)
let lemma_local_pres_client (m m1:CS.connection_model) (local:CS.local_event)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    CS.legal_event m (CS.ConnLocalEvent local) /\
                    CS.step_model m (CS.ConnLocalEvent local) == Some m1)
          (ensures m1.CS.model_handshake.CS.hs_encrypted_extensions ==
                     m.CS.model_handshake.CS.hs_encrypted_extensions /\
                   m1.CS.model_handshake.CS.hs_certificate ==
                     m.CS.model_handshake.CS.hs_certificate /\
                   m1.CS.model_handshake.CS.hs_certificate_verify ==
                     m.CS.model_handshake.CS.hs_certificate_verify)
  = ()
#pop-options

(* ================= server field pinning (6-head peel) ================= *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_server_fields_pinned
  (ms:CS.connection_model) (install:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv_local:CS.local_event)
  (cv:GCV.certificateVerify) (sf:GFin.finished) (tail:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay ms
          (install :: sent_ev (M.EncryptedExtensions ee) :: sent_ev (M.Certificate cert) ::
           CS.ConnLocalEvent cv_local :: sent_ev (M.CertificateVerify cv) ::
           sent_ev (M.Finished sf) :: tail)
          rs rr final /\
        final.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
        final.CS.model_handshake.CS.hs_certificate == Some cert /\
        final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        final.CS.model_handshake.CS.hs_server_finished == Some sf)
  =
  let e1 = sent_ev (M.EncryptedExtensions ee) in
  let e2 = sent_ev (M.Certificate cert) in
  let e3 = CS.ConnLocalEvent cv_local in
  let e4 = sent_ev (M.CertificateVerify cv) in
  let e5 = sent_ev (M.Finished sf) in
  let l0 = install :: e1 :: e2 :: e3 :: e4 :: e5 :: tail in
  PWReplay.lemma_conn_events_sent_seal_replay_head ms install (e1::e2::e3::e4::e5::tail) rs rr final;
  eliminate exists (m0:CS.connection_model) (ds0 dr0 ts0 tr0:B.bytes).
      CS.legal_event ms install /\ CS.step_model ms install == Some m0 /\
      CS.event_raw_delta_legal ms install ds0 dr0 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection ms install ds0 /\
      Seq.equal rs (B.append ds0 ts0) /\ Seq.equal rr (B.append dr0 tr0) /\
      SMReplay.conn_events_sent_seal_replay m0 (e1::e2::e3::e4::e5::tail) ts0 tr0 final
  with
  (
  PWReplay.lemma_conn_events_sent_seal_replay_head m0 e1 (e2::e3::e4::e5::tail) ts0 tr0 final;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
      CS.legal_event m0 e1 /\ CS.step_model m0 e1 == Some m1 /\
      CS.event_raw_delta_legal m0 e1 ds1 dr1 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m0 e1 ds1 /\
      Seq.equal ts0 (B.append ds1 ts1) /\ Seq.equal tr0 (B.append dr1 tr1) /\
      SMReplay.conn_events_sent_seal_replay m1 (e2::e3::e4::e5::tail) ts1 tr1 final
  with
  (
  lemma_read_ee m0 m1 ee;
  PWReplay.lemma_conn_events_sent_seal_replay_head m1 e2 (e3::e4::e5::tail) ts1 tr1 final;
  eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e2 /\ CS.step_model m1 e2 == Some m2 /\
      CS.event_raw_delta_legal m1 e2 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e2 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 (e3::e4::e5::tail) ts2 tr2 final
  with
  (
  lemma_read_cert m1 m2 cert;
  PWReplay.lemma_conn_events_sent_seal_replay_head m2 e3 (e4::e5::tail) ts2 tr2 final;
  eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
      CS.legal_event m2 e3 /\ CS.step_model m2 e3 == Some m3 /\
      CS.event_raw_delta_legal m2 e3 ds3 dr3 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e3 ds3 /\
      Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
      SMReplay.conn_events_sent_seal_replay m3 (e4::e5::tail) ts3 tr3 final
  with
  (
  lemma_local_pres_server m2 m3 cv_local;
  PWReplay.lemma_conn_events_sent_seal_replay_head m3 e4 (e5::tail) ts3 tr3 final;
  eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
      CS.legal_event m3 e4 /\ CS.step_model m3 e4 == Some m4 /\
      CS.event_raw_delta_legal m3 e4 ds4 dr4 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e4 ds4 /\
      Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
      SMReplay.conn_events_sent_seal_replay m4 (e5::tail) ts4 tr4 final
  with
  (
  lemma_read_cv m3 m4 cv;
  PWReplay.lemma_conn_events_sent_seal_replay_head m4 e5 tail ts4 tr4 final;
  eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
      CS.legal_event m4 e5 /\ CS.step_model m4 e5 == Some m5 /\
      CS.event_raw_delta_legal m4 e5 ds5 dr5 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m4 e5 ds5 /\
      Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
      SMReplay.conn_events_sent_seal_replay m5 tail ts5 tr5 final
  with
  (
  (* role at m4 (before Sent Finished) via config preservation on tail replay from m5 plus step *)
  lemma_sent_replay_preserves_config m5 tail ts5 tr5 final;
  lemma_step_preserves_config m4 e5 m5;
  lemma_read_sf m4 m5 sf;
  lemma_sent_replay_preserves_server_fields m5 tail ts5 tr5 final
  ))))))
#pop-options

(* ================= client field pinning (7-head peel) ================= *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
#restart-solver
let lemma_client_fields_pinned
  (mc:CS.connection_model) (install:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv_validate:CS.local_event)
  (cv:GCV.certificateVerify) (cv_verify:CS.local_event) (sf:GFin.finished)
  (tail:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay mc
          (install :: recv_ev (M.EncryptedExtensions ee) :: recv_ev (M.Certificate cert) ::
           CS.ConnLocalEvent cv_validate :: recv_ev (M.CertificateVerify cv) ::
           CS.ConnLocalEvent cv_verify :: recv_ev (M.Finished sf) :: tail)
          rs rr final /\
        final.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
        final.CS.model_handshake.CS.hs_certificate == Some cert /\
        final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        final.CS.model_handshake.CS.hs_server_finished == Some sf)
  =
  let c1 = recv_ev (M.EncryptedExtensions ee) in
  let c2 = recv_ev (M.Certificate cert) in
  let c3 = CS.ConnLocalEvent cv_validate in
  let c4 = recv_ev (M.CertificateVerify cv) in
  let c5 = CS.ConnLocalEvent cv_verify in
  let c6 = recv_ev (M.Finished sf) in
  let goal = (final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
              final.CS.model_handshake.CS.hs_certificate == Some cert /\
              final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
              final.CS.model_handshake.CS.hs_server_finished == Some sf) in
  PWReplay.lemma_conn_events_received_decode_replay_head mc install (c1::c2::c3::c4::c5::c6::tail) rs rr final;
  eliminate exists (m0:CS.connection_model) (ds0 dr0 ts0 tr0:B.bytes).
      CS.legal_event mc install /\ CS.step_model mc install == Some m0 /\
      CS.event_raw_delta_legal mc install ds0 dr0 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection mc install dr0 /\
      Seq.equal rs (B.append ds0 ts0) /\ Seq.equal rr (B.append dr0 tr0) /\
      SMReplay.conn_events_received_decode_replay m0 (c1::c2::c3::c4::c5::c6::tail) ts0 tr0 final
  with
  (
  lemma_received_replay_preserves_config m0 (c1::c2::c3::c4::c5::c6::tail) ts0 tr0 final;
  PWReplay.lemma_conn_events_received_decode_replay_head m0 c1 (c2::c3::c4::c5::c6::tail) ts0 tr0 final;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
      CS.legal_event m0 c1 /\ CS.step_model m0 c1 == Some m1 /\
      CS.event_raw_delta_legal m0 c1 ds1 dr1 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m0 c1 dr1 /\
      Seq.equal ts0 (B.append ds1 ts1) /\ Seq.equal tr0 (B.append dr1 tr1) /\
      SMReplay.conn_events_received_decode_replay m1 (c2::c3::c4::c5::c6::tail) ts1 tr1 final
  with
  (
  lemma_read_recv_ee m0 m1 ee;
  lemma_step_preserves_config m0 c1 m1;
  PWReplay.lemma_conn_events_received_decode_replay_head m1 c2 (c3::c4::c5::c6::tail) ts1 tr1 final;
  eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 c2 /\ CS.step_model m1 c2 == Some m2 /\
      CS.event_raw_delta_legal m1 c2 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 c2 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 (c3::c4::c5::c6::tail) ts2 tr2 final
  with
  (
  lemma_read_recv_cert m1 m2 cert;
  lemma_step_preserves_config m1 c2 m2;
  PWReplay.lemma_conn_events_received_decode_replay_head m2 c3 (c4::c5::c6::tail) ts2 tr2 final;
  eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
      CS.legal_event m2 c3 /\ CS.step_model m2 c3 == Some m3 /\
      CS.event_raw_delta_legal m2 c3 ds3 dr3 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 c3 dr3 /\
      Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
      SMReplay.conn_events_received_decode_replay m3 (c4::c5::c6::tail) ts3 tr3 final
  with
  (
  lemma_local_pres_client m2 m3 cv_validate;
  lemma_step_preserves_config m2 c3 m3;
  PWReplay.lemma_conn_events_received_decode_replay_head m3 c4 (c5::c6::tail) ts3 tr3 final;
  eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
      CS.legal_event m3 c4 /\ CS.step_model m3 c4 == Some m4 /\
      CS.event_raw_delta_legal m3 c4 ds4 dr4 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 c4 dr4 /\
      Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
      SMReplay.conn_events_received_decode_replay m4 (c5::c6::tail) ts4 tr4 final
  with
  (
  lemma_read_recv_cv m3 m4 cv;
  lemma_step_preserves_config m3 c4 m4;
  PWReplay.lemma_conn_events_received_decode_replay_head m4 c5 (c6::tail) ts4 tr4 final;
  eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
      CS.legal_event m4 c5 /\ CS.step_model m4 c5 == Some m5 /\
      CS.event_raw_delta_legal m4 c5 ds5 dr5 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m4 c5 dr5 /\
      Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
      SMReplay.conn_events_received_decode_replay m5 (c6::tail) ts5 tr5 final
  with
  (
  lemma_local_pres_client m4 m5 cv_verify;
  lemma_step_preserves_config m4 c5 m5;
  PWReplay.lemma_conn_events_received_decode_replay_head m5 c6 tail ts5 tr5 final;
  eliminate exists (m6:CS.connection_model) (ds6 dr6 ts6 tr6:B.bytes).
      CS.legal_event m5 c6 /\ CS.step_model m5 c6 == Some m6 /\
      CS.event_raw_delta_legal m5 c6 ds6 dr6 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m5 c6 dr6 /\
      Seq.equal ts5 (B.append ds6 ts6) /\ Seq.equal tr5 (B.append dr6 tr6) /\
      SMReplay.conn_events_received_decode_replay m6 tail ts6 tr6 final
  with
  (
  lemma_read_recv_sf m5 m6 sf;
  lemma_step_preserves_config m5 c6 m6;
  lemma_received_replay_preserves_client_fields m6 tail ts6 tr6 final
  )))))))
#pop-options

(* ---- non-install local preserves the whole record ---- *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_noninstall_local_preserves_record (m m1:CS.connection_model) (l:CS.local_event)
  : Lemma (requires CS.step_model m (CS.ConnLocalEvent l) == Some m1 /\
                    PB.local_event_does_not_install_record_keys l)
          (ensures m1.CS.model_record == m.CS.model_record)
  = ()

let lemma_local_step_preserves_protected_buffer_empty
  (m m1:CS.connection_model) (l:CS.local_event)
  : Lemma
      (requires
        CS.protected_handshake_buffer_empty m /\
        CS.step_model m (CS.ConnLocalEvent l) == Some m1)
      (ensures CS.protected_handshake_buffer_empty m1)
  = ()

let lemma_received_handshake_step_preserves_protected_buffer_empty
  (m m1:CS.connection_model) (msg:M.handshake_msg)
  : Lemma
      (requires
        CS.protected_handshake_buffer_empty m /\
        CS.step_model m (recv_ev msg) == Some m1)
      (ensures CS.protected_handshake_buffer_empty m1)
  = ()

let lemma_received_replay_head_legal
  (m:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (f:CS.connection_model)
  : Lemma (requires SMReplay.conn_events_received_decode_replay m (ev :: rest) rs rr f)
          (ensures CS.legal_event m ev)
  = ()

let lemma_skip_not_install_server (m m1:CS.connection_model) (l:CS.local_event)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                    m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
                    CS.legal_event m (CS.ConnLocalEvent l))
          (ensures PB.local_event_does_not_install_record_keys l)
  = ()

let lemma_skip_not_install_client (m m1:CS.connection_model) (l:CS.local_event)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    m.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived /\
                    CS.legal_event m (CS.ConnLocalEvent l))
          (ensures PB.local_event_does_not_install_record_keys l)
  = ()
#pop-options

(* ================= Stage A: EE/Cert/CV pairs via :887 ================= *)
let install_ev_server (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
    CS.install_role = CS.ServerEndpoint;
    CS.install_payload = {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material; }; })

let install_ev_client (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
    CS.install_epoch = CS.TrafficHandshake;
    CS.install_direction = CS.TrafficRead;
    CS.install_material = material; })

unfold let stageA_result
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify)
  (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_c:GCV.certificateVerify)
  (cv_verify:CS.local_event) (sf_c:GFin.finished)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event) (raw_tail:list CS.conn_event)
  (final_s final_c:CS.connection_model) : prop =
  exists (server_after2 client_after2:CS.connection_model)
         (pair0 pair1 pair2:PB.protected_message_replay)
         (sts str cts ctr:B.bytes).
    PB.protected_handshake_event_projection_pair pair0
      (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
    PB.protected_handshake_event_projection_pair pair1
      (M.Certificate cert_s) (M.Certificate cert_c) /\
    PB.protected_handshake_event_projection_pair pair2
      (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
    PB.write_read_record_material_aligned server_after2 client_after2 /\
    client_after2.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
    client_after2.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    CS.protected_handshake_buffer_empty client_after2 /\
    CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
    CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
    CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
    CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
    PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
    PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
    PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
    Seq.equal sts ctr /\
    SMReplay.conn_events_sent_seal_replay server_after2
      (sent_ev (M.Finished sf_s) :: tail_s) sts str final_s /\
    SMReplay.conn_events_received_decode_replay client_after2
      (CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail) cts ctr final_c

#push-options "--fuel 2 --ifuel 2 --z3rlimit 180"
let lemma_stageA
  (ms mc:CS.connection_model)
  (material_s material_c:CS.traffic_key_material)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (fl_sent_s fl_recv_s:B.bytes)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate:CS.local_event)
  (cv_c:GCV.certificateVerify) (cv_verify:CS.local_event) (sf_c:GFin.finished)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event) (raw_tail:list CS.conn_event)
  (fl_sent_c fl_recv_c:B.bytes)
  (final_s final_c:CS.connection_model)
  : Lemma
      (requires
        ms.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        mc.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        (match ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
               mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
         | Some a, Some b -> Seq.equal a b | _ -> False) /\
        Seq.equal ms.CS.model_handshake.CS.hs_transcript mc.CS.model_handshake.CS.hs_transcript /\
        CS.negotiated_aead_alg ms.CS.model_handshake ==
          CS.negotiated_aead_alg mc.CS.model_handshake /\
        CS.protected_handshake_buffer_empty mc /\
        CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
        CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
        CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
        CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
        Seq.equal fl_sent_s fl_recv_c /\
        SMReplay.conn_events_sent_seal_replay ms
          (install_ev_server material_s :: sent_ev (M.EncryptedExtensions ee_s) ::
           sent_ev (M.Certificate cert_s) :: CS.ConnLocalEvent cv_local ::
           sent_ev (M.CertificateVerify cv_s) :: sent_ev (M.Finished sf_s) :: tail_s)
          fl_sent_s fl_recv_s final_s /\
        SMReplay.conn_events_received_decode_replay mc
          (install_ev_client material_c :: raw_ee :: raw_cert ::
           CS.ConnLocalEvent cv_validate :: raw_cv ::
           CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail)
          fl_sent_c fl_recv_c final_c)
      (ensures
        stageA_result ee_s cert_s cv_s sf_s tail_s ee_c cert_c cv_c
          cv_verify sf_c raw_ee raw_cert raw_cv raw_sf raw_tail final_s final_c)
  =
  let sEE = sent_ev (M.EncryptedExtensions ee_s) in
  let sCert = sent_ev (M.Certificate cert_s) in
  let sCV = sent_ev (M.CertificateVerify cv_s) in
  let sFin = sent_ev (M.Finished sf_s) in
  let cEE = recv_ev (M.EncryptedExtensions ee_c) in
  let cCert = recv_ev (M.Certificate cert_c) in
  let cCV = recv_ev (M.CertificateVerify cv_c) in
  let lcvl = CS.ConnLocalEvent cv_local in
  let lcvval = CS.ConnLocalEvent cv_validate in
  let lcvv = CS.ConnLocalEvent cv_verify in
  let server_rest0 = sCert :: lcvl :: sCV :: sFin :: tail_s in
  let client_rest0 =
    raw_cert :: lcvval :: raw_cv :: lcvv :: raw_sf :: raw_tail in
  PWSFlight.lemma_single_message_sender_after_server_write_client_read_install_normalizes_received_head
    ms mc material_s material_c
    (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c)
    raw_ee server_rest0 client_rest0
    fl_sent_s fl_recv_s fl_sent_c fl_recv_c final_s final_c;
  PWSFlight.lemma_protected_handshake_event_projection_pair_after_server_write_client_read_install_heads_with_tails
    ms mc material_s material_c
    (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c)
    server_rest0 client_rest0
    fl_sent_s fl_recv_s fl_sent_c fl_recv_c final_s final_c;
  eliminate exists (sm0 cm0 sm1 cm1:CS.connection_model)
                   (pair0:PB.protected_message_replay)
                   (sts1 str1 cts1 ctr1:B.bytes).
      CS.step_model ms (install_ev_server material_s) == Some sm0 /\
      CS.step_model mc (install_ev_client material_c) == Some cm0 /\
      CS.step_model sm0 sEE == Some sm1 /\
      CS.step_model cm0 cEE == Some cm1 /\
      pair0.PB.pm_sender == sm0 /\ pair0.PB.pm_receiver == cm0 /\
      PB.protected_handshake_event_projection_pair pair0
        (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
      Seq.equal sts1 ctr1 /\
      SMReplay.conn_events_sent_seal_replay sm1 server_rest0 sts1 str1 final_s /\
      SMReplay.conn_events_received_decode_replay cm1 client_rest0 cts1 ctr1 final_c
  with
  (
    lemma_step_preserves_config ms (install_ev_server material_s) sm0;
    lemma_step_preserves_config mc (install_ev_client material_c) cm0;
    lemma_step_preserves_config sm0 sEE sm1;
    lemma_step_preserves_config cm0 cEE cm1;
    lemma_read_ee sm0 sm1 ee_s;
    lemma_read_recv_ee cm0 cm1 ee_c;
    PWAlign.lemma_next_seq_models_preserve_write_read_record_material_alignment
      sm0 cm0 sm1 cm1;
    lemma_local_step_preserves_protected_buffer_empty
      mc cm0
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = material_c;
      });
    lemma_received_handshake_step_preserves_protected_buffer_empty
      cm0 cm1 (M.EncryptedExtensions ee_c);
    PWHead.lemma_single_message_sender_normalizes_received_handshake_head
      sm1 cm1 (M.Certificate cert_s) (M.Certificate cert_c) raw_cert
      (lcvl :: sCV :: sFin :: tail_s)
      (lcvval :: raw_cv :: lcvv :: raw_sf :: raw_tail)
      sts1 str1 cts1 ctr1 final_s final_c;
    PWHead.lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
      sm1 cm1 (M.Certificate cert_s) (M.Certificate cert_c)
      (lcvl :: sCV :: sFin :: tail_s)
      (lcvval :: raw_cv :: lcvv :: raw_sf :: raw_tail)
      sts1 str1 cts1 ctr1 final_s final_c;
    lemma_received_replay_head_legal
      cm1 cCert (lcvval :: raw_cv :: lcvv :: raw_sf :: raw_tail)
      cts1 ctr1 final_c;
    eliminate exists (sm2 cm2:CS.connection_model)
                     (pair1:PB.protected_message_replay)
                     (sts2 str2 cts2 ctr2:B.bytes).
        CS.step_model sm1 sCert == Some sm2 /\
        CS.step_model cm1 cCert == Some cm2 /\
        pair1.PB.pm_sender == sm1 /\ pair1.PB.pm_receiver == cm1 /\
        PB.protected_handshake_event_projection_pair pair1
          (M.Certificate cert_s) (M.Certificate cert_c) /\
        Seq.equal sts2 ctr2 /\
        SMReplay.conn_events_sent_seal_replay sm2
          (lcvl :: sCV :: sFin :: tail_s) sts2 str2 final_s /\
        SMReplay.conn_events_received_decode_replay cm2
          (lcvval :: raw_cv :: lcvv :: raw_sf :: raw_tail)
          cts2 ctr2 final_c
    with
    (
      lemma_step_preserves_config sm1 sCert sm2;
      lemma_step_preserves_config cm1 cCert cm2;
      lemma_read_cert sm1 sm2 cert_s;
      lemma_read_recv_cert cm1 cm2 cert_c;
      PWAlign.lemma_next_seq_models_preserve_write_read_record_material_alignment
        sm1 cm1 sm2 cm2;
      lemma_received_handshake_step_preserves_protected_buffer_empty
        cm1 cm2 (M.Certificate cert_c);
      PWHead.lemma_sent_received_replays_skip_empty_opposite_heads_preserve_peer_stream
        sm2 cm2 lcvl lcvval
        (sCV :: sFin :: tail_s)
        (raw_cv :: lcvv :: raw_sf :: raw_tail)
        sts2 str2 cts2 ctr2 final_s final_c;
      eliminate exists (sm3 cm3:CS.connection_model)
                       (sts3 str3 cts3 ctr3:B.bytes).
          CS.legal_event sm2 lcvl /\
          CS.step_model sm2 lcvl == Some sm3 /\
          CS.legal_event cm2 lcvval /\
          CS.step_model cm2 lcvval == Some cm3 /\
          Seq.equal sts3 ctr3 /\
          SMReplay.conn_events_sent_seal_replay sm3
            (sCV :: sFin :: tail_s) sts3 str3 final_s /\
          SMReplay.conn_events_received_decode_replay cm3
            (raw_cv :: lcvv :: raw_sf :: raw_tail) cts3 ctr3 final_c
      with
      (
        lemma_skip_not_install_server sm2 sm3 cv_local;
        lemma_skip_not_install_client cm2 cm3 cv_validate;
        lemma_step_preserves_config sm2 lcvl sm3;
        lemma_step_preserves_config cm2 lcvval cm3;
        PWAlign.lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment
          sm2 cv_local sm3 cm2;
        PWAlign.lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment
          sm3 cm2 cv_validate cm3;
        lemma_local_step_preserves_protected_buffer_empty cm2 cm3 cv_validate;
        PWHead.lemma_single_message_sender_normalizes_received_handshake_head
          sm3 cm3 (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) raw_cv
          (sFin :: tail_s) (lcvv :: raw_sf :: raw_tail)
          sts3 str3 cts3 ctr3 final_s final_c;
        PWHead.lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
          sm3 cm3 (M.CertificateVerify cv_s) (M.CertificateVerify cv_c)
          (sFin :: tail_s) (lcvv :: raw_sf :: raw_tail)
          sts3 str3 cts3 ctr3 final_s final_c;
        lemma_received_replay_head_legal
          cm3 cCV (lcvv :: raw_sf :: raw_tail)
          cts3 ctr3 final_c;
        eliminate exists (sm4 cm4:CS.connection_model)
                         (pair2:PB.protected_message_replay)
                         (sts4 str4 cts4 ctr4:B.bytes).
            CS.step_model sm3 sCV == Some sm4 /\
            CS.step_model cm3 cCV == Some cm4 /\
            pair2.PB.pm_sender == sm3 /\ pair2.PB.pm_receiver == cm3 /\
            PB.protected_handshake_event_projection_pair pair2
              (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
            Seq.equal sts4 ctr4 /\
            SMReplay.conn_events_sent_seal_replay sm4
              (sFin :: tail_s) sts4 str4 final_s /\
            SMReplay.conn_events_received_decode_replay cm4
              (lcvv :: raw_sf :: raw_tail) cts4 ctr4 final_c
        with
        (
          lemma_step_preserves_config sm3 sCV sm4;
          lemma_read_cv sm3 sm4 cv_s;
          lemma_read_recv_cv cm3 cm4 cv_c;
          lemma_step_preserves_config cm3 cCV cm4;
          PWAlign.lemma_next_seq_models_preserve_write_read_record_material_alignment
            sm3 cm3 sm4 cm4;
          lemma_received_handshake_step_preserves_protected_buffer_empty
            cm3 cm4 (M.CertificateVerify cv_c);
          assert (PB.protected_handshake_event_projection_pair pair0
            (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c));
          assert (PB.protected_handshake_event_projection_pair pair1
            (M.Certificate cert_s) (M.Certificate cert_c));
          assert (PB.protected_handshake_event_projection_pair pair2
            (M.CertificateVerify cv_s) (M.CertificateVerify cv_c));
          assert (PB.write_read_record_material_aligned sm4 cm4);
          assert (cm4.CS.model_control ==
            CS.ControlHandshaking CS.HsCertificateVerifyReceived);
          assert (cm4.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert (CS.protected_handshake_buffer_empty cm4);
          assert (CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c));
          assert (CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c));
          assert (CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c));
          assert (CCShape.canonical_event raw_sf ==
            recv_ev (M.Finished sf_c));
          assert (PWHead.received_handshake_head_normal_form
            (M.EncryptedExtensions ee_c) raw_ee);
          assert (PWHead.received_handshake_head_normal_form
            (M.Certificate cert_c) raw_cert);
          assert (PWHead.received_handshake_head_normal_form
            (M.CertificateVerify cv_c) raw_cv);
          assert (Seq.equal sts4 ctr4);
          assert (SMReplay.conn_events_sent_seal_replay sm4
            (sent_ev (M.Finished sf_s) :: tail_s) sts4 str4 final_s);
          assert (SMReplay.conn_events_received_decode_replay cm4
            (CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail)
            cts4 ctr4 final_c);
          introduce exists
            (server_after2 client_after2:CS.connection_model)
            (p0 p1 p2:PB.protected_message_replay)
            (xa xb xc xd:B.bytes).
              PB.protected_handshake_event_projection_pair p0
                (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
              PB.protected_handshake_event_projection_pair p1
                (M.Certificate cert_s) (M.Certificate cert_c) /\
              PB.protected_handshake_event_projection_pair p2
                (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
              PB.write_read_record_material_aligned server_after2 client_after2 /\
              client_after2.CS.model_control ==
                CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
              client_after2.CS.model_config.CS.config_role == CS.ClientEndpoint /\
              CS.protected_handshake_buffer_empty client_after2 /\
              CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
              CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
              CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
              CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
              PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
              PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
              PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
              Seq.equal xa xd /\
              SMReplay.conn_events_sent_seal_replay server_after2
                (sent_ev (M.Finished sf_s) :: tail_s) xa xb final_s /\
              SMReplay.conn_events_received_decode_replay client_after2
                (CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail)
                xc xd final_c
          with sm4 cm4 pair0 pair1 pair2 sts4 str4 cts4 ctr4
          and ()
        )
      )
    )
  )
#pop-options

(* ================= Stage B: SF (Finished) pair via :1138 ================= *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_skip_not_install_client_cv (m:CS.connection_model) (l:CS.local_event)
  : Lemma (requires m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
                    CS.legal_event m (CS.ConnLocalEvent l))
          (ensures PB.local_event_does_not_install_record_keys l)
  = ()

let lemma_aligned_transfer (s r1 r2:CS.connection_model)
  : Lemma (requires PB.write_read_record_material_aligned s r1 /\
                    r2.CS.model_record == r1.CS.model_record)
          (ensures PB.write_read_record_material_aligned s r2)
  = ()
#pop-options

unfold let stageB_result
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify)
  (sf_s:GFin.finished)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_c:GCV.certificateVerify)
  (sf_c:GFin.finished)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event) : prop =
  exists (pair_ee pair_cert pair_cv pair_sf:PB.protected_message_replay).
    PB.protected_handshake_event_projection_pair pair_ee
      (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
    PB.protected_handshake_event_projection_pair pair_cert
      (M.Certificate cert_s) (M.Certificate cert_c) /\
    PB.protected_handshake_event_projection_pair pair_cv
      (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
    PB.protected_handshake_event_projection_pair pair_sf
      (M.Finished sf_s) (M.Finished sf_c) /\
    CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
    CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
    CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
    CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
    PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
    PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
    PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
    PWHead.received_handshake_head_normal_form (M.Finished sf_c) raw_sf

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
let lemma_stageB
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify)
  (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_c:GCV.certificateVerify)
  (cv_verify:CS.local_event) (sf_c:GFin.finished)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event) (raw_tail:list CS.conn_event)
  (final_s final_c:CS.connection_model)
  : Lemma
      (requires
        stageA_result ee_s cert_s cv_s sf_s tail_s ee_c cert_c cv_c
          cv_verify sf_c raw_ee raw_cert raw_cv raw_sf raw_tail final_s final_c)
      (ensures
        stageB_result ee_s cert_s cv_s sf_s ee_c cert_c cv_c sf_c
          raw_ee raw_cert raw_cv raw_sf)
  =
  let cFin = recv_ev (M.Finished sf_c) in
  let sFin = sent_ev (M.Finished sf_s) in
  let lcvv = CS.ConnLocalEvent cv_verify in
  eliminate exists (server_after2 client_after2:CS.connection_model)
                   (pair0 pair1 pair2:PB.protected_message_replay)
                   (sts str cts ctr:B.bytes).
      PB.protected_handshake_event_projection_pair pair0
        (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
      PB.protected_handshake_event_projection_pair pair1
        (M.Certificate cert_s) (M.Certificate cert_c) /\
      PB.protected_handshake_event_projection_pair pair2
        (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
      PB.write_read_record_material_aligned server_after2 client_after2 /\
      client_after2.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
      client_after2.CS.model_config.CS.config_role == CS.ClientEndpoint /\
      CS.protected_handshake_buffer_empty client_after2 /\
      CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
      CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
      CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
      CCShape.canonical_event raw_sf == cFin /\
      PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
      PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
      PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
      Seq.equal sts ctr /\
      SMReplay.conn_events_sent_seal_replay server_after2
        (sFin :: tail_s) sts str final_s /\
      SMReplay.conn_events_received_decode_replay client_after2
        (lcvv :: raw_sf :: raw_tail) cts ctr final_c
  with (
    PWHead.lemma_received_replay_skip_empty_head_preserves_peer_stream
      sts client_after2 lcvv (raw_sf :: raw_tail)
      cts ctr final_c;
    eliminate exists (cvs:CS.connection_model) (tts ttr:B.bytes).
        CS.legal_event client_after2 lcvv /\
        CS.step_model client_after2 lcvv == Some cvs /\
        Seq.equal sts ttr /\
        SMReplay.conn_events_received_decode_replay
          cvs (raw_sf :: raw_tail) tts ttr final_c
    with (
      lemma_skip_not_install_client_cv client_after2 cv_verify;
      lemma_noninstall_local_preserves_record client_after2 cvs cv_verify;
      lemma_aligned_transfer server_after2 client_after2 cvs;
      lemma_local_step_preserves_protected_buffer_empty
        client_after2 cvs cv_verify;
      PWHead.lemma_single_message_sender_normalizes_received_handshake_head
        server_after2 cvs (M.Finished sf_s) (M.Finished sf_c) raw_sf
        tail_s raw_tail sts str tts ttr final_s final_c;
      PWHead.lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
        server_after2 cvs (M.Finished sf_s) (M.Finished sf_c)
        tail_s raw_tail sts str tts ttr final_s final_c;
      eliminate exists (fah rah:CS.connection_model) (psf:PB.protected_message_replay)
                       (ftls ftlr rtls rtlr:B.bytes).
          CS.step_model server_after2 sFin == Some fah /\
          CS.step_model cvs cFin == Some rah /\
          psf.PB.pm_sender == server_after2 /\ psf.PB.pm_receiver == cvs /\
          PB.protected_handshake_event_projection_pair psf (M.Finished sf_s) (M.Finished sf_c) /\
          Seq.equal ftls rtlr /\
          SMReplay.conn_events_sent_seal_replay fah tail_s ftls ftlr final_s /\
          SMReplay.conn_events_received_decode_replay rah raw_tail rtls rtlr final_c
      with (
        introduce exists (pair_ee pair_cert pair_cv pair_sf:PB.protected_message_replay).
          PB.protected_handshake_event_projection_pair pair_ee
            (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
          PB.protected_handshake_event_projection_pair pair_cert
            (M.Certificate cert_s) (M.Certificate cert_c) /\
          PB.protected_handshake_event_projection_pair pair_cv
            (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
          PB.protected_handshake_event_projection_pair pair_sf
            (M.Finished sf_s) (M.Finished sf_c) /\
          CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
          CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
          CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
          CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
          PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
          PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
          PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
          PWHead.received_handshake_head_normal_form (M.Finished sf_c) raw_sf
        with pair0 pair1 pair2 psf
        and ()
      )
    )
  )
#pop-options

(* ================================================================== *)
(* Strengthened capstone: field-pinned 4-pair server-flight inversion *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
#restart-solver
let lemma_conclude_pinned_server_flight
  (client server:CS.connection_state)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished)
  (pair_ee pair_cert pair_cv pair_sf:PB.protected_message_replay)
  : Lemma
      (requires
        server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_s /\
        client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_c /\
        PB.protected_handshake_event_projection_pair pair_ee
          (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
        PB.protected_handshake_event_projection_pair pair_cert
          (M.Certificate cert_s) (M.Certificate cert_c) /\
        PB.protected_handshake_event_projection_pair pair_cv
          (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
        PB.protected_handshake_event_projection_pair pair_sf
          (M.Finished sf_s) (M.Finished sf_c))
      (ensures server_flight_pairs_conclusion client server)
  =
  assert (server_flight_pairs_conclusion client server)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
(* The client's log carries the RAW flight: for a single-message record the
   implementation emits a saturating head [ConnProtectedHandshake] step rather
   than a [ConnNetworkEvent].  [client_normalized_appdata_exact_spine] records
   the raw events together with their NORMAL FORM, which is what downstream
   consumers need in order to normalise their own replays
   ([TLS13.ConnectionState.ProtectedWireNormalize]). *)
let lemma_normalized_client_spine_from_raw
  (s:sysp)
  (ch:GCH.clientHello) (sh:GSH.serverHello)
  (raw_flight:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event) (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event) (sf:GFin.finished)
  (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
  (raw_tail:list CS.conn_event)
  : Lemma
      (requires
        client_raw_prefix_package s ch sh raw_flight /\
        raw_flight ==
          raw_ee :: raw_cert :: CS.ConnLocalEvent cv_validate ::
          raw_cv :: CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail /\
        PWHead.received_handshake_head_normal_form
          (M.EncryptedExtensions ee) raw_ee /\
        PWHead.received_handshake_head_normal_form
          (M.Certificate cert) raw_cert /\
        PWHead.received_handshake_head_normal_form
          (M.CertificateVerify cv) raw_cv /\
        PWHead.received_handshake_head_normal_form
          (M.Finished sf) raw_sf)
      (ensures client_normalized_appdata_exact_spine s.client)
  =
  reveal_opaque (`%client_normalized_appdata_exact_spine)
    client_normalized_appdata_exact_spine;
  eliminate exists
    (start:CS.handshake_start)
    (client_shared:C.x25519_shared_secret)
    (region:list CS.conn_event).
      (forall (e:CS.conn_event).
        L.memP e region ==> CCShape.is_client_hs_install e == true) /\
      (exists (er:CS.conn_event).
        L.memP er region /\
        CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
      (exists (ew:CS.conn_event).
        L.memP ew region /\
        CCShape.is_client_hs_install_dir CS.TrafficWrite ew) /\
      s.client.CS.cs_event_log ==
        L.append
          (PWSeg.client_cleartext_handshake_prefix_events
            start ch sh client_shared)
          (L.append region raw_flight)
  with
  (
    introduce exists
      (start0:CS.handshake_start)
      (ch0:GCH.clientHello) (sh0:GSH.serverHello)
      (client_shared0:C.x25519_shared_secret)
      (region0:list CS.conn_event)
      (ee0:GEE.encryptedExtensions) (cert0:GCert.certificate)
      (cv_validate0:CS.local_event)
      (cv0:GCV.certificateVerify)
      (cv_verify0:CS.local_event)
      (sf0:GFin.finished)
      (raw_ee0 raw_cert0 raw_cv0 raw_sf0:CS.conn_event)
      (tail0:list CS.conn_event).
        client_normalized_appdata_spine_body
          s.client start0 ch0 sh0 client_shared0 region0 ee0 cert0
          cv_validate0 cv0 cv_verify0 sf0
          raw_ee0 raw_cert0 raw_cv0 raw_sf0 tail0
    with start ch sh client_shared region
         ee cert cv_validate cv cv_verify sf
         raw_ee raw_cert raw_cv raw_sf raw_tail
    and ()
  )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let lemma_finish_strong (s:sysp)
  (ms:CS.connection_model) (material_s:CS.traffic_key_material)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (d_ch_s rest_sr:B.bytes)
  (mc:CS.connection_model) (material_c:CS.traffic_key_material)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate_c:CS.local_event)
  (cv_c:GCV.certificateVerify) (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
  (tail_c raw_flight_c:list CS.conn_event)
  (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (rest_cs:B.bytes)
  : Lemma
      (requires
        server_flight_bridge_inputs s.client s.server /\
        server_side_package s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
          fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr /\
        client_side_package s mc material_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
          tail_c raw_flight_c fl_sent_c fl_recv_c ch_c sh_c rest_cs)
      (ensures
        server_flight_pairs_conclusion s.client s.server /\
        client_normalized_appdata_exact_spine s.client)
  =
  lemma_goalA_state s;
  lemma_byte_pairing_quiet s;
  let cs = s.client.CS.cs_wire_log.CL.raw_sent in
  let sr = s.server.CS.cs_wire_log.CL.raw_received in
  let ss = s.server.CS.cs_wire_log.CL.raw_sent in
  let cr = s.client.CS.cs_wire_log.CL.raw_received in
  let final_s = s.server.CS.cs_model in
  let final_c = s.client.CS.cs_model in
  lemma_client_side_package_has_raw_prefix s mc material_c
    ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
    tail_c raw_flight_c fl_sent_c fl_recv_c ch_c sh_c rest_cs;
  (* ---- CH agreement ---- *)
  lemma_ch_serialize_agree ch_c ch_s cs sr rest_cs rest_sr d_ch_s;
  (* ---- SH agreement + flight-byte pairing ---- *)
  Seq.lemma_eq_elim ss cr;
  assert (Seq.equal ss
            (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh_c))) fl_recv_c));
  lemma_front_handshake_record_agree
    (W.serialize_handshake (M.ServerHello sh_s))
    (W.serialize_handshake (M.ServerHello sh_c))
    fl_sent_s fl_recv_c ss;
  assert (Seq.equal fl_sent_s fl_recv_c);
  (* ---- ServerHello agreement: same serialized bytes, injective codec ---- *)
  Inj.lemma_serialize_handshake_server_hello_injective sh_s sh_c;
  assert (sh_s == sh_c);
  assert (CS.negotiated_aead_alg ms.CS.model_handshake ==
          CS.negotiated_aead_alg mc.CS.model_handshake);
  (* ---- transcript equality ---- *)
  lemma_transcript_cong ch_s ch_c sh_s sh_c;
  assert (Seq.equal ms.CS.model_handshake.CS.hs_transcript
                    mc.CS.model_handshake.CS.hs_transcript);
  (* ---- handshake-secret agreement ---- *)
  lemma_secret_swap final_s.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
                    final_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
  assert (match ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
                mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
          | Some a, Some b -> Seq.equal a b
          | _ -> False);
  eliminate exists (g_ee g_cert g_cv g_sf raw_tail:list CS.conn_event).
      raw_flight_c ==
        L.append g_ee
          (L.append g_cert
            (CS.ConnLocalEvent cv_validate_c ::
              L.append g_cv
                (CS.ConnLocalEvent cv_verify_c ::
                  L.append g_sf raw_tail))) /\
      CCShape.delivers_handshake g_ee (M.EncryptedExtensions ee_c) /\
      CCShape.delivers_handshake g_cert (M.Certificate cert_c) /\
      CCShape.delivers_handshake g_cv (M.CertificateVerify cv_c) /\
      CCShape.delivers_handshake g_sf (M.Finished sf_c) /\
      CCShape.canonical_log raw_tail == tail_c
  with
  (
    (* Peel each delivery group down to the event that carries its message. *)
    CCShape.lemma_delivers_handshake_singleton g_ee (M.EncryptedExtensions ee_c);
    CCShape.lemma_delivers_handshake_singleton g_cert (M.Certificate cert_c);
    CCShape.lemma_delivers_handshake_singleton g_cv (M.CertificateVerify cv_c);
    CCShape.lemma_delivers_handshake_singleton g_sf (M.Finished sf_c);
    let raw_ee = L.hd g_ee in
    let raw_cert = L.hd g_cert in
    let raw_cv = L.hd g_cv in
    let raw_sf = L.hd g_sf in
    assert (L.append g_sf raw_tail == raw_sf :: raw_tail);
    assert (L.append g_cv
              (CS.ConnLocalEvent cv_verify_c :: L.append g_sf raw_tail) ==
            raw_cv :: CS.ConnLocalEvent cv_verify_c :: raw_sf :: raw_tail);
    assert (raw_flight_c ==
      raw_ee :: raw_cert :: CS.ConnLocalEvent cv_validate_c ::
      raw_cv :: CS.ConnLocalEvent cv_verify_c :: raw_sf :: raw_tail);
    let server_list_stageA =
      install_ev_server material_s ::
      sent_ev (M.EncryptedExtensions ee_s) ::
      sent_ev (M.Certificate cert_s) ::
      CS.ConnLocalEvent cv_local_s ::
      sent_ev (M.CertificateVerify cv_s) ::
      sent_ev (M.Finished sf_s) :: tail_s in
    let client_list_stageA =
      install_ev_client material_c ::
      raw_ee :: raw_cert :: CS.ConnLocalEvent cv_validate_c ::
      raw_cv :: CS.ConnLocalEvent cv_verify_c :: raw_sf :: raw_tail in
    let client_list_ordinary =
      install_ev_client material_c ::
      recv_ev (M.EncryptedExtensions ee_c) ::
      recv_ev (M.Certificate cert_c) ::
      CS.ConnLocalEvent cv_validate_c ::
      recv_ev (M.CertificateVerify cv_c) ::
      CS.ConnLocalEvent cv_verify_c ::
      recv_ev (M.Finished sf_c) :: raw_tail in
    assert (RI.server_hs_write_install_event material_s ==
      install_ev_server material_s);
    assert (RI.client_hs_read_install_event material_c ==
      install_ev_client material_c);
    assert (server_flight_events ee_s cert_s cv_local_s cv_s sf_s tail_s ==
      sent_ev (M.EncryptedExtensions ee_s) ::
      sent_ev (M.Certificate cert_s) ::
      CS.ConnLocalEvent cv_local_s ::
      sent_ev (M.CertificateVerify cv_s) ::
      sent_ev (M.Finished sf_s) :: tail_s);
    lemma_replay_cong_sent ms
      (RI.server_hs_write_install_event material_s ::
       server_flight_events ee_s cert_s cv_local_s cv_s sf_s tail_s)
      server_list_stageA fl_sent_s fl_recv_s final_s;
    lemma_replay_cong_recv mc
      (RI.client_hs_read_install_event material_c :: raw_flight_c)
      client_list_stageA fl_sent_c fl_recv_c final_c;
    lemma_sent_replay_preserves_config
      ms server_list_stageA fl_sent_s fl_recv_s final_s;
    lemma_received_replay_preserves_config
      mc client_list_stageA fl_sent_c fl_recv_c final_c;
    assert (ms.CS.model_config.CS.config_role == CS.ServerEndpoint);
    assert (mc.CS.model_config.CS.config_role == CS.ClientEndpoint);
    lemma_server_fields_pinned ms (install_ev_server material_s)
      ee_s cert_s cv_local_s cv_s sf_s tail_s
      fl_sent_s fl_recv_s final_s;
    lemma_stageA ms mc material_s material_c
      ee_s cert_s cv_local_s cv_s sf_s tail_s fl_sent_s fl_recv_s
      ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
      raw_ee raw_cert raw_cv raw_sf raw_tail
      fl_sent_c fl_recv_c final_s final_c;
    lemma_stageB ee_s cert_s cv_s sf_s tail_s
      ee_c cert_c cv_c cv_verify_c sf_c
      raw_ee raw_cert raw_cv raw_sf raw_tail final_s final_c;
    eliminate exists
      (pair_ee pair_cert pair_cv pair_sf:PB.protected_message_replay).
        PB.protected_handshake_event_projection_pair pair_ee
          (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c) /\
        PB.protected_handshake_event_projection_pair pair_cert
          (M.Certificate cert_s) (M.Certificate cert_c) /\
        PB.protected_handshake_event_projection_pair pair_cv
          (M.CertificateVerify cv_s) (M.CertificateVerify cv_c) /\
        PB.protected_handshake_event_projection_pair pair_sf
          (M.Finished sf_s) (M.Finished sf_c) /\
        CCShape.canonical_event raw_ee == recv_ev (M.EncryptedExtensions ee_c) /\
        CCShape.canonical_event raw_cert == recv_ev (M.Certificate cert_c) /\
        CCShape.canonical_event raw_cv == recv_ev (M.CertificateVerify cv_c) /\
        CCShape.canonical_event raw_sf == recv_ev (M.Finished sf_c) /\
        PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee_c) raw_ee /\
        PWHead.received_handshake_head_normal_form (M.Certificate cert_c) raw_cert /\
        PWHead.received_handshake_head_normal_form (M.CertificateVerify cv_c) raw_cv /\
        PWHead.received_handshake_head_normal_form (M.Finished sf_c) raw_sf
    with
    (
      lemma_normalized_client_spine_from_raw s ch_c sh_c raw_flight_c
        ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
        raw_ee raw_cert raw_cv raw_sf raw_tail;
      PWNorm.lemma_normalize_flight_recv_after
        mc (install_ev_client material_c)
        (M.EncryptedExtensions ee_c) (M.Certificate cert_c)
        (M.CertificateVerify cv_c) (M.Finished sf_c)
        raw_ee raw_cert raw_cv raw_sf
        cv_validate_c cv_verify_c raw_tail
        fl_sent_c fl_recv_c final_c;
      assert (PWNorm.recv_ev (M.EncryptedExtensions ee_c) ==
              recv_ev (M.EncryptedExtensions ee_c));
      assert (install_ev_client material_c ::
         PWNorm.normal_flight
           (M.EncryptedExtensions ee_c) (M.Certificate cert_c)
           (M.CertificateVerify cv_c) (M.Finished sf_c)
           cv_validate_c cv_verify_c raw_tail
        == client_list_ordinary);
      lemma_replay_cong_recv mc
        (install_ev_client material_c ::
         PWNorm.normal_flight
           (M.EncryptedExtensions ee_c) (M.Certificate cert_c)
           (M.CertificateVerify cv_c) (M.Finished sf_c)
           cv_validate_c cv_verify_c raw_tail)
        client_list_ordinary
        fl_sent_c fl_recv_c final_c;
      lemma_client_fields_pinned mc (install_ev_client material_c)
        ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c raw_tail
        fl_sent_c fl_recv_c final_c;
      assert (final_s.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_s);
      assert (final_s.CS.model_handshake.CS.hs_certificate == Some cert_s);
      assert (final_s.CS.model_handshake.CS.hs_certificate_verify == Some cv_s);
      assert (final_s.CS.model_handshake.CS.hs_server_finished == Some sf_s);
      assert (final_c.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_c);
      assert (final_c.CS.model_handshake.CS.hs_certificate == Some cert_c);
      assert (final_c.CS.model_handshake.CS.hs_certificate_verify == Some cv_c);
      assert (final_c.CS.model_handshake.CS.hs_server_finished == Some sf_c);
      lemma_conclude_pinned_server_flight s.client s.server
        ee_s cert_s cv_s sf_s ee_c cert_c cv_c sf_c
        pair_ee pair_cert pair_cv pair_sf
    )
  )
#pop-options

(* Note: the server-side and client-side existential packages carry 14 and 15
   witnesses respectively.  Eliminating them in a single definition makes the
   proof obligation enormous: [eliminate exists] desugars to a chain of
   [indefinite_descriptionK] calls whose results are destructed by dependent
   tuples, and since F* no longer substitutes let-bound definitions into VCs
   those destructurings survive un-reduced in the context (FStarLang/FStar#4444).
   Nesting the two eliminations multiplied the cost: it needed [--z3rlimit 1600]
   and drove Z3 to a 17GB resident set, which is fatal on a 16GB CI runner.
   Splitting the two eliminations into separate definitions keeps each query
   small.  Do not merge them back together. *)

#restart-solver
#push-options "--fuel 2 --ifuel 2 --z3rlimit 800"
let lemma_combine_client_side (s:sysp)
  (ms:CS.connection_model) (material_s:CS.traffic_key_material)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
  (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (d_ch_s rest_sr:B.bytes)
  : Lemma (requires
            server_flight_bridge_inputs s.client s.server /\
            server_side_package s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
              fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr)
          (ensures
            server_flight_pairs_conclusion s.client s.server /\
            client_normalized_appdata_exact_spine s.client)
  =
  lemma_client_side s;
  eliminate exists (mc:CS.connection_model) (material_c:CS.traffic_key_material)
    (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_validate_c:CS.local_event)
    (cv_c:GCV.certificateVerify) (cv_verify_c:CS.local_event) (sf_c:GFin.finished)
    (tail_c raw_flight_c:list CS.conn_event)
    (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
    (rest_cs:B.bytes).
    client_side_package s mc material_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
      tail_c raw_flight_c fl_sent_c fl_recv_c ch_c sh_c rest_cs
  with
  (
    lemma_finish_strong s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
      fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr
      mc material_c ee_c cert_c cv_validate_c cv_c cv_verify_c sf_c
      tail_c raw_flight_c
      fl_sent_c fl_recv_c ch_c sh_c rest_cs
  )
#pop-options

#restart-solver
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_combine_strong (s:sysp)
  : Lemma (requires server_flight_bridge_inputs s.client s.server)
          (ensures
            server_flight_pairs_conclusion s.client s.server /\
            client_normalized_appdata_exact_spine s.client)
  =
  lemma_server_side s;
  eliminate exists (ms:CS.connection_model) (material_s:CS.traffic_key_material)
    (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
    (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (tail_s:list CS.conn_event)
    (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
    (d_ch_s rest_sr:B.bytes).
    server_side_package s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
      fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr
  with
  (
    lemma_combine_client_side s ms material_s ee_s cert_s cv_local_s cv_s sf_s tail_s
      fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_sr
  )
#pop-options

(* ================================================================== *)
(* The deliverable.                                                    *)
(* ================================================================== *)
let lemma_server_flight_pairs_from_replays_and_pairing client server =
  let s : sysp = { client = client; server = server } in
  lemma_combine_strong s

let lemma_client_normalized_appdata_exact_spine_from_replays_and_pairing
  client server =
  let s : sysp = { client = client; server = server } in
  lemma_combine_strong s

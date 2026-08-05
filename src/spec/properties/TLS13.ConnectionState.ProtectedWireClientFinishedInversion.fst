module TLS13.ConnectionState.ProtectedWireClientFinishedInversion

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CCShape = TLS13.ConnectionState.ClientCanonicalShape
module CD = TLS13.Impl.Client.Driver
module CL = TLS13.ConnectionLog
module CNoCcs = TLS13.ConnectionState.ClientNoCcsFromPairing
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
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module PWSFlight = TLS13.ConnectionState.ProtectedWireServerFlight
module PWHead = TLS13.ConnectionState.ProtectedWireHead
module PWNorm = TLS13.ConnectionState.ProtectedWireNormalize
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module PWStaged = TLS13.ConnectionState.ProtectedWireStaged
module SFInv = TLS13.ConnectionState.ProtectedWireServerFlightInversion
module Pairing = TLS13.Impl.Driver.Pairing
module R = TLS13.Record.Spec
module RR = TLS13.Wire.Spec.Reveal.Record
module RecAlign = TLS13.ConnectionState.ProtectedWireRecordAlignment
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

module RI = TLS13.ConnectionState.ProtectedWireServerFlightInversion.RedundantInstall
module Region = TLS13.ConnectionState.ProtectedWireServerFlightInversion.Region
module CReg = TLS13.ConnectionState.ProtectedWireServerFlightInversion.ClientRegion
module Canonical = TLS13.Spec.StateMachine.Canonical
module NRA = TLS13.ConnectionState.NoCcsRecordAux
module GCCS = TLS13.Wire.Generated.ChangeCipherSpec

open TLS13.ConnectionState.ProtectedWireBase

noeq type sysp = { client : CS.connection_state; server : CS.connection_state }

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_goalA_state (s:sysp)
  : Lemma (requires client_finished_bridge_inputs s.client s.server)
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
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80 --split_queries always"
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
  returns
    (Seq.equal (W.serialize_handshake (M.ClientHello ch_c))
               (W.serialize_handshake (M.ClientHello ch_s)))
  with _.
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100"
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
  (* The case split is written out one constructor at a time rather than left to
     a `| _ -> ()` catch-all: under Z3 4.15.3 the single catch-all query no
     longer closes within rlimit 100 at ifuel 4, because it has to invert
     `local_event` (13 constructors) inside `conn_event` in one go.  Enumerating
     the arms gives the solver the inversion for free, and each arm is then a
     small, independent query. *)
  match ev with
  | CS.ConnNetworkEvent _ -> ()
  | CS.ConnProtectedHandshake _ -> ()
  | CS.ConnLocalEvent lev ->
    match lev with
    | CS.LocalStartHandshake _ -> ()
    | CS.LocalStartServer -> ()
    | CS.LocalSelectServerParameters _ -> ()
    | CS.LocalDeriveSharedSecret _ -> ()
    | CS.LocalInstallTrafficKeys _ -> ()
    | CS.LocalInstallTrafficKeysForRole _ -> ()
    | CS.LocalValidateCertificate _ -> ()
    | CS.LocalVerifyCertificateSignature _ -> ()
    | CS.LocalSignCertificateVerify _ -> ()
    | CS.LocalVerifyFinished _ -> ()
    | CS.LocalVerifyClientFinished _ -> ()
    | CS.LocalDeliverApplicationData _ -> ()
    | CS.LocalFail _ -> ()
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
    returns
      (final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
         m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
         m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
    with _.
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
    returns
      (final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
         m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
       final.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
         m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
    with _.
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
    returns server_write_installed final material
    with _.
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
    returns (exists (material:CS.traffic_key_material). server_write_installed final material)
    with _.
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
         returns (exists (ew2:CS.conn_event). L.memP ew2 rest /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew2)
         with _. ();
         lemma_server_region_write_installed model1 rest tail_sent tail_received final)
    )
#pop-options

(* ================= inlined from Scratch_Prefix ================= *)


let server_prefix_transcript (ch:GCH.clientHello) (sh:GSH.serverHello) : GTot B.bytes =
  Tr.append
    (Tr.append Tr.empty (W.serialize_handshake (M.ClientHello ch)))
    (W.serialize_handshake (M.ServerHello sh))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
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
  returns
    (p.CS.model_config == cfg /\
     p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
     p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
     p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
  with _.
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    returns
      (p.CS.model_config == cfg /\
       p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
       p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
       p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
    with _.
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      returns
        (p.CS.model_config == cfg /\
         p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
         p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
         p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
      with _.
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 r4 ts4 tr4 p
        returns
          (p.CS.model_config == cfg /\
           p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
           p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
           p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
        with _.
        (
          PWReplay.lemma_conn_events_sent_seal_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m4 e4 ds5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_sent_seal_replay m5 [] ts5 tr5 p
          returns
            (p.CS.model_config == cfg /\
             p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
             p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
             p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
          with _. ()
        )
      )
    )
  )
#pop-options

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
      (ensures m1.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript)
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
      (ensures final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript)
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
    returns (final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript)
    with _.
    (
      lemma_install_step_preserves_transcript m ev model1;
      lemma_region_preserves_transcript_sent model1 rest ts tr final
    )
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
#restart-solver
let rec lemma_region_preserves_transcript_received
  (m:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        L.for_all is_key_install_ev evs /\
        SMReplay.conn_events_received_decode_replay m evs rs rr final)
      (ensures final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript)
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
    returns (final.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript)
    with _.
    (
      lemma_install_step_preserves_transcript m ev model1;
      lemma_region_preserves_transcript_received model1 rest ts tr final
    )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
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
        p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
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
  returns
    (p.CS.model_config == cfg /\
     p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
     p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
     p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
  with _.
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    returns
      (p.CS.model_config == cfg /\
       p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
       p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
       p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
    with _.
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      returns
        (p.CS.model_config == cfg /\
         p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
         p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
         p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
      with _.
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 [] ts4 tr4 p
        returns
          (p.CS.model_config == cfg /\
           p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
           p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
           p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
        with _. ()
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 80 --split_queries always"
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
  returns goal
  with _.
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    returns goal
    with _.
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      returns goal
      with _.
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 r4 ts4 tr4 p
        returns goal
        with _.
        (
          PWReplay.lemma_conn_events_sent_seal_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m4 e4 ds5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_sent_seal_replay m5 [] ts5 tr5 p
          returns goal
          with _.
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
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
  returns goal
  with _.
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    returns goal
    with _.
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      returns goal
      with _.
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 r4 ts4 tr4 p
        returns goal
        with _.
        (
          PWReplay.lemma_conn_events_received_decode_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m4 e4 dr5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_received_decode_replay m5 [] ts5 tr5 p
          returns goal
          with _.
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
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
  returns goal
  with _.
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    returns goal
    with _.
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      returns goal
      with _.
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 [] ts4 tr4 p
        returns goal
        with _.
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

#push-options "--fuel 2 --ifuel 4 --z3rlimit 100 --split_queries always"
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
  returns goal
  with _.
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    returns goal
    with _.
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      returns goal
      with _.
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 [] ts4 tr4 p
        returns goal
        with _.
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
          with _. lemma_install_empty_sent x);
    L.for_all_mem Region.is_empty_sent_ev region

let lemma_forall_install_key (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true))
      (ensures L.for_all is_key_install_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> is_key_install_ev x == true
    with (introduce L.memP x region ==> is_key_install_ev x == true
          with _. lemma_install_key x);
    L.for_all_mem is_key_install_ev region
#pop-options

(* ------------------------------------------------------------------ *)
(* The server flight event list (post-region).                        *)
(* ------------------------------------------------------------------ *)

let sent_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
                         CL.message_value = M.TlsHandshake msg })


let lemma_install_empty_recv (e:CS.conn_event)
  : Lemma (requires CCShape.is_client_hs_install e == true)
          (ensures Region.is_empty_recv_ev e == true)
  = ()

let lemma_install_key_c (e:CS.conn_event)
  : Lemma (requires CCShape.is_client_hs_install e == true)
          (ensures is_key_install_ev e == true)
  = ()

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_forall_install_empty_recv (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true))
      (ensures L.for_all Region.is_empty_recv_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> Region.is_empty_recv_ev x == true
    with (introduce L.memP x region ==> Region.is_empty_recv_ev x == true
          with _. lemma_install_empty_recv x);
    L.for_all_mem Region.is_empty_recv_ev region

let lemma_forall_install_key_c (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true))
      (ensures L.for_all is_key_install_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> is_key_install_ev x == true
    with (introduce L.memP x region ==> is_key_install_ev x == true
          with _. lemma_install_key_c x);
    L.for_all_mem is_key_install_ev region
#pop-options

(* ------------------------------------------------------------------ *)
(* The client (received) flight event list (post-region).             *)
(* ------------------------------------------------------------------ *)

let recv_ev (msg:M.handshake_msg) : CS.conn_event =
  CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
                         CL.message_value = M.TlsHandshake msg })


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

let lemma_replay_cong_sent
  (m:CS.connection_model) (l1 l2:list CS.conn_event) (a b:B.bytes) (f:CS.connection_model)
  : Lemma
      (requires l1 == l2 /\ SMReplay.conn_events_sent_seal_replay m l1 a b f)
      (ensures SMReplay.conn_events_sent_seal_replay m l2 a b f)
  = ()

#restart-solver
let lemma_replay_cong_recv
  (m:CS.connection_model) (l1 l2:list CS.conn_event) (a b:B.bytes) (f:CS.connection_model)
  : Lemma
      (requires l1 == l2 /\ SMReplay.conn_events_received_decode_replay m l1 a b f)
      (ensures SMReplay.conn_events_received_decode_replay m l2 a b f)
  = ()

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

let lemma_step_preserves_config (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma (requires CS.step_model m ev == Some m1)
          (ensures m1.CS.model_config == m.CS.model_config)
  = match ev with
    | CS.ConnProtectedHandshake _ -> ()
    | CS.ConnLocalEvent local -> ()
    | CS.ConnNetworkEvent msg -> ()

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
      returns (final.CS.model_config == m.CS.model_config)
      with _.
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
      returns (final.CS.model_config == m.CS.model_config)
      with _.
      ( lemma_step_preserves_config m ev model1;
        lemma_received_replay_preserves_config model1 rest tail_sent tail_received final )
#pop-options



(* ================================================================== *)
(* STEP 1 building blocks: direction-swapped region infrastructure.    *)
(* ================================================================== *)

(* ---------------- CLIENT WRITE install (sent-seal) ---------------- *)

let client_write_keys_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_record.CS.record_write ==
    R.install_keys m.CS.model_record.CS.record_write R.Handshake
      material.CS.traffic_key material.CS.traffic_iv

let client_write_material_matches (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  CS.traffic_install_matches_key_schedule
    m.CS.model_handshake {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material;
    }

let client_write_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == Some material /\
  client_write_keys_installed m material /\
  client_write_material_matches m material

let cw_install_ev (install:CS.traffic_key_install) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)

let install_of_client_hs_cw (ev:CS.conn_event{CCShape.is_client_hs_install ev == true})
  : (install:CS.traffic_key_install{
      ev == cw_install_ev install /\
      install.CS.install_epoch == CS.TrafficHandshake})
= match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) -> install

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_cw_install_step_preserves
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        CS.legal_event m (cw_install_ev install) /\
        CS.step_model m (cw_install_ev install) == Some m1 /\
        client_write_installed m material)
      (ensures client_write_installed m1 material /\
               m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_cw_write_install_establishes
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        install.CS.install_direction == CS.TrafficWrite /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        CS.legal_event m (cw_install_ev install) /\
        CS.step_model m (cw_install_ev install) == Some m1)
      (ensures client_write_installed m1 install.CS.install_material)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_cw_install_step_preserves_control
  (m:CS.connection_model) (install:CS.traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_epoch == CS.TrafficHandshake /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        CS.legal_event m (cw_install_ev install) /\
        CS.step_model m (cw_install_ev install) == Some m1)
      (ensures
        m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_cw_region_preserves_write_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        client_write_installed m material /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures client_write_installed final material)
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_client_hs_cw ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    returns client_write_installed final material
    with _.
    ( lemma_cw_install_step_preserves m install model1 material;
      lemma_cw_region_preserves_write_installed model1 rest tail_sent tail_received final material )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_cw_region_write_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        (exists (ew:CS.conn_event). L.memP ew region /\ CCShape.is_client_hs_install_dir CS.TrafficWrite ew) /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). client_write_installed final material))
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_client_hs_cw ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    returns (exists (material:CS.traffic_key_material). client_write_installed final material)
    with _.
    ( if install.CS.install_direction = CS.TrafficWrite
      then
        (lemma_cw_write_install_establishes m install model1;
         lemma_cw_region_preserves_write_installed
           model1 rest tail_sent tail_received final install.CS.install_material)
      else
        (lemma_cw_install_step_preserves_control m install model1;
         eliminate exists (ew:CS.conn_event).
           L.memP ew region /\ CCShape.is_client_hs_install_dir CS.TrafficWrite ew
         returns (exists (ew2:CS.conn_event). L.memP ew2 rest /\ CCShape.is_client_hs_install_dir CS.TrafficWrite ew2)
         with _. ();
         lemma_cw_region_write_installed model1 rest tail_sent tail_received final) )
#pop-options

(* ---------------- SERVER READ install (received-decode) ---------------- *)

let server_read_keys_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_record.CS.record_read ==
    R.install_keys m.CS.model_record.CS.record_read R.Handshake
      material.CS.traffic_key material.CS.traffic_iv

let server_read_material_matches (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint
    m.CS.model_handshake {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = material;
    }

let server_read_installed (m:CS.connection_model) (material:CS.traffic_key_material) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
  m.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == Some material /\
  server_read_keys_installed m material /\
  server_read_material_matches m material

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_sr_install_step_preserves
  (m:CS.connection_model) (install:CS.role_traffic_key_install)
  (m1:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        install.CS.install_role == CS.ServerEndpoint /\
        install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
        CS.legal_event m (server_hs_install_ev install) /\
        CS.step_model m (server_hs_install_ev install) == Some m1 /\
        server_read_installed m material)
      (ensures server_read_installed m1 material /\
               m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_sr_read_install_establishes
  (m:CS.connection_model) (install:CS.role_traffic_key_install)
  (m1:CS.connection_model)
  : Lemma
      (requires
        install.CS.install_role == CS.ServerEndpoint /\
        install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake /\
        install.CS.install_payload.CS.install_direction == CS.TrafficRead /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        CS.legal_event m (server_hs_install_ev install) /\
        CS.step_model m (server_hs_install_ev install) == Some m1)
      (ensures server_read_installed m1 install.CS.install_payload.CS.install_material)
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_sr_install_step_preserves_control
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
= ()
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_sr_region_preserves_read_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        server_read_installed m material /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures server_read_installed final material)
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns server_read_installed final material
    with _.
    ( lemma_sr_install_step_preserves m install model1 material;
      lemma_sr_region_preserves_read_installed model1 rest tail_sent tail_received final material )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_sr_region_read_installed
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        (exists (er:CS.conn_event). L.memP er region /\ SCShape.is_server_hs_install_dir CS.TrafficRead er) /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). server_read_installed final material))
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns (exists (material:CS.traffic_key_material). server_read_installed final material)
    with _.
    ( if install.CS.install_payload.CS.install_direction = CS.TrafficRead
      then
        (lemma_sr_read_install_establishes m install model1;
         lemma_sr_region_preserves_read_installed
           model1 rest tail_sent tail_received final install.CS.install_payload.CS.install_material)
      else
        (lemma_sr_install_step_preserves_control m install model1;
         eliminate exists (er:CS.conn_event).
           L.memP er region /\ SCShape.is_server_hs_install_dir CS.TrafficRead er
         returns (exists (er2:CS.conn_event). L.memP er2 rest /\ SCShape.is_server_hs_install_dir CS.TrafficRead er2)
         with _. ();
         lemma_sr_region_read_installed model1 rest tail_sent tail_received final) )
#pop-options

(* ---------- Redundant-install identity + byte-neutral prepend ---------- *)

let cw_redundant_install_event (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficHandshake;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = material;
    })

let sr_redundant_install_event (material:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = material;
      };
    })

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_redundant_cw_install_identity
  (m:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires client_write_installed m material)
      (ensures
        CS.legal_event m (cw_redundant_install_event material) /\
        CS.step_model m (cw_redundant_install_event material) == Some m)
= assert (CS.step_model m (cw_redundant_install_event material) == Some m);
  assert (CS.legal_event m (cw_redundant_install_event material))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_redundant_sr_install_identity
  (m:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires server_read_installed m material)
      (ensures
        CS.legal_event m (sr_redundant_install_event material) /\
        CS.step_model m (sr_redundant_install_event material) == Some m)
= assert (CS.step_model m (sr_redundant_install_event material) == Some m);
  assert (CS.legal_event m (sr_redundant_install_event material))
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_cw_install_sent
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        client_write_installed m material /\
        SMReplay.conn_events_sent_seal_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_sent_seal_replay
          m (cw_redundant_install_event material :: rest) rs rr final)
= lemma_redundant_cw_install_identity m material;
  let ev = cw_redundant_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (Canonical.sent_event_nonempty_seal_projection m ev B.empty);
  PWReplay.lemma_conn_events_sent_seal_replay_cons
    m ev rest rs rr final m B.empty B.empty rs rr
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_sr_install_received
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        server_read_installed m material /\
        SMReplay.conn_events_received_decode_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_received_decode_replay
          m (sr_redundant_install_event material :: rest) rs rr final)
= lemma_redundant_sr_install_identity m material;
  let ev = sr_redundant_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (Canonical.received_event_nonempty_decode_projection m ev B.empty);
  PWReplay.lemma_conn_events_received_decode_replay_cons
    m ev rest rs rr final m B.empty B.empty rs rr
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
let lemma_server_prefix_model_recv
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
        p.CS.model_config == cfg /\
        p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
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
  PWReplay.lemma_conn_events_received_decode_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m0 e0 dr1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_received_decode_replay m1 r1 ts1 tr1 p
  returns
    (p.CS.model_config == cfg /\
     p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
     p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
     p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
  with _.
  (
    PWReplay.lemma_conn_events_received_decode_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m1 e1 dr2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_received_decode_replay m2 r2 ts2 tr2 p
    returns
      (p.CS.model_config == cfg /\
       p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
       p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
       p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
    with _.
    (
      PWReplay.lemma_conn_events_received_decode_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m2 e2 dr3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_received_decode_replay m3 r3 ts3 tr3 p
      returns
        (p.CS.model_config == cfg /\
         p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
         p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
         p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
      with _.
      (
        PWReplay.lemma_conn_events_received_decode_replay_head m3 e3 r4 ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m3 e3 dr4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_received_decode_replay m4 r4 ts4 tr4 p
        returns
          (p.CS.model_config == cfg /\
           p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
           p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
           p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
        with _.
        (
          PWReplay.lemma_conn_events_received_decode_replay_head m4 e4 [] ts4 tr4 p;
          eliminate exists (m5:CS.connection_model) (ds5 dr5 ts5 tr5:B.bytes).
            CS.legal_event m4 e4 /\ CS.step_model m4 e4 == Some m5 /\
            CS.event_raw_delta_legal m4 e4 ds5 dr5 /\
            TLS13.Spec.StateMachine.Canonical.received_event_nonempty_decode_projection m4 e4 dr5 /\
            Seq.equal ts4 (B.append ds5 ts5) /\ Seq.equal tr4 (B.append dr5 tr5) /\
            SMReplay.conn_events_received_decode_replay m5 [] ts5 tr5 p
          returns
            (p.CS.model_config == cfg /\
             p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
             p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared /\
             p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
          with _. ()
        )
      )
    )
  )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60 --split_queries always"
let lemma_client_prefix_model_sent
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
        p.CS.model_config == cfg /\
        p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
        p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
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
  PWReplay.lemma_conn_events_sent_seal_replay_head m0 e0 r1 ps pr p;
  eliminate exists (m1:CS.connection_model) (ds1 dr1 ts1 tr1:B.bytes).
    CS.legal_event m0 e0 /\ CS.step_model m0 e0 == Some m1 /\
    CS.event_raw_delta_legal m0 e0 ds1 dr1 /\
    TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m0 e0 ds1 /\
    Seq.equal ps (B.append ds1 ts1) /\ Seq.equal pr (B.append dr1 tr1) /\
    SMReplay.conn_events_sent_seal_replay m1 r1 ts1 tr1 p
  returns
    (p.CS.model_config == cfg /\
     p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
     p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
     p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
  with _.
  (
    PWReplay.lemma_conn_events_sent_seal_replay_head m1 e1 r2 ts1 tr1 p;
    eliminate exists (m2:CS.connection_model) (ds2 dr2 ts2 tr2:B.bytes).
      CS.legal_event m1 e1 /\ CS.step_model m1 e1 == Some m2 /\
      CS.event_raw_delta_legal m1 e1 ds2 dr2 /\
      TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m1 e1 ds2 /\
      Seq.equal ts1 (B.append ds2 ts2) /\ Seq.equal tr1 (B.append dr2 tr2) /\
      SMReplay.conn_events_sent_seal_replay m2 r2 ts2 tr2 p
    returns
      (p.CS.model_config == cfg /\
       p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
       p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
       p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
    with _.
    (
      PWReplay.lemma_conn_events_sent_seal_replay_head m2 e2 r3 ts2 tr2 p;
      eliminate exists (m3:CS.connection_model) (ds3 dr3 ts3 tr3:B.bytes).
        CS.legal_event m2 e2 /\ CS.step_model m2 e2 == Some m3 /\
        CS.event_raw_delta_legal m2 e2 ds3 dr3 /\
        TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m2 e2 ds3 /\
        Seq.equal ts2 (B.append ds3 ts3) /\ Seq.equal tr2 (B.append dr3 tr3) /\
        SMReplay.conn_events_sent_seal_replay m3 r3 ts3 tr3 p
      returns
        (p.CS.model_config == cfg /\
         p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
         p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
         p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
      with _.
      (
        PWReplay.lemma_conn_events_sent_seal_replay_head m3 e3 [] ts3 tr3 p;
        eliminate exists (m4:CS.connection_model) (ds4 dr4 ts4 tr4:B.bytes).
          CS.legal_event m3 e3 /\ CS.step_model m3 e3 == Some m4 /\
          CS.event_raw_delta_legal m3 e3 ds4 dr4 /\
          TLS13.Spec.StateMachine.Canonical.sent_event_nonempty_seal_projection m3 e3 ds4 /\
          Seq.equal ts3 (B.append ds4 ts4) /\ Seq.equal tr3 (B.append dr4 tr4) /\
          SMReplay.conn_events_sent_seal_replay m4 [] ts4 tr4 p
        returns
          (p.CS.model_config == cfg /\
           p.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
           p.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared /\
           p.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh)
        with _. ()
      )
    )
  )
#pop-options


(* ---- client-READ region via SENT-seal (for redundant flight head) ---- *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_cr_region_preserves_read_installed_sent
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        CReg.client_read_installed m material /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures CReg.client_read_installed final material)
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = CReg.install_of_client_hs ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    returns CReg.client_read_installed final material
    with _.
    ( CReg.lemma_client_install_step_preserves m install model1 material;
      lemma_cr_region_preserves_read_installed_sent model1 rest tail_sent tail_received final material )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
#restart-solver
let rec lemma_cr_region_read_installed_sent
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
        (exists (er:CS.conn_event). L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
        SMReplay.conn_events_sent_seal_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). CReg.client_read_installed final material))
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = CReg.install_of_client_hs ev in
    PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.sent_event_nonempty_seal_projection m ev delta_sent /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
    returns (exists (material:CS.traffic_key_material). CReg.client_read_installed final material)
    with _.
    ( if install.CS.install_direction = CS.TrafficRead
      then
        (CReg.lemma_client_read_install_establishes m install model1;
         lemma_cr_region_preserves_read_installed_sent
           model1 rest tail_sent tail_received final install.CS.install_material)
      else
        (CReg.lemma_client_install_step_preserves_control m install model1;
         eliminate exists (er:CS.conn_event).
           L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er
         returns (exists (er2:CS.conn_event). L.memP er2 rest /\ CCShape.is_client_hs_install_dir CS.TrafficRead er2)
         with _. ();
         lemma_cr_region_read_installed_sent model1 rest tail_sent tail_received final) )
#pop-options

(* ---- server-WRITE region via RECEIVED-decode (for redundant flight head) ---- *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_sw_region_preserves_write_installed_recv
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model) (material:CS.traffic_key_material)
  : Lemma
      (requires
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        server_write_installed m material /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures server_write_installed final material)
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns server_write_installed final material
    with _.
    ( lemma_server_install_step_preserves m install model1 material;
      lemma_sw_region_preserves_write_installed_recv model1 rest tail_sent tail_received final material )
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_sw_region_write_installed_recv
  (m:CS.connection_model) (region:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true) /\
        (exists (ew:CS.conn_event). L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew) /\
        SMReplay.conn_events_received_decode_replay m region rs rr final)
      (ensures (exists (material:CS.traffic_key_material). server_write_installed final material))
      (decreases region)
= match region with
  | [] -> ()
  | ev :: rest ->
    let install = install_of_server_hs ev in
    PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
    eliminate exists (model1:CS.connection_model)
                     (delta_sent delta_received tail_sent tail_received:B.bytes).
      CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
      CS.event_raw_delta_legal m ev delta_sent delta_received /\
      Canonical.received_event_nonempty_decode_projection m ev delta_received /\
      Seq.equal rs (B.append delta_sent tail_sent) /\
      Seq.equal rr (B.append delta_received tail_received) /\
      SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
    returns (exists (material:CS.traffic_key_material). server_write_installed final material)
    with _.
    ( if install.CS.install_payload.CS.install_direction = CS.TrafficWrite
      then
        (lemma_server_write_install_establishes m install model1;
         lemma_sw_region_preserves_write_installed_recv
           model1 rest tail_sent tail_received final install.CS.install_payload.CS.install_material)
      else
        (lemma_server_install_step_preserves_control m install model1;
         eliminate exists (ew:CS.conn_event).
           L.memP ew region /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew
         returns (exists (ew2:CS.conn_event). L.memP ew2 rest /\ SCShape.is_server_hs_install_dir CS.TrafficWrite ew2)
         with _. ();
         lemma_sw_region_write_installed_recv model1 rest tail_sent tail_received final) )
#pop-options

(* ---- opposite-direction redundant prepends for the flight install heads ---- *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_client_read_install_sent
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CReg.client_read_installed m material /\
        SMReplay.conn_events_sent_seal_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_sent_seal_replay
          m (RI.client_hs_read_install_event material :: rest) rs rr final)
= RI.lemma_redundant_client_hs_read_install_identity m material;
  let ev = RI.client_hs_read_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (Canonical.sent_event_nonempty_seal_projection m ev B.empty);
  PWReplay.lemma_conn_events_sent_seal_replay_cons
    m ev rest rs rr final m B.empty B.empty rs rr
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_server_write_install_received
  (m:CS.connection_model) (material:CS.traffic_key_material)
  (rest:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        server_write_installed m material /\
        SMReplay.conn_events_received_decode_replay m rest rs rr final)
      (ensures
        SMReplay.conn_events_received_decode_replay
          m (RI.server_hs_write_install_event material :: rest) rs rr final)
= RI.lemma_redundant_server_hs_write_install_identity m material;
  let ev = RI.server_hs_write_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (Canonical.received_event_nonempty_decode_projection m ev B.empty);
  PWReplay.lemma_conn_events_received_decode_replay_cons
    m ev rest rs rr final m B.empty B.empty rs rr
#pop-options

(* ================================================================== *)
(* STEP 1 — side packages (client SENT-seal, server RECEIVED-decode).  *)
(* ================================================================== *)

let client_flight_tail
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (validate:CS.local_event) (cv:GCV.certificateVerify) (verifysig:CS.local_event)
  (sf:GFin.finished) (rest:list CS.conn_event) : list CS.conn_event =
  recv_ev (M.EncryptedExtensions ee) ::
  recv_ev (M.Certificate cert) ::
  CS.ConnLocalEvent validate ::
  recv_ev (M.CertificateVerify cv) ::
  CS.ConnLocalEvent verifysig ::
  recv_ev (M.Finished sf) :: rest

let server_flight_tail
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (rest:list CS.conn_event) : list CS.conn_event =
  sent_ev (M.EncryptedExtensions ee) ::
  sent_ev (M.Certificate cert) ::
  CS.ConnLocalEvent cv_local ::
  sent_ev (M.CertificateVerify cv) ::
  sent_ev (M.Finished sf) :: rest

(* CH-suffix alignment: from the paired byte streams, the client's post-CH
   SENT bytes equal the server's post-CH RECEIVED bytes. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80 --split_queries always"
let lemma_ch_flight_align
  (ch_c ch_s:GCH.clientHello)
  (cs sr:B.bytes)
  (fl_sent fl_recv d_ch:B.bytes)
  : Lemma
      (requires
        (let ch_c_ser = W.serialize_handshake (M.ClientHello ch_c) in
         B.length ch_c_ser <= 16640 /\
         Seq.equal cs (B.append (W.serialize_record T.Handshake ch_c_ser) fl_sent) /\
         Seq.equal sr (B.append d_ch fl_recv) /\
         Seq.equal cs sr /\
         CS.received_cleartext_tls_message_raw
           (M.TlsHandshake (M.ClientHello ch_s)) d_ch))
      (ensures Seq.equal fl_sent fl_recv)
=
  let ch_c_ser = W.serialize_handshake (M.ClientHello ch_c) in
  let front_c = W.serialize_record T.Handshake ch_c_ser in
  let l1 = B.length front_c in
  WFL.lemma_parse_record_wire_serialize_record T.Handshake ch_c_ser;
  Seq.lemma_eq_elim cs (B.append front_c fl_sent);
  Seq.lemma_eq_elim cs sr;
  Seq.lemma_eq_elim sr (B.append d_ch fl_recv);
  slice_prefix front_c fl_sent;
  Seq.lemma_eq_elim (Seq.slice cs 0 l1) front_c;
  WRD.lemma_parse_record_wire_from_prefix cs T.Handshake ch_c_ser l1;
  eliminate exists (frag:M.sealed_record).
    W.parse_record_wire d_ch == Some (T.Handshake, frag, B.length d_ch) /\
    W.parse_tls_message T.Handshake frag == Some (M.TlsHandshake (M.ClientHello ch_s))
  returns Seq.equal fl_sent fl_recv
  with _.
  (
    let ld = B.length d_ch in
    slice_prefix d_ch fl_recv;
    Seq.lemma_eq_elim (Seq.slice cs 0 ld) d_ch;
    WRD.lemma_parse_record_wire_from_prefix cs T.Handshake frag ld;
    assert (W.parse_record_wire cs == Some (T.Handshake, ch_c_ser, l1));
    assert (W.parse_record_wire cs == Some (T.Handshake, frag, ld));
    assert (ld == l1);
    Seq.lemma_eq_elim d_ch front_c;
    (* cs == front_c ++ fl_sent == front_c ++ fl_recv -> cancel *)
    Seq.lemma_append_inj front_c fl_sent front_c fl_recv
  )
#pop-options

(* ---------------- CLIENT side package (SENT-seal) ---------------- *)

let client_pkg (s:sysp)
  (mc:CS.connection_model)
  (mat_read mat_write:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (validate:CS.local_event) (cv:GCV.certificateVerify) (verifysig:CS.local_event)
  (sf:GFin.finished) (client_rest:list CS.conn_event)
  (fl_sent fl_recv:B.bytes) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (sh_rest:B.bytes) : prop =
  SMReplay.conn_events_sent_seal_replay mc
    (RI.client_hs_read_install_event mat_read ::
     client_flight_tail ee cert validate cv verifysig sf client_rest)
    fl_sent fl_recv s.client.CS.cs_model /\
  client_write_installed mc mat_write /\
  CReg.client_read_installed mc mat_read /\
  Some? mc.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    s.client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  mc.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh /\
  Seq.equal s.client.CS.cs_wire_log.CL.raw_sent
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch))) fl_sent) /\
  B.length (W.serialize_handshake (M.ClientHello ch)) <= 16640 /\
  Seq.equal s.client.CS.cs_wire_log.CL.raw_received
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) sh_rest) /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640

let client_pkg_exists (s:sysp) : prop =
  exists (mc:CS.connection_model)
    (mat_read mat_write:CS.traffic_key_material)
    (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
    (validate:CS.local_event) (cv:GCV.certificateVerify) (verifysig:CS.local_event)
    (sf:GFin.finished) (client_rest:list CS.conn_event)
    (fl_sent fl_recv:B.bytes) (ch:GCH.clientHello) (sh:GSH.serverHello)
    (sh_rest:B.bytes).
    client_pkg s mc mat_read mat_write ee cert validate cv verifysig sf client_rest
      fl_sent fl_recv ch sh sh_rest

(* ---------------- SERVER side package (RECEIVED-decode) ---------------- *)

let server_pkg (s:sysp)
  (ms:CS.connection_model)
  (mat_write mat_read:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (server_rest:list CS.conn_event)
  (fl_sent fl_recv:B.bytes) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (d_ch rest_ss:B.bytes) : prop =
  SMReplay.conn_events_received_decode_replay ms
    (RI.server_hs_write_install_event mat_write ::
     server_flight_tail ee cert cv_local cv sf server_rest)
    fl_sent fl_recv s.server.CS.cs_model /\
  server_read_installed ms mat_read /\
  server_write_installed ms mat_write /\
  Some? ms.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
  ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
    s.server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
  ms.CS.model_handshake.CS.hs_transcript == server_prefix_transcript ch sh /\
  SCShape.log_has_no_received_ccs server_rest /\
  CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) d_ch /\
  Seq.equal s.server.CS.cs_wire_log.CL.raw_received (B.append d_ch fl_recv) /\
  Seq.equal s.server.CS.cs_wire_log.CL.raw_sent
    (B.append (W.serialize_record T.Handshake (W.serialize_handshake (M.ServerHello sh))) rest_ss) /\
  B.length (W.serialize_handshake (M.ServerHello sh)) <= 16640

let server_pkg_exists (s:sysp) : prop =
  exists (ms:CS.connection_model)
    (mat_write mat_read:CS.traffic_key_material)
    (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
    (cv_local:CS.local_event) (cv:GCV.certificateVerify)
    (sf:GFin.finished) (server_rest:list CS.conn_event)
    (fl_sent fl_recv:B.bytes) (ch:GCH.clientHello) (sh:GSH.serverHello)
    (d_ch rest_ss:B.bytes).
    server_pkg s ms mat_write mat_read ee cert cv_local cv sf server_rest
      fl_sent fl_recv ch sh d_ch rest_ss

(* ================================================================== *)
(* STEP 1 lemmas — build the two side packages.                        *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_client_install_empty_sent (e:CS.conn_event)
  : Lemma (requires CCShape.is_client_hs_install e == true)
          (ensures Region.is_empty_sent_ev e == true)
  = ()

let lemma_forall_client_install_empty_sent (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true))
      (ensures L.for_all Region.is_empty_sent_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> Region.is_empty_sent_ev x == true
    with (introduce L.memP x region ==> Region.is_empty_sent_ev x == true
          with _. lemma_client_install_empty_sent x);
    L.for_all_mem Region.is_empty_sent_ev region

let lemma_server_install_empty_recv (e:CS.conn_event)
  : Lemma (requires SCShape.is_server_hs_install e == true)
          (ensures Region.is_empty_recv_ev e == true)
  = ()

let lemma_forall_server_install_empty_recv (region:list CS.conn_event)
  : Lemma
      (requires (forall (e:CS.conn_event). L.memP e region ==> SCShape.is_server_hs_install e == true))
      (ensures L.for_all Region.is_empty_recv_ev region)
  = introduce forall (x:CS.conn_event). L.memP x region ==> Region.is_empty_recv_ev x == true
    with (introduce L.memP x region ==> Region.is_empty_recv_ev x == true
          with _. lemma_server_install_empty_recv x);
    L.for_all_mem Region.is_empty_recv_ev region
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 400 --split_queries always"
let lemma_client_side_cf (s:sysp)
  : Lemma (requires client_finished_bridge_inputs s.client s.server)
          (ensures client_pkg_exists s)
  =
  let cfg_c = s.client.CS.cs_model.CS.model_config in
  let cs = s.client.CS.cs_wire_log.CL.raw_sent in
  let cr = s.client.CS.cs_wire_log.CL.raw_received in
  let final = s.client.CS.cs_model in
  let m0 = CS.initial_model cfg_c in
  lemma_client_replays s;
  CNoCcs.lemma_no_received_ccs_from_pairing_client s.client s.server;
  lemma_appdata_client s.client;
  assert (WStep.client_reachable (CS.initial cfg_c) s.client);
  assert (cfg_c.CS.config_role == CS.ClientEndpoint);
  assert (CCShape.log_has_no_received_ccs s.client.CS.cs_event_log);
  SFInv.lemma_client_normalized_appdata_exact_spine_from_replays_and_pairing
    s.client s.server;
  eliminate exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
                   (client_shared:C.x25519_shared_secret)
                   (region:list CS.conn_event)
                   (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                   (cv_validate:CS.local_event) (cv:GCV.certificateVerify)
                   (cv_verify:CS.local_event) (sf:GFin.finished)
                   (raw_ee raw_cert raw_cv raw_sf:CS.conn_event)
                   (tail:list CS.conn_event).
    PWHead.received_handshake_head_normal_form (M.EncryptedExtensions ee) raw_ee /\
    PWHead.received_handshake_head_normal_form (M.Certificate cert) raw_cert /\
    PWHead.received_handshake_head_normal_form (M.CertificateVerify cv) raw_cv /\
    PWHead.received_handshake_head_normal_form (M.Finished sf) raw_sf /\
    (forall (e:CS.conn_event). L.memP e region ==> CCShape.is_client_hs_install e == true) /\
    (exists (er:CS.conn_event). L.memP er region /\ CCShape.is_client_hs_install_dir CS.TrafficRead er) /\
    (exists (ew:CS.conn_event). L.memP ew region /\ CCShape.is_client_hs_install_dir CS.TrafficWrite ew) /\
    s.client.CS.cs_event_log ==
      L.append
        (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
        (L.append region
           (raw_ee ::
            raw_cert ::
            CS.ConnLocalEvent cv_validate ::
            raw_cv ::
            CS.ConnLocalEvent cv_verify ::
            raw_sf ::
            tail))
  returns client_pkg_exists s
  with _.
  (
    let prefix = PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared in
    (* The log carries the RAW flight; the network-event spine [cflight] is its
       normal form, and the two denote the same replay
       ([PWNorm.lemma_normalize_flight_sent]). *)
    let raw_cflight =
      raw_ee :: raw_cert :: CS.ConnLocalEvent cv_validate ::
      raw_cv :: CS.ConnLocalEvent cv_verify :: raw_sf :: tail in
    let cflight = client_flight_tail ee cert cv_validate cv cv_verify sf tail in
    let suffix = L.append region raw_cflight in
    assert (s.client.CS.cs_event_log == L.append prefix suffix);
    (* ---- SENT-seal branch ---- *)
    lemma_replay_cong_sent m0 s.client.CS.cs_event_log (L.append prefix suffix) cs cr final;
    PWReplay.lemma_conn_events_sent_seal_replay_append_split m0 prefix suffix cs cr final;
    eliminate exists (mp:CS.connection_model)
                     (ps_sent ps_recv suf_sent suf_recv:B.bytes).
      Seq.equal cs (B.append ps_sent suf_sent) /\
      Seq.equal cr (B.append ps_recv suf_recv) /\
      SMReplay.conn_events_sent_seal_replay m0 prefix ps_sent ps_recv mp /\
      SMReplay.conn_events_sent_seal_replay mp suffix suf_sent suf_recv final
    returns client_pkg_exists s
    with _.
    (
      lemma_client_prefix_model_sent cfg_c start ch sh client_shared ps_sent ps_recv mp;
      lemma_client_prefix_sent_bytes cfg_c start ch sh client_shared ps_sent ps_recv mp;
      PWReplay.lemma_conn_events_sent_seal_replay_append_split mp region raw_cflight suf_sent suf_recv final;
      eliminate exists (mc:CS.connection_model)
                       (rg_sent rg_recv fl_sent fl_recv:B.bytes).
        Seq.equal suf_sent (B.append rg_sent fl_sent) /\
        Seq.equal suf_recv (B.append rg_recv fl_recv) /\
        SMReplay.conn_events_sent_seal_replay mp region rg_sent rg_recv mc /\
        SMReplay.conn_events_sent_seal_replay mc raw_cflight fl_sent fl_recv final
      returns client_pkg_exists s
      with _.
      (
        PWNorm.lemma_normalize_flight_sent mc
          (M.EncryptedExtensions ee) (M.Certificate cert)
          (M.CertificateVerify cv) (M.Finished sf)
          raw_ee raw_cert raw_cv raw_sf
          cv_validate cv_verify tail
          fl_sent fl_recv final;
        assert (PWNorm.normal_flight
                  (M.EncryptedExtensions ee) (M.Certificate cert)
                  (M.CertificateVerify cv) (M.Finished sf)
                  cv_validate cv_verify tail
                == cflight);
        lemma_replay_cong_sent mc
          (PWNorm.normal_flight
            (M.EncryptedExtensions ee) (M.Certificate cert)
            (M.CertificateVerify cv) (M.Finished sf)
            cv_validate cv_verify tail)
          cflight fl_sent fl_recv final;
        lemma_forall_client_install_empty_sent region;
        Region.lemma_empty_sent_tail_collapses mp region rg_sent rg_recv mc;
        lemma_cw_region_write_installed mp region rg_sent rg_recv mc;
        lemma_cr_region_read_installed_sent mp region rg_sent rg_recv mc;
        eliminate exists (mat_write:CS.traffic_key_material). client_write_installed mc mat_write
        returns client_pkg_exists s
        with _.
        (
          eliminate exists (mat_read:CS.traffic_key_material). CReg.client_read_installed mc mat_read
          returns client_pkg_exists s
          with _.
          (
            lemma_sent_replay_preserves_secrets mp region rg_sent rg_recv mc;
            lemma_sent_replay_preserves_secrets mc cflight fl_sent fl_recv final;
            lemma_forall_install_key_c region;
            lemma_region_preserves_transcript_sent mp region rg_sent rg_recv mc;
            lemma_prepend_redundant_client_read_install_sent mc mat_read cflight fl_sent fl_recv final;
            (* byte accounting: cs == record(CH) ++ fl_sent *)
            Seq.lemma_eq_elim rg_sent B.empty;
            Seq.append_empty_l fl_sent;
            Seq.lemma_eq_elim suf_sent fl_sent;
            Seq.lemma_eq_elim ps_sent
              (W.serialize_record T.Handshake (W.serialize_handshake (M.ClientHello ch)));
            Seq.lemma_eq_elim cs (B.append ps_sent suf_sent);
            (* ---- RECEIVED-decode branch (SH bytes) ---- *)
            lemma_replay_cong_recv m0 s.client.CS.cs_event_log (L.append prefix suffix) cs cr final;
            PWReplay.lemma_conn_events_received_decode_replay_append_split m0 prefix suffix cs cr final;
            eliminate exists (mp2:CS.connection_model)
                             (ps_sent2 ps_recv2 suf_sent2 suf_recv2:B.bytes).
              Seq.equal cs (B.append ps_sent2 suf_sent2) /\
              Seq.equal cr (B.append ps_recv2 suf_recv2) /\
              SMReplay.conn_events_received_decode_replay m0 prefix ps_sent2 ps_recv2 mp2 /\
              SMReplay.conn_events_received_decode_replay mp2 suffix suf_sent2 suf_recv2 final
            returns client_pkg_exists s
            with _.
            (
              lemma_client_prefix_received_bytes cfg_c start ch sh client_shared ps_sent2 ps_recv2 mp2;
              Seq.lemma_eq_elim cr (B.append ps_recv2 suf_recv2);
              introduce exists (mc0:CS.connection_model)
                (mat_read0 mat_write0:CS.traffic_key_material)
                (ee0:GEE.encryptedExtensions) (cert0:GCert.certificate)
                (validate0:CS.local_event) (cv0:GCV.certificateVerify) (verifysig0:CS.local_event)
                (sf0:GFin.finished) (client_rest0:list CS.conn_event)
                (fl_sent0 fl_recv0:B.bytes) (ch0:GCH.clientHello) (sh0:GSH.serverHello)
                (sh_rest0:B.bytes).
                client_pkg s mc0 mat_read0 mat_write0 ee0 cert0 validate0 cv0 verifysig0 sf0 client_rest0
                  fl_sent0 fl_recv0 ch0 sh0 sh_rest0
              with mc mat_read mat_write ee cert cv_validate cv cv_verify sf tail
                   fl_sent fl_recv ch sh suf_recv2
              and ()
            )
          )
        )
      )
    )
  )
#pop-options

(* A suffix of a CCS-free log is CCS-free. *)
let lemma_no_ccs_of_suffix (log a b:list CS.conn_event)
  : Lemma (requires SCShape.log_has_no_received_ccs log /\ log == L.append a b)
          (ensures SCShape.log_has_no_received_ccs b)
  = introduce forall (e:CS.conn_event). L.memP e b ==> SCShape.is_received_ccs e == false
    with introduce _ ==> _ with _.
      ( L.append_memP a b e )

(* [tail] is a suffix of [server_flight_tail ... tail]. *)
let lemma_no_ccs_server_flight_tail
  (log region:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (tail:list CS.conn_event)
  : Lemma
      (requires SCShape.log_has_no_received_ccs log /\
                log == L.append region (server_flight_tail ee cert cv_local cv sf tail))
      (ensures SCShape.log_has_no_received_ccs tail)
  = lemma_no_ccs_of_suffix log region (server_flight_tail ee cert cv_local cv sf tail);
    let sflight = server_flight_tail ee cert cv_local cv sf tail in
    introduce forall (e:CS.conn_event). L.memP e tail ==> SCShape.is_received_ccs e == false
    with introduce _ ==> _ with _.
      ( assert (L.memP e sflight) )

#push-options "--fuel 2 --ifuel 2 --z3rlimit 150 --split_queries always"
let lemma_server_side_cf (s:sysp)
  : Lemma (requires client_finished_bridge_inputs s.client s.server)
          (ensures server_pkg_exists s)
  =
  let cfg_s = s.server.CS.cs_model.CS.model_config in
  let ss = s.server.CS.cs_wire_log.CL.raw_sent in
  let sr = s.server.CS.cs_wire_log.CL.raw_received in
  let final = s.server.CS.cs_model in
  let m0 = CS.initial_model cfg_s in
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
  returns server_pkg_exists s
  with _.
  (
    let prefix = PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh in
    let sflight = server_flight_tail ee cert cv_local cv sf tail in
    let suffix = L.append region sflight in
    assert (s.server.CS.cs_event_log == L.append prefix suffix);
    (* ---- RECEIVED-decode branch (main) ---- *)
    lemma_replay_cong_recv m0 s.server.CS.cs_event_log (L.append prefix suffix) ss sr final;
    PWReplay.lemma_conn_events_received_decode_replay_append_split m0 prefix suffix ss sr final;
    eliminate exists (mp:CS.connection_model)
                     (ps_sent ps_recv suf_sent suf_recv:B.bytes).
      Seq.equal ss (B.append ps_sent suf_sent) /\
      Seq.equal sr (B.append ps_recv suf_recv) /\
      SMReplay.conn_events_received_decode_replay m0 prefix ps_sent ps_recv mp /\
      SMReplay.conn_events_received_decode_replay mp suffix suf_sent suf_recv final
    returns server_pkg_exists s
    with _.
    (
      lemma_server_prefix_model_recv cfg_s ch selection server_shared sh ps_sent ps_recv mp;
      lemma_server_prefix_received_bytes cfg_s ch selection server_shared sh ps_sent ps_recv mp;
      PWReplay.lemma_conn_events_received_decode_replay_append_split mp region sflight suf_sent suf_recv final;
      eliminate exists (ms:CS.connection_model)
                       (rg_sent rg_recv fl_sent fl_recv:B.bytes).
        Seq.equal suf_sent (B.append rg_sent fl_sent) /\
        Seq.equal suf_recv (B.append rg_recv fl_recv) /\
        SMReplay.conn_events_received_decode_replay mp region rg_sent rg_recv ms /\
        SMReplay.conn_events_received_decode_replay ms sflight fl_sent fl_recv final
      returns server_pkg_exists s
      with _.
      (
        lemma_forall_server_install_empty_recv region;
        Region.lemma_empty_recv_tail_collapses mp region rg_sent rg_recv ms;
        lemma_sr_region_read_installed mp region rg_sent rg_recv ms;
        lemma_sw_region_write_installed_recv mp region rg_sent rg_recv ms;
        eliminate exists (mat_read:CS.traffic_key_material). server_read_installed ms mat_read
        returns server_pkg_exists s
        with _.
        (
          eliminate exists (mat_write:CS.traffic_key_material). server_write_installed ms mat_write
          returns server_pkg_exists s
          with _.
          (
            lemma_received_replay_preserves_secrets mp region rg_sent rg_recv ms;
            lemma_received_replay_preserves_secrets ms sflight fl_sent fl_recv final;
            lemma_forall_install_key region;
            lemma_region_preserves_transcript_received mp region rg_sent rg_recv ms;
            lemma_prepend_redundant_server_write_install_received ms mat_write sflight fl_sent fl_recv final;
            (* byte accounting: sr == d_ch ++ fl_recv, d_ch == ps_recv *)
            Seq.lemma_eq_elim rg_recv B.empty;
            Seq.append_empty_l fl_recv;
            Seq.lemma_eq_elim suf_recv fl_recv;
            Seq.lemma_eq_elim sr (B.append ps_recv suf_recv);
            (* ---- SENT-seal branch (SH bytes) ---- *)
            lemma_replay_cong_sent m0 s.server.CS.cs_event_log (L.append prefix suffix) ss sr final;
            PWReplay.lemma_conn_events_sent_seal_replay_append_split m0 prefix suffix ss sr final;
            eliminate exists (mp2:CS.connection_model)
                             (ps_sent2 ps_recv2 suf_sent2 suf_recv2:B.bytes).
              Seq.equal ss (B.append ps_sent2 suf_sent2) /\
              Seq.equal sr (B.append ps_recv2 suf_recv2) /\
              SMReplay.conn_events_sent_seal_replay m0 prefix ps_sent2 ps_recv2 mp2 /\
              SMReplay.conn_events_sent_seal_replay mp2 suffix suf_sent2 suf_recv2 final
            returns server_pkg_exists s
            with _.
            (
              lemma_server_prefix_sent_bytes cfg_s ch selection server_shared sh ps_sent2 ps_recv2 mp2;
              Seq.lemma_eq_elim ss (B.append ps_sent2 suf_sent2);
              lemma_no_ccs_of_suffix s.server.CS.cs_event_log prefix suffix;
              lemma_no_ccs_server_flight_tail suffix region ee cert cv_local cv sf tail;
              introduce exists (ms0:CS.connection_model)
                (mat_write0 mat_read0:CS.traffic_key_material)
                (ee0:GEE.encryptedExtensions) (cert0:GCert.certificate)
                (cv_local0:CS.local_event) (cv0:GCV.certificateVerify)
                (sf0:GFin.finished) (server_rest0:list CS.conn_event)
                (fl_sent0 fl_recv0:B.bytes) (ch0:GCH.clientHello) (sh0:GSH.serverHello)
                (d_ch0 rest_ss0:B.bytes).
                server_pkg s ms0 mat_write0 mat_read0 ee0 cert0 cv_local0 cv0 sf0 server_rest0
                  fl_sent0 fl_recv0 ch0 sh0 d_ch0 rest_ss0
              with ms mat_write mat_read ee cert cv_local cv sf tail
                   fl_sent fl_recv ch sh ps_recv suf_sent2
              and ()
            )
          )
        )
      )
    )
  )
#pop-options

(* ================================================================== *)
(* STEP 2/3 — flight peeling chains + producer 1886 call.              *)
(* ================================================================== *)

let client_flight_chain
  (mc final_c:CS.connection_model) (mat_read:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event) (cv:GCV.certificateVerify) (cv_verify:CS.local_event)
  (sf:GFin.finished) (client_rest:list CS.conn_event)
  (ci c0 c1 cas c2 cvs c3:CS.connection_model)
  (ct_sent ct_recv:B.bytes) : prop =
  CS.step_model mc (RI.client_hs_read_install_event mat_read) == Some ci /\
  CS.step_model ci (recv_ev (M.EncryptedExtensions ee)) == Some c0 /\
  CS.step_model c0 (recv_ev (M.Certificate cert)) == Some c1 /\
  CS.legal_event c1 (CS.ConnLocalEvent cv_validate) /\
  CS.step_model c1 (CS.ConnLocalEvent cv_validate) == Some cas /\
  CS.step_model cas (recv_ev (M.CertificateVerify cv)) == Some c2 /\
  CS.legal_event c2 (CS.ConnLocalEvent cv_verify) /\
  CS.step_model c2 (CS.ConnLocalEvent cv_verify) == Some cvs /\
  CS.step_model cvs (recv_ev (M.Finished sf)) == Some c3 /\
  SMReplay.conn_events_sent_seal_replay c3 client_rest ct_sent ct_recv final_c

let client_chain_exists
  (mc final_c:CS.connection_model) (mat_read:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event) (cv:GCV.certificateVerify) (cv_verify:CS.local_event)
  (sf:GFin.finished) (client_rest:list CS.conn_event) : prop =
  exists (ci c0 c1 cas c2 cvs c3:CS.connection_model) (ct_sent ct_recv:B.bytes).
    client_flight_chain mc final_c mat_read ee cert cv_validate cv cv_verify sf client_rest
      ci c0 c1 cas c2 cvs c3 ct_sent ct_recv

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120 --split_queries always"
let lemma_peel_client_flight
  (mc final_c:CS.connection_model) (mat_read:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event) (cv:GCV.certificateVerify) (cv_verify:CS.local_event)
  (sf:GFin.finished) (client_rest:list CS.conn_event)
  (fl_sent fl_recv:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay mc
          (RI.client_hs_read_install_event mat_read ::
           client_flight_tail ee cert cv_validate cv cv_verify sf client_rest)
          fl_sent fl_recv final_c)
      (ensures
        client_chain_exists mc final_c mat_read ee cert cv_validate cv cv_verify sf client_rest)
  =
  let goal = client_chain_exists mc final_c mat_read ee cert cv_validate cv cv_verify sf client_rest in
  let e_i = RI.client_hs_read_install_event mat_read in
  let e0 = recv_ev (M.EncryptedExtensions ee) in
  let e1 = recv_ev (M.Certificate cert) in
  let ea = CS.ConnLocalEvent cv_validate in
  let e2 = recv_ev (M.CertificateVerify cv) in
  let ev = CS.ConnLocalEvent cv_verify in
  let e3 = recv_ev (M.Finished sf) in
  let r_i = e0 :: e1 :: ea :: e2 :: ev :: e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head mc e_i r_i fl_sent fl_recv final_c;
  eliminate exists (ci:CS.connection_model) (dis dir tis tir:B.bytes).
    CS.legal_event mc e_i /\ CS.step_model mc e_i == Some ci /\
    CS.event_raw_delta_legal mc e_i dis dir /\
    Canonical.sent_event_nonempty_seal_projection mc e_i dis /\
    Seq.equal fl_sent (B.append dis tis) /\ Seq.equal fl_recv (B.append dir tir) /\
    SMReplay.conn_events_sent_seal_replay ci r_i tis tir final_c
  returns goal
  with _. (
  let r0 = e1 :: ea :: e2 :: ev :: e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head ci e0 r0 tis tir final_c;
  eliminate exists (c0:CS.connection_model) (d0s d0r t0s t0r:B.bytes).
    CS.legal_event ci e0 /\ CS.step_model ci e0 == Some c0 /\
    CS.event_raw_delta_legal ci e0 d0s d0r /\
    Canonical.sent_event_nonempty_seal_projection ci e0 d0s /\
    Seq.equal tis (B.append d0s t0s) /\ Seq.equal tir (B.append d0r t0r) /\
    SMReplay.conn_events_sent_seal_replay c0 r0 t0s t0r final_c
  returns goal
  with _. (
  let r1 = ea :: e2 :: ev :: e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head c0 e1 r1 t0s t0r final_c;
  eliminate exists (c1:CS.connection_model) (d1s d1r t1s t1r:B.bytes).
    CS.legal_event c0 e1 /\ CS.step_model c0 e1 == Some c1 /\
    CS.event_raw_delta_legal c0 e1 d1s d1r /\
    Canonical.sent_event_nonempty_seal_projection c0 e1 d1s /\
    Seq.equal t0s (B.append d1s t1s) /\ Seq.equal t0r (B.append d1r t1r) /\
    SMReplay.conn_events_sent_seal_replay c1 r1 t1s t1r final_c
  returns goal
  with _. (
  let ra = e2 :: ev :: e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head c1 ea ra t1s t1r final_c;
  eliminate exists (cas:CS.connection_model) (das dar tas tar:B.bytes).
    CS.legal_event c1 ea /\ CS.step_model c1 ea == Some cas /\
    CS.event_raw_delta_legal c1 ea das dar /\
    Canonical.sent_event_nonempty_seal_projection c1 ea das /\
    Seq.equal t1s (B.append das tas) /\ Seq.equal t1r (B.append dar tar) /\
    SMReplay.conn_events_sent_seal_replay cas ra tas tar final_c
  returns goal
  with _. (
  let r2 = ev :: e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head cas e2 r2 tas tar final_c;
  eliminate exists (c2:CS.connection_model) (d2s d2r t2s t2r:B.bytes).
    CS.legal_event cas e2 /\ CS.step_model cas e2 == Some c2 /\
    CS.event_raw_delta_legal cas e2 d2s d2r /\
    Canonical.sent_event_nonempty_seal_projection cas e2 d2s /\
    Seq.equal tas (B.append d2s t2s) /\ Seq.equal tar (B.append d2r t2r) /\
    SMReplay.conn_events_sent_seal_replay c2 r2 t2s t2r final_c
  returns goal
  with _. (
  let rv = e3 :: client_rest in
  PWReplay.lemma_conn_events_sent_seal_replay_head c2 ev rv t2s t2r final_c;
  eliminate exists (cvs:CS.connection_model) (dvs dvr tvs tvr:B.bytes).
    CS.legal_event c2 ev /\ CS.step_model c2 ev == Some cvs /\
    CS.event_raw_delta_legal c2 ev dvs dvr /\
    Canonical.sent_event_nonempty_seal_projection c2 ev dvs /\
    Seq.equal t2s (B.append dvs tvs) /\ Seq.equal t2r (B.append dvr tvr) /\
    SMReplay.conn_events_sent_seal_replay cvs rv tvs tvr final_c
  returns goal
  with _. (
  PWReplay.lemma_conn_events_sent_seal_replay_head cvs e3 client_rest tvs tvr final_c;
  eliminate exists (c3:CS.connection_model) (d3s d3r t3s t3r:B.bytes).
    CS.legal_event cvs e3 /\ CS.step_model cvs e3 == Some c3 /\
    CS.event_raw_delta_legal cvs e3 d3s d3r /\
    Canonical.sent_event_nonempty_seal_projection cvs e3 d3s /\
    Seq.equal tvs (B.append d3s t3s) /\ Seq.equal tvr (B.append d3r t3r) /\
    SMReplay.conn_events_sent_seal_replay c3 client_rest t3s t3r final_c
  returns goal
  with _. (
    introduce exists (ci0 c00 c10 cas0 c20 cvs0 c30:CS.connection_model) (cts ctr:B.bytes).
      client_flight_chain mc final_c mat_read ee cert cv_validate cv cv_verify sf client_rest
        ci0 c00 c10 cas0 c20 cvs0 c30 cts ctr
    with ci c0 c1 cas c2 cvs c3 t3s t3r
    and ()
  )))))))
#pop-options

#restart-solver
let server_flight_chain
  (ms final_s:CS.connection_model) (mat_write:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (server_rest:list CS.conn_event)
  (si s0 s1 sas s2 s3:CS.connection_model)
  (st_sent st_recv:B.bytes) : prop =
  CS.step_model ms (RI.server_hs_write_install_event mat_write) == Some si /\
  CS.step_model si (sent_ev (M.EncryptedExtensions ee)) == Some s0 /\
  CS.step_model s0 (sent_ev (M.Certificate cert)) == Some s1 /\
  CS.legal_event s1 (CS.ConnLocalEvent cv_local) /\
  CS.step_model s1 (CS.ConnLocalEvent cv_local) == Some sas /\
  CS.step_model sas (sent_ev (M.CertificateVerify cv)) == Some s2 /\
  CS.step_model s2 (sent_ev (M.Finished sf)) == Some s3 /\
  SMReplay.conn_events_received_decode_replay s3 server_rest st_sent st_recv final_s

let server_chain_exists
  (ms final_s:CS.connection_model) (mat_write:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (server_rest:list CS.conn_event) : prop =
  exists (si s0 s1 sas s2 s3:CS.connection_model) (st_sent st_recv:B.bytes).
    server_flight_chain ms final_s mat_write ee cert cv_local cv sf server_rest
      si s0 s1 sas s2 s3 st_sent st_recv

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120 --split_queries always"
let lemma_peel_server_flight
  (ms final_s:CS.connection_model) (mat_write:CS.traffic_key_material)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_local:CS.local_event) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (server_rest:list CS.conn_event)
  (fl_sent fl_recv:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay ms
          (RI.server_hs_write_install_event mat_write ::
           server_flight_tail ee cert cv_local cv sf server_rest)
          fl_sent fl_recv final_s)
      (ensures
        server_chain_exists ms final_s mat_write ee cert cv_local cv sf server_rest)
  =
  let goal = server_chain_exists ms final_s mat_write ee cert cv_local cv sf server_rest in
  let e_i = RI.server_hs_write_install_event mat_write in
  let e0 = sent_ev (M.EncryptedExtensions ee) in
  let e1 = sent_ev (M.Certificate cert) in
  let ea = CS.ConnLocalEvent cv_local in
  let e2 = sent_ev (M.CertificateVerify cv) in
  let e3 = sent_ev (M.Finished sf) in
  let r_i = e0 :: e1 :: ea :: e2 :: e3 :: server_rest in
  PWReplay.lemma_conn_events_received_decode_replay_head ms e_i r_i fl_sent fl_recv final_s;
  eliminate exists (si:CS.connection_model) (dis dir tis tir:B.bytes).
    CS.legal_event ms e_i /\ CS.step_model ms e_i == Some si /\
    CS.event_raw_delta_legal ms e_i dis dir /\
    Canonical.received_event_nonempty_decode_projection ms e_i dir /\
    Seq.equal fl_sent (B.append dis tis) /\ Seq.equal fl_recv (B.append dir tir) /\
    SMReplay.conn_events_received_decode_replay si r_i tis tir final_s
  returns goal
  with _. (
  let r0 = e1 :: ea :: e2 :: e3 :: server_rest in
  PWReplay.lemma_conn_events_received_decode_replay_head si e0 r0 tis tir final_s;
  eliminate exists (s0:CS.connection_model) (d0s d0r t0s t0r:B.bytes).
    CS.legal_event si e0 /\ CS.step_model si e0 == Some s0 /\
    CS.event_raw_delta_legal si e0 d0s d0r /\
    Canonical.received_event_nonempty_decode_projection si e0 d0r /\
    Seq.equal tis (B.append d0s t0s) /\ Seq.equal tir (B.append d0r t0r) /\
    SMReplay.conn_events_received_decode_replay s0 r0 t0s t0r final_s
  returns goal
  with _. (
  let r1 = ea :: e2 :: e3 :: server_rest in
  PWReplay.lemma_conn_events_received_decode_replay_head s0 e1 r1 t0s t0r final_s;
  eliminate exists (s1:CS.connection_model) (d1s d1r t1s t1r:B.bytes).
    CS.legal_event s0 e1 /\ CS.step_model s0 e1 == Some s1 /\
    CS.event_raw_delta_legal s0 e1 d1s d1r /\
    Canonical.received_event_nonempty_decode_projection s0 e1 d1r /\
    Seq.equal t0s (B.append d1s t1s) /\ Seq.equal t0r (B.append d1r t1r) /\
    SMReplay.conn_events_received_decode_replay s1 r1 t1s t1r final_s
  returns goal
  with _. (
  let ra = e2 :: e3 :: server_rest in
  PWReplay.lemma_conn_events_received_decode_replay_head s1 ea ra t1s t1r final_s;
  eliminate exists (sas:CS.connection_model) (das dar tas tar:B.bytes).
    CS.legal_event s1 ea /\ CS.step_model s1 ea == Some sas /\
    CS.event_raw_delta_legal s1 ea das dar /\
    Canonical.received_event_nonempty_decode_projection s1 ea dar /\
    Seq.equal t1s (B.append das tas) /\ Seq.equal t1r (B.append dar tar) /\
    SMReplay.conn_events_received_decode_replay sas ra tas tar final_s
  returns goal
  with _. (
  let r2 = e3 :: server_rest in
  PWReplay.lemma_conn_events_received_decode_replay_head sas e2 r2 tas tar final_s;
  eliminate exists (s2:CS.connection_model) (d2s d2r t2s t2r:B.bytes).
    CS.legal_event sas e2 /\ CS.step_model sas e2 == Some s2 /\
    CS.event_raw_delta_legal sas e2 d2s d2r /\
    Canonical.received_event_nonempty_decode_projection sas e2 d2r /\
    Seq.equal tas (B.append d2s t2s) /\ Seq.equal tar (B.append d2r t2r) /\
    SMReplay.conn_events_received_decode_replay s2 r2 t2s t2r final_s
  returns goal
  with _. (
  PWReplay.lemma_conn_events_received_decode_replay_head s2 e3 server_rest t2s t2r final_s;
  eliminate exists (s3:CS.connection_model) (d3s d3r t3s t3r:B.bytes).
    CS.legal_event s2 e3 /\ CS.step_model s2 e3 == Some s3 /\
    CS.event_raw_delta_legal s2 e3 d3s d3r /\
    Canonical.received_event_nonempty_decode_projection s2 e3 d3r /\
    Seq.equal t2s (B.append d3s t3s) /\ Seq.equal t2r (B.append d3r t3r) /\
    SMReplay.conn_events_received_decode_replay s3 server_rest t3s t3r final_s
  returns goal
  with _. (
    introduce exists (si0 s00 s10 sas0 s20 s30:CS.connection_model) (sts str:B.bytes).
      server_flight_chain ms final_s mat_write ee cert cv_local cv sf server_rest
        si0 s00 s10 sas0 s20 s30 sts str
    with si s0 s1 sas s2 s3 t3s t3r
    and ()
  ))))))
#pop-options

(* ================================================================== *)
(* Per-step stage / role / record-field tracking lemmas.               *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
(* ---- client single-step lemmas ---- *)
let lemma_c_install (m m1:CS.connection_model) (mat:CS.traffic_key_material)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
             CS.step_model m (RI.client_hs_read_install_event mat) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_recv_ee (m m1:CS.connection_model) (ee:GEE.encryptedExtensions)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
             CS.step_model m (recv_ev (M.EncryptedExtensions ee)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_recv_cert (m m1:CS.connection_model) (cert:GCert.certificate)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived /\
             CS.step_model m (recv_ev (M.Certificate cert)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_validate (m m1 m2:CS.connection_model) (l:CS.local_event) (cv:GCV.certificateVerify)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived /\
             CS.legal_event m (CS.ConnLocalEvent l) /\
             CS.step_model m (CS.ConnLocalEvent l) == Some m1 /\
             CS.step_model m1 (recv_ev (M.CertificateVerify cv)) == Some m2)
          (ensures
             PWBase.local_event_does_not_install_record_keys l /\
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_recv_cv (m m1:CS.connection_model) (cv:GCV.certificateVerify)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated /\
             CS.step_model m (recv_ev (M.CertificateVerify cv)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_verifysig (m m1 m2:CS.connection_model) (l:CS.local_event) (sf:GFin.finished)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
             CS.legal_event m (CS.ConnLocalEvent l) /\
             CS.step_model m (CS.ConnLocalEvent l) == Some m1 /\
             CS.step_model m1 (recv_ev (M.Finished sf)) == Some m2)
          (ensures
             PWBase.local_event_does_not_install_record_keys l /\
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_c_recv_sf (m m1:CS.connection_model) (sf:GFin.finished)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified /\
             CS.step_model m (recv_ev (M.Finished sf)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ClientEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
             m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

(* ---- server single-step lemmas ---- *)
let lemma_s_install (m m1:CS.connection_model) (mat:CS.traffic_key_material)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
             CS.step_model m (RI.server_hs_write_install_event mat) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_s_sent_ee (m m1:CS.connection_model) (ee:GEE.encryptedExtensions)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
             CS.step_model m (sent_ev (M.EncryptedExtensions ee)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_s_sent_cert (m m1:CS.connection_model) (cert:GCert.certificate)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             CS.step_model m (sent_ev (M.Certificate cert)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_s_cv_local (m m1 m2:CS.connection_model) (l:CS.local_event) (cv:GCV.certificateVerify)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             CS.legal_event m (CS.ConnLocalEvent l) /\
             CS.step_model m (CS.ConnLocalEvent l) == Some m1 /\
             CS.step_model m1 (sent_ev (M.CertificateVerify cv)) == Some m2)
          (ensures
             PWBase.local_event_does_not_install_record_keys l /\
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_s_sent_cv (m m1:CS.connection_model) (cv:GCV.certificateVerify)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             CS.step_model m (sent_ev (M.CertificateVerify cv)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()

let lemma_s_sent_sf (m m1:CS.connection_model) (sf:GFin.finished)
  : Lemma (requires
             m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
             CS.step_model m (sent_ev (M.Finished sf)) == Some m1)
          (ensures
             m1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
             m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
             m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
             m1.CS.model_handshake.CS.hs_client_finished ==
               m.CS.model_handshake.CS.hs_client_finished)
  = ()
#pop-options

(* ================================================================== *)
(* STEP 2 — pre-flight CF-direction alignment  mc / ms.                *)
(* ================================================================== *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 60"
let lemma_preflight_align
  (mc ms:CS.connection_model)
  (mat_write mat_read:CS.traffic_key_material)
  : Lemma
      (requires
        client_write_installed mc mat_write /\
        server_read_installed ms mat_read /\
        (match
          mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
        with
        | Some client_secret, Some server_secret -> Seq.equal client_secret server_secret
        | _, _ -> False) /\
        Seq.equal mc.CS.model_handshake.CS.hs_transcript
                  ms.CS.model_handshake.CS.hs_transcript)
      (ensures PWBase.write_read_record_material_aligned mc ms)
  =
  lemma_redundant_cw_install_identity mc mat_write;
  lemma_redundant_sr_install_identity ms mat_read;
  RecAlign.lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
    mc ms mat_write mat_read mc ms
#pop-options

(* ================================================================== *)
(* STEP 3 — call the encrypted-flight producer (PWSFlight :1886).      *)
(* ================================================================== *)

unfold let postflight_pkg (s:sysp)
  (c3 s3:CS.connection_model)
  (client_rest server_rest:list CS.conn_event)
  (cts ctr sts str:B.bytes) : prop =
  c3.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  c3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
  s3.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  s3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
  PWBase.write_read_record_material_aligned c3 s3 /\
  Seq.equal cts str /\
  SCShape.log_has_no_received_ccs server_rest /\
  SMReplay.conn_events_sent_seal_replay c3 client_rest cts ctr s.client.CS.cs_model /\
  SMReplay.conn_events_received_decode_replay s3 server_rest sts str s.server.CS.cs_model

unfold let postflight_exists (s:sysp) : prop =
  exists (c3 s3:CS.connection_model) (client_rest server_rest:list CS.conn_event)
    (cts ctr sts str:B.bytes).
    postflight_pkg s c3 s3 client_rest server_rest cts ctr sts str

let lemma_mk_postflight (s:sysp)
  (c3 s3:CS.connection_model) (client_rest server_rest:list CS.conn_event)
  (cts ctr sts str:B.bytes)
  : Lemma (requires postflight_pkg s c3 s3 client_rest server_rest cts ctr sts str)
          (ensures postflight_exists s)
  = introduce exists (c3' s3':CS.connection_model) (crest srest:list CS.conn_event)
        (cts' ctr' sts' str':B.bytes).
        postflight_pkg s c3' s3' crest srest cts' ctr' sts' str'
    with c3 s3 client_rest server_rest cts ctr sts str
    and ()

(* Core producer step: chains already peeled; invoke PWSFlight :1886 and
   package the output as a postflight existential.  Kept separate from the
   agreement/peel reasoning of lemma_finish_cf to keep each Z3 query small. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150 --split_queries always"
let lemma_cf_producer_core (s:sysp)
  (mc ms:CS.connection_model)
  (mat_read_c mat_write_s:CS.traffic_key_material)
  (ci c0 c1 cas c2 cvs c3:CS.connection_model)
  (si s0 s1 sas s2 s3:CS.connection_model)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (validate_c:CS.local_event)
  (cv_c:GCV.certificateVerify) (verifysig_c:CS.local_event) (sf_c:GFin.finished)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished)
  (client_rest server_rest:list CS.conn_event)
  (fl_sent_c fl_recv_c fl_sent_s fl_recv_s:B.bytes)
  (ct_sent ct_recv st_sent st_recv:B.bytes)
  : Lemma
      (requires
        PWBase.write_read_record_material_aligned mc ms /\
        Seq.equal fl_sent_c fl_recv_s /\
        SCShape.log_has_no_received_ccs server_rest /\
        mc.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        mc.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        ms.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        ms.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        client_flight_chain mc s.client.CS.cs_model mat_read_c ee_c cert_c validate_c
          cv_c verifysig_c sf_c client_rest ci c0 c1 cas c2 cvs c3 ct_sent ct_recv /\
        server_flight_chain ms s.server.CS.cs_model mat_write_s ee_s cert_s cv_local_s
          cv_s sf_s server_rest si s0 s1 sas s2 s3 st_sent st_recv /\
        SMReplay.conn_events_sent_seal_replay mc
          (RI.client_hs_read_install_event mat_read_c ::
           client_flight_tail ee_c cert_c validate_c cv_c verifysig_c sf_c client_rest)
          fl_sent_c fl_recv_c s.client.CS.cs_model /\
        SMReplay.conn_events_received_decode_replay ms
          (RI.server_hs_write_install_event mat_write_s ::
           server_flight_tail ee_s cert_s cv_local_s cv_s sf_s server_rest)
          fl_sent_s fl_recv_s s.server.CS.cs_model)
      (ensures postflight_exists s)
  =
  let final_c = s.client.CS.cs_model in
  let final_s = s.server.CS.cs_model in
  (* ---- client stage tracking ---- *)
  lemma_c_install mc ci mat_read_c;
  lemma_c_recv_ee ci c0 ee_c;
  lemma_c_recv_cert c0 c1 cert_c;
  lemma_c_validate c1 cas c2 validate_c cv_c;
  lemma_c_recv_cv cas c2 cv_c;
  lemma_c_verifysig c2 cvs c3 verifysig_c sf_c;
  lemma_c_recv_sf cvs c3 sf_c;
  (* ---- server stage tracking ---- *)
  lemma_s_install ms si mat_write_s;
  lemma_s_sent_ee si s0 ee_s;
  lemma_s_sent_cert s0 s1 cert_s;
  lemma_s_cv_local s1 sas s2 cv_local_s cv_s;
  lemma_s_sent_cv sas s2 cv_s;
  lemma_s_sent_sf s2 s3 sf_s;
  (* ---- call the producer ---- *)
  PWSFlight.lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails
    ms mc
    si ci s0 c0 s1 c1 sas cas s2 c2 cvs s3 c3
    cv_local_s validate_c verifysig_c
    mat_write_s mat_read_c
    (M.EncryptedExtensions ee_s) (M.EncryptedExtensions ee_c)
    (M.Certificate cert_s) (M.Certificate cert_c)
    (M.CertificateVerify cv_s) (M.CertificateVerify cv_c)
    (M.Finished sf_s) (M.Finished sf_c)
    server_rest client_rest
    fl_sent_s fl_recv_s fl_sent_c fl_recv_c
    final_s final_c;
  assert (exists (cts ctr sts str:B.bytes).
    PWBase.write_read_record_material_aligned c3 s3 /\
    Seq.equal cts str /\
    SMReplay.conn_events_sent_seal_replay c3 client_rest cts ctr final_c /\
    SMReplay.conn_events_received_decode_replay s3 server_rest sts str final_s);
  eliminate exists (cts ctr sts str:B.bytes).
    PWBase.write_read_record_material_aligned c3 s3 /\
    Seq.equal cts str /\
    SMReplay.conn_events_sent_seal_replay c3 client_rest cts ctr final_c /\
    SMReplay.conn_events_received_decode_replay s3 server_rest sts str final_s
  returns postflight_exists s
  with _.
  (
    lemma_mk_postflight s c3 s3 client_rest server_rest cts ctr sts str
  )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300 --split_queries always"
let lemma_finish_cf (s:sysp)
  (ms:CS.connection_model)
  (mat_write_s mat_read_s:CS.traffic_key_material)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_local_s:CS.local_event)
  (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (server_rest:list CS.conn_event)
  (fl_sent_s fl_recv_s:B.bytes) (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (d_ch_s rest_ss:B.bytes)
  (mc:CS.connection_model)
  (mat_read_c mat_write_c:CS.traffic_key_material)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (validate_c:CS.local_event)
  (cv_c:GCV.certificateVerify) (verifysig_c:CS.local_event) (sf_c:GFin.finished)
  (client_rest:list CS.conn_event)
  (fl_sent_c fl_recv_c:B.bytes) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (sh_rest_c:B.bytes)
  : Lemma
      (requires
        client_finished_bridge_inputs s.client s.server /\
        server_pkg s ms mat_write_s mat_read_s ee_s cert_s cv_local_s cv_s sf_s server_rest
          fl_sent_s fl_recv_s ch_s sh_s d_ch_s rest_ss /\
        client_pkg s mc mat_read_c mat_write_c ee_c cert_c validate_c cv_c verifysig_c sf_c
          client_rest fl_sent_c fl_recv_c ch_c sh_c sh_rest_c)
      (ensures postflight_exists s)
  =
  lemma_goalA_state s;
  lemma_byte_pairing_quiet s;
  let cs = s.client.CS.cs_wire_log.CL.raw_sent in
  let sr = s.server.CS.cs_wire_log.CL.raw_received in
  let ss = s.server.CS.cs_wire_log.CL.raw_sent in
  let cr = s.client.CS.cs_wire_log.CL.raw_received in
  let final_s = s.server.CS.cs_model in
  let final_c = s.client.CS.cs_model in
  (* ---- CH agreement (cs = client sent, sr = server received) ---- *)
  Seq.lemma_eq_elim cs sr;
  lemma_ch_serialize_agree ch_c ch_s cs sr fl_sent_c fl_recv_s d_ch_s;
  (* ---- flight byte equality: client_raw_sent == server_raw_received ---- *)
  lemma_ch_flight_align ch_c ch_s cs sr fl_sent_c fl_recv_s d_ch_s;
  assert (Seq.equal fl_sent_c fl_recv_s);
  (* ---- SH agreement (ss = server sent, cr = client received) ---- *)
  Seq.lemma_eq_elim ss cr;
  assert (Seq.equal ss
            (B.append
              (W.serialize_record T.Handshake
                (W.serialize_handshake (M.ServerHello sh_c)))
              sh_rest_c));
  lemma_front_handshake_record_agree
    (W.serialize_handshake (M.ServerHello sh_s))
    (W.serialize_handshake (M.ServerHello sh_c))
    rest_ss sh_rest_c ss;
  (* ---- transcript equality ---- *)
  lemma_transcript_cong ch_s ch_c sh_s sh_c;
  assert (Seq.equal mc.CS.model_handshake.CS.hs_transcript
                    ms.CS.model_handshake.CS.hs_transcript);
  (* ---- handshake-secret agreement ---- *)
  lemma_secret_swap final_s.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
                    final_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret;
  assert (match mc.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
                ms.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
          | Some a, Some b -> Seq.equal a b
          | _ -> False);
  (* ---- pre-flight alignment mc / ms ---- *)
  lemma_preflight_align mc ms mat_write_c mat_read_s;
  assert (mc.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert (mc.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  assert (ms.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (ms.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
  (* ---- peel both flights into intermediate models ---- *)
  lemma_peel_client_flight mc final_c mat_read_c ee_c cert_c validate_c cv_c verifysig_c sf_c
    client_rest fl_sent_c fl_recv_c;
  lemma_peel_server_flight ms final_s mat_write_s ee_s cert_s cv_local_s cv_s sf_s
    server_rest fl_sent_s fl_recv_s;
  eliminate exists (ci c0 c1 cas c2 cvs c3:CS.connection_model) (ct_sent ct_recv:B.bytes).
    client_flight_chain mc final_c mat_read_c ee_c cert_c validate_c cv_c verifysig_c sf_c
      client_rest ci c0 c1 cas c2 cvs c3 ct_sent ct_recv
  returns postflight_exists s
  with _.
  (
  eliminate exists (si s0 s1 sas s2 s3:CS.connection_model) (st_sent st_recv:B.bytes).
    server_flight_chain ms final_s mat_write_s ee_s cert_s cv_local_s cv_s sf_s
      server_rest si s0 s1 sas s2 s3 st_sent st_recv
  returns postflight_exists s
  with _.
  (
    lemma_cf_producer_core s mc ms mat_read_c mat_write_s
      ci c0 c1 cas c2 cvs c3 si s0 s1 sas s2 s3
      ee_c cert_c validate_c cv_c verifysig_c sf_c
      ee_s cert_s cv_local_s cv_s sf_s
      client_rest server_rest
      fl_sent_c fl_recv_c fl_sent_s fl_recv_s
      ct_sent ct_recv st_sent st_recv
  ))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let lemma_combine_cf (s:sysp)
  : Lemma (requires client_finished_bridge_inputs s.client s.server)
          (ensures postflight_exists s)
  =
  lemma_client_side_cf s;
  lemma_server_side_cf s;
  eliminate exists (mc:CS.connection_model)
    (mrc mwc:CS.traffic_key_material)
    (eec:GEE.encryptedExtensions) (certc:GCert.certificate)
    (valc:CS.local_event) (cvc:GCV.certificateVerify) (vfc:CS.local_event)
    (sfc:GFin.finished) (crest:list CS.conn_event)
    (flsc flrc:B.bytes) (chc:GCH.clientHello) (shc:GSH.serverHello)
    (shrestc:B.bytes).
    client_pkg s mc mrc mwc eec certc valc cvc vfc sfc crest flsc flrc chc shc shrestc
  returns postflight_exists s
  with _.
  (
  eliminate exists (ms:CS.connection_model)
    (mws mrs:CS.traffic_key_material)
    (ees:GEE.encryptedExtensions) (certs:GCert.certificate)
    (cvls:CS.local_event) (cvs:GCV.certificateVerify)
    (sfs:GFin.finished) (srest:list CS.conn_event)
    (flss flrs:B.bytes) (chs:GCH.clientHello) (shs:GSH.serverHello)
    (dchs restss:B.bytes).
    server_pkg s ms mws mrs ees certs cvls cvs sfs srest flss flrs chs shs dchs restss
  returns postflight_exists s
  with _.
  (
    lemma_finish_cf s
      ms mws mrs ees certs cvls cvs sfs srest flss flrs chs shs dchs restss
      mc mrc mwc eec certc valc cvc vfc sfc crest flsc flrc chc shc shrestc
  ))
#pop-options

(* ================================================================== *)
(* STEP 4 — expose the client Finished past the flight tail.           *)
(* ================================================================== *)

(* A single legal step out of a failed control stays failed. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_step_preserves_failed
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma (requires CS.step_model m ev == Some m1 /\ CS.ControlFailed? m.CS.model_control)
          (ensures CS.ControlFailed? m1.CS.model_control)
  = ()
#pop-options

(* Failed control is absorbing under a received-decode replay. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec lemma_failed_absorbing_recv
  (m:CS.connection_model) (events:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m events rs rr final /\
        CS.ControlFailed? m.CS.model_control)
      (ensures CS.ControlFailed? final.CS.model_control)
      (decreases events)
  = match events with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\
        CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.received_event_nonempty_decode_projection m ev dr /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_received_decode_replay model1 rest ts tr final
      returns CS.ControlFailed? final.CS.model_control
      with _.
      ( lemma_step_preserves_failed m ev model1;
        lemma_failed_absorbing_recv model1 rest ts tr final )
#pop-options

(* Failed control is absorbing under a sent-seal replay. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec lemma_failed_absorbing_sent
  (m:CS.connection_model) (events:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m events rs rr final /\
        CS.ControlFailed? m.CS.model_control)
      (ensures CS.ControlFailed? final.CS.model_control)
      (decreases events)
  = match events with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\
        CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.sent_event_nonempty_seal_projection m ev ds /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_sent_seal_replay model1 rest ts tr final
      returns CS.ControlFailed? final.CS.model_control
      with _.
      ( lemma_step_preserves_failed m ev model1;
        lemma_failed_absorbing_sent model1 rest ts tr final )
#pop-options

(* ------------------------------------------------------------------ *)
(* STEP 4 classify lemmas: one legal step at the pre-CF control.       *)
(* ------------------------------------------------------------------ *)

(* The sent delta of a `Sent ChangeCipherSpec` event parses as a cleartext
   ChangeCipherSpec record (leading content-type byte 0x14). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_ccs_sent_delta_parses (ds:B.bytes)
  : Lemma
      (requires Seq.equal ds (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec))
      (ensures
        (exists (frag:M.sealed_record) (c:nat).
           W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
           c <= B.length ds))
  =
  W.lemma_serialize_tls_message_change_cipher_spec ();
  let frag : B.bytes = B.singleton 1uy in
  assert (B.length frag == 1);
  assert (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec ==
          W.serialize_record T.Change_cipher_spec frag);
  Seq.lemma_eq_elim ds (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec);
  assert (ds == W.serialize_record T.Change_cipher_spec frag);
  W.lemma_parse_record_serialize_record T.Change_cipher_spec frag;
  assert (W.parse_record ds == Some (T.Change_cipher_spec, (frag <: M.sealed_record), B.length ds));
  W.lemma_parse_record_implies_parse_record_wire ds;
  assert (W.parse_record_wire ds == Some (T.Change_cipher_spec, (frag <: M.sealed_record), B.length ds));
  introduce exists (fr:M.sealed_record) (c:nat).
      W.parse_record_wire ds == Some (T.Change_cipher_spec, fr, c) /\ c <= B.length ds
  with (frag <: M.sealed_record) (B.length ds) and ()
#pop-options

(* Server at HsServerFinishedSent (received-decode side).  A single legal
   received-decode step is either the CF itself, or fails the control, or is
   byte-neutral on the received stream and preserves record_read/control. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200 --split_queries always"
let lemma_server_step_classify
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  (ds dr:B.bytes)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        SCShape.is_received_ccs ev == false)
      (ensures
        (exists (cf:GFin.finished). ev == recv_ev (M.Finished cf)) \/
        CS.ControlFailed? m1.CS.model_control \/
        (B.length dr == 0 /\
         m1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
         m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
         m1.CS.model_config.CS.config_role == CS.ServerEndpoint))
  =
  match ev with
  | CS.ConnProtectedHandshake _ -> ()
  | CS.ConnLocalEvent local -> ()
  | CS.ConnNetworkEvent msg ->
    match msg.CL.message_value with
    | M.TlsHandshake (M.Finished fin) ->
      ( match msg.CL.message_direction with
        | CL.Received ->
          introduce exists (cf:GFin.finished). ev == recv_ev (M.Finished cf)
          with fin and ()
        | CL.Sent -> () )
    | M.TlsHandshake _ -> ()
    | M.TlsAlert _ -> ()
    | M.TlsChangeCipherSpec -> ()
    | M.TlsApplicationData _ -> ()
    | M.TlsIgnoredPostHandshake _ -> ()
    | M.TlsKeyUpdate _ -> ()
#pop-options

(* Client at HsServerFinishedVerified (sent-seal side).  A single legal
   sent-seal step is either the CF itself, or fails the control, or is
   byte-neutral on the sent stream (preserving record_write/control), or is a
   ChangeCipherSpec send whose sent delta parses as a cleartext CCS record. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 300 --split_queries always"
#restart-solver
let lemma_client_step_classify
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  (ds dr:B.bytes)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.event_raw_delta_legal m ev ds dr)
      (ensures
        (exists (cf:GFin.finished). ev == sent_ev (M.Finished cf)) \/
        CS.ControlFailed? m1.CS.model_control \/
        (B.length ds == 0 /\
         m1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
         m1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
         m1.CS.model_config.CS.config_role == CS.ClientEndpoint) \/
        (exists (frag:M.sealed_record) (c:nat).
           W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
           c <= B.length ds))
  =
  match ev with
  | CS.ConnProtectedHandshake _ -> ()
  | CS.ConnLocalEvent local -> ()
  | CS.ConnNetworkEvent msg ->
    match msg.CL.message_value with
    | M.TlsHandshake (M.Finished fin) ->
      ( match msg.CL.message_direction with
        | CL.Sent ->
          introduce exists (cf:GFin.finished). ev == sent_ev (M.Finished cf)
          with fin and ()
        | CL.Received -> () )
    | M.TlsHandshake _ -> ()
    | M.TlsAlert _ -> ()
    | M.TlsChangeCipherSpec ->
      ( match msg.CL.message_direction with
        | CL.Received -> ()
        | CL.Sent ->
          assert (Seq.equal ds (CS.serialized_cleartext_tls_message M.TlsChangeCipherSpec));
          lemma_ccs_sent_delta_parses ds )
#pop-options

(* ------------------------------------------------------------------ *)
(* STEP 4 peel lemmas: expose the CF past the byte-neutral tail.       *)
(* ------------------------------------------------------------------ *)

let server_cf_peeled
  (rd0:R.direction_state) (rr:B.bytes) (final:CS.connection_model) : prop =
  exists (mpre:CS.connection_model) (cf:GFin.finished)
         (tail3:list CS.conn_event) (rs':B.bytes).
    mpre.CS.model_record.CS.record_read == rd0 /\
    mpre.CS.model_config.CS.config_role == CS.ServerEndpoint /\
    mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
    SMReplay.conn_events_received_decode_replay mpre
       (recv_ev (M.Finished cf) :: tail3) rs' rr final

#push-options "--fuel 2 --ifuel 2 --z3rlimit 200 --split_queries always"
let rec lemma_peel_server_cf
  (m:CS.connection_model) (events:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m events rs rr final /\
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        final.CS.model_control == CS.ControlApplicationData /\
        SCShape.log_has_no_received_ccs events)
      (ensures server_cf_peeled m.CS.model_record.CS.record_read rr final)
      (decreases events)
  = match events with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
      assert (L.memP ev events);
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.received_event_nonempty_decode_projection m ev dr /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_received_decode_replay model1 rest ts tr final
      returns server_cf_peeled m.CS.model_record.CS.record_read rr final
      with _.
      ( lemma_server_step_classify m ev model1 ds dr;
        eliminate
          (exists (cf:GFin.finished). ev == recv_ev (M.Finished cf))
          \/
          (CS.ControlFailed? model1.CS.model_control \/
           (B.length dr == 0 /\
            model1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
            model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
            model1.CS.model_config.CS.config_role == CS.ServerEndpoint))
        returns server_cf_peeled m.CS.model_record.CS.record_read rr final
        with hcf.
          ( eliminate exists (cf:GFin.finished). ev == recv_ev (M.Finished cf)
            returns server_cf_peeled m.CS.model_record.CS.record_read rr final
            with _.
              ( lemma_replay_cong_recv m events (recv_ev (M.Finished cf) :: rest) rs rr final;
                introduce exists (mpre:CS.connection_model) (cf':GFin.finished)
                                 (tail3:list CS.conn_event) (rs':B.bytes).
                    mpre.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
                    mpre.CS.model_config.CS.config_role == CS.ServerEndpoint /\
                    mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
                    SMReplay.conn_events_received_decode_replay mpre
                       (recv_ev (M.Finished cf') :: tail3) rs' rr final
                with m cf rest rs and () ) )
        and hrest.
          ( eliminate
              CS.ControlFailed? model1.CS.model_control
              \/
              (B.length dr == 0 /\
               model1.CS.model_record.CS.record_read == m.CS.model_record.CS.record_read /\
               model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
               model1.CS.model_config.CS.config_role == CS.ServerEndpoint)
            returns server_cf_peeled m.CS.model_record.CS.record_read rr final
            with hfail.
              ( lemma_failed_absorbing_recv model1 rest ts tr final )
            and hneutral.
              ( assert (Seq.equal rr tr);
                Seq.lemma_eq_elim rr tr;
                lemma_no_ccs_of_suffix events [ev] rest;
                lemma_peel_server_cf model1 rest ts tr final ) ) )
#pop-options

let client_cf_peeled
  (wr0:R.direction_state) (rs:B.bytes) (final:CS.connection_model) : prop =
  exists (mpre:CS.connection_model) (cf:GFin.finished)
         (tail3:list CS.conn_event) (rr':B.bytes).
    mpre.CS.model_record.CS.record_write == wr0 /\
    mpre.CS.model_config.CS.config_role == CS.ClientEndpoint /\
    mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
    SMReplay.conn_events_sent_seal_replay mpre
       (sent_ev (M.Finished cf) :: tail3) rs rr' final

#push-options "--fuel 2 --ifuel 2 --z3rlimit 250 --split_queries always"
let rec lemma_peel_client_cf
  (m:CS.connection_model) (events:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m events rs rr final /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        final.CS.model_control == CS.ControlApplicationData /\
        (exists (frag:M.sealed_record) (c:nat).
           W.parse_record_wire rs == Some (T.Application_data, frag, c)))
      (ensures client_cf_peeled m.CS.model_record.CS.record_write rs final)
      (decreases events)
  = match events with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.sent_event_nonempty_seal_projection m ev ds /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_sent_seal_replay model1 rest ts tr final
      returns client_cf_peeled m.CS.model_record.CS.record_write rs final
      with _.
      ( lemma_client_step_classify m ev model1 ds dr;
        eliminate
          (exists (cf:GFin.finished). ev == sent_ev (M.Finished cf))
          \/
          (CS.ControlFailed? model1.CS.model_control
           \/
           ((B.length ds == 0 /\
             model1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
             model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
             model1.CS.model_config.CS.config_role == CS.ClientEndpoint)
            \/
            (exists (frag:M.sealed_record) (c:nat).
               W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
               c <= B.length ds)))
        returns client_cf_peeled m.CS.model_record.CS.record_write rs final
        with hcf.
          ( eliminate exists (cf:GFin.finished). ev == sent_ev (M.Finished cf)
            returns client_cf_peeled m.CS.model_record.CS.record_write rs final
            with _.
              ( lemma_replay_cong_sent m events (sent_ev (M.Finished cf) :: rest) rs rr final;
                introduce exists (mpre:CS.connection_model) (cf':GFin.finished)
                                 (tail3:list CS.conn_event) (rr':B.bytes).
                    mpre.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
                    mpre.CS.model_config.CS.config_role == CS.ClientEndpoint /\
                    mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
                    SMReplay.conn_events_sent_seal_replay mpre
                       (sent_ev (M.Finished cf') :: tail3) rs rr' final
                with m cf rest rr and () ) )
        and hrest.
          ( eliminate
              CS.ControlFailed? model1.CS.model_control
              \/
              ((B.length ds == 0 /\
                model1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
                model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
                model1.CS.model_config.CS.config_role == CS.ClientEndpoint)
               \/
               (exists (frag:M.sealed_record) (c:nat).
                  W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
                  c <= B.length ds))
            returns client_cf_peeled m.CS.model_record.CS.record_write rs final
            with hfail.
              ( lemma_failed_absorbing_sent model1 rest ts tr final )
            and hrest2.
              ( eliminate
                  (B.length ds == 0 /\
                   model1.CS.model_record.CS.record_write == m.CS.model_record.CS.record_write /\
                   model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
                   model1.CS.model_config.CS.config_role == CS.ClientEndpoint)
                  \/
                  (exists (frag:M.sealed_record) (c:nat).
                     W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
                     c <= B.length ds)
                returns client_cf_peeled m.CS.model_record.CS.record_write rs final
                with hneutral.
                  ( assert (Seq.equal rs ts);
                    Seq.lemma_eq_elim rs ts;
                    lemma_peel_client_cf model1 rest ts tr final )
                and hccs.
                  ( eliminate exists (frag:M.sealed_record) (c:nat).
                       W.parse_record_wire ds == Some (T.Change_cipher_spec, frag, c) /\
                       c <= B.length ds
                    returns client_cf_peeled m.CS.model_record.CS.record_write rs final
                    with _.
                      ( Seq.lemma_eq_elim rs (B.append ds ts);
                        WRD.lemma_parse_record_wire_prefix ds T.Change_cipher_spec frag c;
                        assert (Seq.equal (Seq.slice rs 0 c) (Seq.slice ds 0 c));
                        Seq.lemma_eq_elim (Seq.slice rs 0 c) (Seq.slice ds 0 c);
                        WRD.lemma_parse_record_wire_from_prefix rs T.Change_cipher_spec frag c ) ) ) ) )
#pop-options

(* ================================================================== *)
(* STEP 5/6 — expose the CF, build the pair, pin the fields.           *)
(* ================================================================== *)

(* A post-handshake control (App-data or teardown): closed under stepping and
   never the site of an hs_client_finished update. *)
let control_post_handshake (c:CS.connection_control_state) : bool =
  match c with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed
  | CS.ControlFailed _ -> true
  | _ -> false

(* Alignment depends only on sender.record_write and receiver.record_read. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let lemma_aligned_transfer
  (c3 s3 mc ms:CS.connection_model)
  : Lemma
      (requires
        PWBase.write_read_record_material_aligned c3 s3 /\
        mc.CS.model_record.CS.record_write == c3.CS.model_record.CS.record_write /\
        ms.CS.model_record.CS.record_read == s3.CS.model_record.CS.record_read)
      (ensures PWBase.write_read_record_material_aligned mc ms)
  = ()
#pop-options

(* Stepping the CLIENT Finished sets hs_client_finished and leaves handshaking. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_client_cf_step_sets
  (m:CS.connection_model) (m1:CS.connection_model) (cf:GFin.finished)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model m (sent_ev (M.Finished cf)) == Some m1)
      (ensures
        m1.CS.model_handshake.CS.hs_client_finished == Some cf /\
        control_post_handshake m1.CS.model_control)
  = ()
#pop-options

(* Stepping the SERVER-received Finished sets hs_client_finished. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lemma_server_cf_step_sets
  (m:CS.connection_model) (m1:CS.connection_model) (cf:GFin.finished)
  : Lemma
      (requires
        m.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        m.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.step_model m (recv_ev (M.Finished cf)) == Some m1)
      (ensures
        m1.CS.model_handshake.CS.hs_client_finished == Some cf /\
        control_post_handshake m1.CS.model_control)
  = ()
#pop-options

(* At a non-handshaking control, any legal step preserves hs_client_finished
   and stays non-handshaking (the ONLY arms setting hs_client_finished require
   a handshaking control). *)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 150 --split_queries always"
let lemma_step_appdata_family
  (m:CS.connection_model) (ev:CS.conn_event) (m1:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m ev == Some m1 /\
        control_post_handshake m.CS.model_control)
      (ensures
        control_post_handshake m1.CS.model_control /\
        m1.CS.model_handshake.CS.hs_client_finished ==
          m.CS.model_handshake.CS.hs_client_finished)
  = match m.CS.model_control with
    | CS.ControlApplicationData -> ()
    | CS.ControlClosing -> ()
    | CS.ControlClosed -> ()
    | CS.ControlFailed _ -> ()
    | CS.ControlNew -> ()
    | CS.ControlHandshaking _ -> ()
#pop-options

(* Monotonicity of hs_client_finished across a non-handshaking sent-seal replay. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let rec lemma_sent_replay_preserves_hs_cf
  (m:CS.connection_model) (evs:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m evs rs rr final /\
        control_post_handshake m.CS.model_control)
      (ensures
        final.CS.model_handshake.CS.hs_client_finished ==
          m.CS.model_handshake.CS.hs_client_finished /\
        control_post_handshake final.CS.model_control)
      (decreases evs)
  = match evs with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_sent_seal_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.sent_event_nonempty_seal_projection m ev ds /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_sent_seal_replay model1 rest ts tr final
      returns (final.CS.model_handshake.CS.hs_client_finished ==
                 m.CS.model_handshake.CS.hs_client_finished /\
               control_post_handshake final.CS.model_control)
      with _.
      ( lemma_step_appdata_family m ev model1;
        lemma_sent_replay_preserves_hs_cf model1 rest ts tr final )
#pop-options

(* Monotonicity of hs_client_finished across a non-handshaking received-decode replay. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let rec lemma_received_replay_preserves_hs_cf
  (m:CS.connection_model) (evs:list CS.conn_event) (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m evs rs rr final /\
        control_post_handshake m.CS.model_control)
      (ensures
        final.CS.model_handshake.CS.hs_client_finished ==
          m.CS.model_handshake.CS.hs_client_finished /\
        control_post_handshake final.CS.model_control)
      (decreases evs)
  = match evs with
    | [] -> ()
    | ev :: rest ->
      PWReplay.lemma_conn_events_received_decode_replay_head m ev rest rs rr final;
      eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
        CS.legal_event m ev /\ CS.step_model m ev == Some model1 /\
        CS.event_raw_delta_legal m ev ds dr /\
        Canonical.received_event_nonempty_decode_projection m ev dr /\
        Seq.equal rs (B.append ds ts) /\
        Seq.equal rr (B.append dr tr) /\
        SMReplay.conn_events_received_decode_replay model1 rest ts tr final
      returns (final.CS.model_handshake.CS.hs_client_finished ==
                 m.CS.model_handshake.CS.hs_client_finished /\
               control_post_handshake final.CS.model_control)
      with _.
      ( lemma_step_appdata_family m ev model1;
        lemma_received_replay_preserves_hs_cf model1 rest ts tr final )
#pop-options

(* A single Application_data record byte-stream parses at the wire level. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let lemma_appdata_records_parse (raw:B.bytes)
  : Lemma
      (requires CS.raw_records_exactly raw T.Application_data 1)
      (ensures
        (exists (frag:M.sealed_record) (c:nat).
           W.parse_record_wire raw == Some (T.Application_data, frag, c) /\
           c <= B.length raw))
  =
  NRA.lemma_raw_records_exactly_nonempty_decompose raw T.Application_data 1;
  assert (exists (frag:M.sealed_record) (consumed:nat).
    W.parse_record raw == Some (T.Application_data, frag, consumed) /\
    consumed <= B.length raw);
  eliminate exists (fragment:M.sealed_record) (consumed:nat).
    W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
    consumed <= B.length raw
  returns (exists (frag:M.sealed_record) (c:nat).
             W.parse_record_wire raw == Some (T.Application_data, frag, c) /\
             c <= B.length raw)
  with _.
  ( W.lemma_parse_record_implies_parse_record_wire raw;
    introduce exists (frag:M.sealed_record) (c:nat).
        W.parse_record_wire raw == Some (T.Application_data, frag, c) /\ c <= B.length raw
    with fragment consumed and () )
#pop-options

(* The server received stream begins with the CF's sealed Application_data record;
   hence the whole stream parses (at content-type Application_data). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150 --split_queries always"
let lemma_server_cf_appdata_stream
  (mpre:CS.connection_model) (cf:GFin.finished) (tail3:list CS.conn_event)
  (rs' str:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay mpre
          (recv_ev (M.Finished cf) :: tail3) rs' str final)
      (ensures
        (exists (frag:M.sealed_record) (c:nat).
           W.parse_record_wire str == Some (T.Application_data, frag, c)))
  =
  PWReplay.lemma_conn_events_received_decode_replay_head mpre (recv_ev (M.Finished cf))
    tail3 rs' str final;
  eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
    CS.legal_event mpre (recv_ev (M.Finished cf)) /\
    CS.step_model mpre (recv_ev (M.Finished cf)) == Some model1 /\
    CS.event_raw_delta_legal mpre (recv_ev (M.Finished cf)) ds dr /\
    Canonical.received_event_nonempty_decode_projection mpre (recv_ev (M.Finished cf)) dr /\
    Seq.equal rs' (B.append ds ts) /\
    Seq.equal str (B.append dr tr) /\
    SMReplay.conn_events_received_decode_replay model1 tail3 ts tr final
  returns (exists (frag:M.sealed_record) (c:nat).
             W.parse_record_wire str == Some (T.Application_data, frag, c))
  with _.
  (
    assert (CS.raw_records_exactly dr T.Application_data 1);
    lemma_appdata_records_parse dr;
    eliminate exists (frag:M.sealed_record) (c:nat).
      W.parse_record_wire dr == Some (T.Application_data, frag, c) /\ c <= B.length dr
    returns (exists (frag:M.sealed_record) (c:nat).
               W.parse_record_wire str == Some (T.Application_data, frag, c))
    with _.
    (
      WRD.lemma_parse_record_wire_prefix dr T.Application_data frag c;
      Seq.lemma_eq_elim str (B.append dr tr);
      assert (Seq.equal (Seq.slice str 0 c) (Seq.slice dr 0 c));
      Seq.lemma_eq_elim (Seq.slice str 0 c) (Seq.slice dr 0 c);
      WRD.lemma_parse_record_wire_from_prefix str T.Application_data frag c;
      introduce exists (fr:M.sealed_record) (cc:nat).
          W.parse_record_wire str == Some (T.Application_data, fr, cc)
      with frag c and ()
    )
  )
#pop-options

(* Field pinning: the whole client sent-seal replay ends with the client's real
   hs_client_finished set to the CF value. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let lemma_pin_client_hs_cf
  (mpre:CS.connection_model) (cf:GFin.finished) (tail3:list CS.conn_event)
  (cts ctr':B.bytes) (final_c:CS.connection_model)
  : Lemma
      (requires
        mpre.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        SMReplay.conn_events_sent_seal_replay mpre
          (sent_ev (M.Finished cf) :: tail3) cts ctr' final_c)
      (ensures final_c.CS.model_handshake.CS.hs_client_finished == Some cf)
  =
  PWReplay.lemma_conn_events_sent_seal_replay_head mpre (sent_ev (M.Finished cf))
    tail3 cts ctr' final_c;
  eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
    CS.legal_event mpre (sent_ev (M.Finished cf)) /\
    CS.step_model mpre (sent_ev (M.Finished cf)) == Some model1 /\
    CS.event_raw_delta_legal mpre (sent_ev (M.Finished cf)) ds dr /\
    Canonical.sent_event_nonempty_seal_projection mpre (sent_ev (M.Finished cf)) ds /\
    Seq.equal cts (B.append ds ts) /\
    Seq.equal ctr' (B.append dr tr) /\
    SMReplay.conn_events_sent_seal_replay model1 tail3 ts tr final_c
  returns (final_c.CS.model_handshake.CS.hs_client_finished == Some cf)
  with _.
  ( lemma_client_cf_step_sets mpre model1 cf;
    lemma_sent_replay_preserves_hs_cf model1 tail3 ts tr final_c )
#pop-options

(* Field pinning: the whole server received-decode replay ends with the server's
   real hs_client_finished set to the CF value. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100 --split_queries always"
let lemma_pin_server_hs_cf
  (mpre:CS.connection_model) (cf:GFin.finished) (tail3:list CS.conn_event)
  (rs' str:B.bytes) (final_s:CS.connection_model)
  : Lemma
      (requires
        mpre.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        mpre.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        SMReplay.conn_events_received_decode_replay mpre
          (recv_ev (M.Finished cf) :: tail3) rs' str final_s)
      (ensures final_s.CS.model_handshake.CS.hs_client_finished == Some cf)
  =
  PWReplay.lemma_conn_events_received_decode_replay_head mpre (recv_ev (M.Finished cf))
    tail3 rs' str final_s;
  eliminate exists (model1:CS.connection_model) (ds dr ts tr:B.bytes).
    CS.legal_event mpre (recv_ev (M.Finished cf)) /\
    CS.step_model mpre (recv_ev (M.Finished cf)) == Some model1 /\
    CS.event_raw_delta_legal mpre (recv_ev (M.Finished cf)) ds dr /\
    Canonical.received_event_nonempty_decode_projection mpre (recv_ev (M.Finished cf)) dr /\
    Seq.equal rs' (B.append ds ts) /\
    Seq.equal str (B.append dr tr) /\
    SMReplay.conn_events_received_decode_replay model1 tail3 ts tr final_s
  returns (final_s.CS.model_handshake.CS.hs_client_finished == Some cf)
  with _.
  ( lemma_server_cf_step_sets mpre model1 cf;
    lemma_received_replay_preserves_hs_cf model1 tail3 ts tr final_s )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 150 --split_queries always"
let lemma_client_finished_pair_from_replays_and_pairing client server =
  let s : sysp = { client = client; server = server } in
  lemma_combine_cf s;
  lemma_appdata_client s.client;
  lemma_appdata_server s.server;
  eliminate exists (c3 s3:CS.connection_model) (client_rest server_rest:list CS.conn_event)
    (cts ctr sts str:B.bytes).
    postflight_pkg s c3 s3 client_rest server_rest cts ctr sts str
  returns client_finished_pair_conclusion s.client s.server
  with _.
  (
    let final_c = s.client.CS.cs_model in
    let final_s = s.server.CS.cs_model in
    lemma_peel_server_cf s3 server_rest sts str final_s;
    eliminate exists (mpre_s:CS.connection_model) (cf_s:GFin.finished)
                     (tail3_s:list CS.conn_event) (rs_s:B.bytes).
      mpre_s.CS.model_record.CS.record_read == s3.CS.model_record.CS.record_read /\
      mpre_s.CS.model_config.CS.config_role == CS.ServerEndpoint /\
      mpre_s.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
      SMReplay.conn_events_received_decode_replay mpre_s
         (recv_ev (M.Finished cf_s) :: tail3_s) rs_s str final_s
    returns client_finished_pair_conclusion s.client s.server
    with _.
    (
      lemma_server_cf_appdata_stream mpre_s cf_s tail3_s rs_s str final_s;
      Seq.lemma_eq_elim cts str;
      lemma_peel_client_cf c3 client_rest cts ctr final_c;
      eliminate exists (mpre_c:CS.connection_model) (cf_c:GFin.finished)
                       (tail3_c:list CS.conn_event) (rr_c:B.bytes).
        mpre_c.CS.model_record.CS.record_write == c3.CS.model_record.CS.record_write /\
        mpre_c.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        mpre_c.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified /\
        SMReplay.conn_events_sent_seal_replay mpre_c
           (sent_ev (M.Finished cf_c) :: tail3_c) cts rr_c final_c
      returns client_finished_pair_conclusion s.client s.server
      with _.
      (
        lemma_aligned_transfer c3 s3 mpre_c mpre_s;
        PWHead.lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails
          mpre_c mpre_s (M.Finished cf_c) (M.Finished cf_s)
          tail3_c tail3_s
          cts rr_c rs_s str
          final_c final_s;
        lemma_pin_client_hs_cf mpre_c cf_c tail3_c cts rr_c final_c;
        lemma_pin_server_hs_cf mpre_s cf_s tail3_s rs_s str final_s;
        assert (final_c.CS.model_handshake.CS.hs_client_finished == Some cf_c);
        assert (final_s.CS.model_handshake.CS.hs_client_finished == Some cf_s)
      )
    )
  )
#pop-options

module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ClientFinished

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SMIds = TLS13.Spec.StateMachine.KeyIdentifiers
module SMReplay = TLS13.Spec.StateMachine.Replay
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CD = TLS13.Impl.Client.Driver
module M = TLS13.Messages
module Sem   = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFRR = TLS13.Impl.Driver.PairingNoTailClientFinishedReceiverReplay
module PNTCFR = TLS13.Impl.Driver.PairingNoTailClientFinishedReplay
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPPD = TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module SD = TLS13.Impl.Server.Driver
module Tac = FStar.Tactics
module WFL = TLS13.Spec.WireFormatLemmas
module RA = TLS13.ConnectionState.ProtectedWireRecordAlignment
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module T = TLS13.Types
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module X = TLS13.X509.Spec
module K = TLS13.Keys
module W = TLS13.Wire.Spec
module L = FStar.List.Tot
module CSL = TLS13.ConnectionState.Lemmas
module WRD = TLS13.Wire.Spec.RevealDecode

module Foundation = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation
module Replay = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay
module ServerFlight = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ServerFlight
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ServerFlight

#push-options "--split_queries always --z3rlimit 10"

noextract
let iaw (cawm:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = cawm;
    })

noextract
let iar (carm:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = carm;
    })

noextract
let append_empty_left (rs:B.bytes) : Lemma (Seq.equal (B.append B.empty rs) rs) =
  Seq.lemma_len_append B.empty rs;
  Seq.lemma_eq_intro (B.append B.empty rs) rs

// Peel a local (empty-delta) event off the front of a sent-seal replay.
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
noextract
let peel_local_deconstruct
  (m:CS.connection_model)
  (lev:CS.conn_event)
  (rest:list CS.conn_event)
  (rs rr:B.bytes)
  (final m1:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? lev /\
        SMReplay.conn_events_sent_seal_replay m (lev :: rest) rs rr final /\
        CS.step_model m lev == Some m1)
      (ensures
        SMReplay.conn_events_sent_seal_replay m1 rest rs rr final /\
        CS.legal_event m lev)
=
  PWReplay.lemma_conn_events_sent_seal_replay_head m lev rest rs rr final;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      (CS.legal_event m lev /\
       CS.step_model m lev == Some model1 /\
       CS.event_raw_delta_legal m lev delta_sent delta_received /\
       SMCan.sent_event_nonempty_seal_projection m lev delta_sent /\
       Seq.equal rs (B.append delta_sent tail_sent) /\
       Seq.equal rr (B.append delta_received tail_received) /\
       SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final)
  returns (SMReplay.conn_events_sent_seal_replay m1 rest rs rr final /\ CS.legal_event m lev)
  with _.
  (
    // local event: delta_sent, delta_received empty; model1 == m1
    assert (Seq.equal delta_sent B.empty);
    assert (Seq.equal delta_received B.empty);
    Seq.lemma_eq_elim delta_sent B.empty;
    Seq.lemma_eq_elim delta_received B.empty;
    append_empty_left tail_sent;
    append_empty_left tail_received;
    assert (Seq.equal rs tail_sent);
    assert (Seq.equal rr tail_received);
    assert (model1 == m1)
  )
#pop-options

// Cons a local (empty-delta) event onto the front of a sent-seal replay.
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
noextract
let peel_local_construct
  (m:CS.connection_model)
  (lev:CS.conn_event)
  (rest:list CS.conn_event)
  (rs rr:B.bytes)
  (final m1:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? lev /\
        CS.legal_event m lev /\
        CS.step_model m lev == Some m1 /\
        SMReplay.conn_events_sent_seal_replay m1 rest rs rr final)
      (ensures SMReplay.conn_events_sent_seal_replay m (lev :: rest) rs rr final)
=
  append_empty_left rs;
  append_empty_left rr;
  PWReplay.lemma_conn_events_sent_seal_replay_cons
    m lev rest rs rr final m1 B.empty B.empty rs rr
#pop-options

noextract
let ev_sent_of (cf:GFin.finished) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  })

noextract
let ev_vf_of (sf:GFin.finished) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalVerifyFinished sf)

// commutation of the two client app installs (proved earlier standalone)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
noextract
let install_commute
  (m:CS.connection_model)
  (cawm carm:CS.traffic_key_material)
  (m_r m_rw:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m (iar carm) == Some m_r /\
        CS.step_model m_r (iaw cawm) == Some m_rw)
      (ensures
        (exists m_w.
          CS.step_model m (iaw cawm) == Some m_w /\
          CS.step_model m_w (iar carm) == Some m_rw))
= ()
#pop-options

// commutation of the two client app installs (proved earlier standalone)
#push-options "--z3rlimit 10 --fuel 3 --ifuel 3"
noextract
let install_commute_full
  (m:CS.connection_model)
  (cawm carm:CS.traffic_key_material)
  (m_r m_rw:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m (iar carm) == Some m_r /\
        CS.step_model m_r (iaw cawm) == Some m_rw /\
        CS.legal_event m (iar carm) /\
        CS.legal_event m_r (iaw cawm))
      (ensures
        (exists m_w.
          CS.step_model m (iaw cawm) == Some m_w /\
          CS.step_model m_w (iar carm) == Some m_rw /\
          CS.legal_event m (iaw cawm) /\
          CS.legal_event m_w (iar carm)))
= ()
#pop-options

#push-options "--z3rlimit 10 --fuel 3 --ifuel 3"
noextract
let plain_write_install_legal
  (m m1:CS.connection_model)
  (ev:CS.conn_event)
  (cawm:CS.traffic_key_material)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_write_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.step_model m (iaw cawm) == Some m1)
      (ensures CS.legal_event m (iaw cawm))
=
  PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev
#pop-options

#push-options "--z3rlimit 10 --fuel 3 --ifuel 3"
noextract
let plain_read_install_legal
  (m m1:CS.connection_model)
  (ev:CS.conn_event)
  (carm:CS.traffic_key_material)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_read_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.step_model m (iar carm) == Some m1)
      (ensures CS.legal_event m (iar carm))
=
  PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev
#pop-options

#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
noextract
let lemma_two_app_install_events_are_local
  (e13 e14:CS.conn_event)
  : Lemma
      (requires PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures CS.ConnLocalEvent? e13 /\ CS.ConnLocalEvent? e14)
=
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  eliminate
    (PNTCAS.client_no_tail_application_write_install_event e13 /\
     PNTCAS.client_no_tail_application_read_install_event e14) \/
    (PNTCAS.client_no_tail_application_read_install_event e13 /\
     PNTCAS.client_no_tail_application_write_install_event e14)
  returns (CS.ConnLocalEvent? e13 /\ CS.ConnLocalEvent? e14)
  with _. (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14
  )
  and _. (
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14
  )
#pop-options

#push-options "--z3rlimit 10 --fuel 4 --ifuel 2 --split_queries always"
noextract
let lemma_cover_to_self_install_replay
  (model12:CS.connection_model)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (suffix_sent suffix_received:B.bytes)
  (final:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        SMReplay.conn_events_sent_seal_replay model12
          (ev_vf_of sf :: e13 :: e14 :: ev_sent_of cf :: [])
          suffix_sent suffix_received final)
      (ensures
        (exists
           (cawm carm:CS.traffic_key_material)
           (av aw ar:CS.connection_model).
           CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some final /\
           SMReplay.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received final))
=
  let ev_vf = ev_vf_of sf in
  let ev_sent = ev_sent_of cf in
  let goal : prop =
    (exists
       (cawm carm:CS.traffic_key_material)
       (av aw ar:CS.connection_model).
       CS.step_model model12 ev_vf == Some av /\
       CS.step_model av (iaw cawm) == Some aw /\
       CS.step_model aw (iar carm) == Some ar /\
       CS.step_model ar ev_sent == Some final /\
       SMReplay.conn_events_sent_seal_replay model12
         (ev_vf :: iaw cawm :: iar carm :: ev_sent :: [])
         suffix_sent suffix_received final) in
  PNTCFR.lemma_client_finished_sent_seal_suffix_head_steps
    model12 sf e13 e14 cf suffix_sent suffix_received final;
  eliminate exists after_verify after_e13 after_e14.
      (CS.step_model model12 ev_vf == Some after_verify /\
       CS.step_model after_verify e13 == Some after_e13 /\
       CS.step_model after_e13 e14 == Some after_e14 /\
       CS.step_model after_e14 ev_sent == Some final)
  returns goal
  with _hs.
  (
    PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
    lemma_two_app_install_events_are_local e13 e14;
    peel_local_deconstruct model12 ev_vf (e13 :: e14 :: ev_sent :: []) suffix_sent suffix_received final after_verify;
    peel_local_deconstruct after_verify e13 (e14 :: ev_sent :: []) suffix_sent suffix_received final after_e13;
    peel_local_deconstruct after_e13 e14 (ev_sent :: []) suffix_sent suffix_received final after_e14;
    // now: conn_events_sent_seal_replay after_e14 [ev_sent] suffix_sent suffix_received final
    eliminate
       (PNTCAS.client_no_tail_application_write_install_event e13 /\
        PNTCAS.client_no_tail_application_read_install_event e14) \/
       (PNTCAS.client_no_tail_application_read_install_event e13 /\
        PNTCAS.client_no_tail_application_write_install_event e14)
    returns goal
    with _caseA.
    (
      PNTCAS.lemma_client_no_tail_application_write_install_event_step_model_as_plain after_verify after_e13 e13;
      PNTCAS.lemma_client_no_tail_application_read_install_event_step_model_as_plain after_e13 after_e14 e14;
      eliminate exists cawm. CS.step_model after_verify (iaw cawm) == Some after_e13
      returns goal
      with _pw.
      (
        eliminate exists carm. CS.step_model after_e13 (iar carm) == Some after_e14
        returns goal
        with _pr.
        (
          plain_write_install_legal after_verify after_e13 e13 cawm;
          plain_read_install_legal after_e13 after_e14 e14 carm;
          peel_local_construct after_e13 (iar carm) (ev_sent :: []) suffix_sent suffix_received final after_e14;
          peel_local_construct after_verify (iaw cawm) (iar carm :: ev_sent :: []) suffix_sent suffix_received final after_e13;
          peel_local_construct model12 ev_vf (iaw cawm :: iar carm :: ev_sent :: []) suffix_sent suffix_received final after_verify;
          assert goal
        )
      )
    )
    and _caseB.
    (
      PNTCAS.lemma_client_no_tail_application_read_install_event_step_model_as_plain after_verify after_e13 e13;
      PNTCAS.lemma_client_no_tail_application_write_install_event_step_model_as_plain after_e13 after_e14 e14;
      eliminate exists carm. CS.step_model after_verify (iar carm) == Some after_e13
      returns goal
      with _pr.
      (
        eliminate exists cawm. CS.step_model after_e13 (iaw cawm) == Some after_e14
        returns goal
        with _pw.
        (
          plain_read_install_legal after_verify after_e13 e13 carm;
          plain_write_install_legal after_e13 after_e14 e14 cawm;
          install_commute_full after_verify cawm carm after_e13 after_e14;
          eliminate exists aw. (CS.step_model after_verify (iaw cawm) == Some aw /\ CS.step_model aw (iar carm) == Some after_e14 /\ CS.legal_event after_verify (iaw cawm) /\ CS.legal_event aw (iar carm))
          returns goal
          with _cm.
          (
            peel_local_construct aw (iar carm) (ev_sent :: []) suffix_sent suffix_received final after_e14;
            peel_local_construct after_verify (iaw cawm) (iar carm :: ev_sent :: []) suffix_sent suffix_received final aw;
            peel_local_construct model12 ev_vf (iaw cawm :: iar carm :: ev_sent :: []) suffix_sent suffix_received final after_verify;
            assert goal
          )
        )
      )
    )
  )
#pop-options

// ===== end HOLE-4 reconstruction machinery =====

// ===== HOLE-4 packaging: compact exact-slice + reconstruction + client wire record =====
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2 --split_queries always"
noextract
let lemma_h4_client_exact_recon (client server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        SMReplay.connection_state_sent_seal_replay_consistent client /\
        clean16_cleartext_final_hello_slot_milestone client server)
      (ensures
        (exists (model12:CS.connection_model) (sf cf:GFin.finished)
           (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model)
           (suffix_sent suffix_received prefix_sent frag:B.bytes)
           (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
           (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
           (cv:GCV.certificateVerify) (e13 e14:CS.conn_event) (prefix_received:B.bytes).
           Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent suffix_sent) /\
           W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent) /\
           CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
           SMReplay.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received client.CS.cs_model /\
           SMReplay.conn_events_sent_seal_replay
             (CS.initial_model client.CS.cs_model.CS.model_config)
             (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
              e4 :: e5 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
              [])
             prefix_sent prefix_received model12 /\
           client.CS.cs_event_log ==
             (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
              e4 :: e5 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
              e13 :: e14 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); }) ::
              [])))
=
  PNTCFR.lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone client server;
  let goalp : prop =
    (exists (model12:CS.connection_model) (sf cf:GFin.finished)
       (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model)
       (suffix_sent suffix_received prefix_sent frag:B.bytes)
       (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
       (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
       (cv:GCV.certificateVerify) (e13 e14:CS.conn_event) (prefix_received:B.bytes).
       Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent suffix_sent) /\
       W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent) /\
       CS.step_model model12 (ev_vf_of sf) == Some av /\
       CS.step_model av (iaw cawm) == Some aw /\
       CS.step_model aw (iar carm) == Some ar /\
       CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
       SMReplay.conn_events_sent_seal_replay model12
         (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
         suffix_sent suffix_received client.CS.cs_model /\
       SMReplay.conn_events_sent_seal_replay
         (CS.initial_model client.CS.cs_model.CS.model_config)
         (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
          e4 :: e5 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
          CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
          [])
         prefix_sent prefix_received model12 /\
       client.CS.cs_event_log ==
         (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
          e4 :: e5 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
          CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
          e13 :: e14 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); }) ::
          [])) in
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf
    (model12:CS.connection_model) prefix_sent prefix_received suffix_sent suffix_received.
    (
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      e4 ::
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
      e13 ::
      e14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    SMReplay.conn_events_sent_seal_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello sh);
       }) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
       e4 ::
       e5 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Certificate cert);
       }) ::
       CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
       }) ::
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Finished sf);
       }) ::
       [])
      prefix_sent
      prefix_received
      model12 /\
    SMReplay.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model

    )
  returns goalp
  with _ex.
  (
    lemma_cover_to_self_install_replay model12 sf e13 e14 cf suffix_sent suffix_received client.CS.cs_model;
    eliminate exists client_start client_ch client_sh client_shared2 client_rest
                     server_ch selection server_shared server_sh server_rest.
      (PNTRB.role_local_cleartext_prefix_shape client server
         client_start client_ch client_sh client_shared2 client_rest
         server_ch selection server_shared server_sh server_rest /\
       WFL.supported_client_hello_wire_profile client_ch /\
       B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640 /\
       PNTRB.normalized_cleartext_raw_wire_bridge client_ch server_ch client_sh server_sh /\
       client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
       client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
       server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
       server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh)
    returns goalp
    with _prof.
    (
      assert (ch == client_ch);
      lemma_client_exact_prefix_sent_ch
        (CS.initial_model client.CS.cs_model.CS.model_config)
        start ch sh client_shared e4 e5 ee cert peer cv sf
        prefix_sent prefix_received model12;
      lemma_client_hello_sent_is_wire_h4 ch prefix_sent;
      eliminate exists frag.
        W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent)
      returns goalp
      with _wire.
      (
        eliminate exists (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model).
          (CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
           SMReplay.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received client.CS.cs_model)
        returns goalp
        with _rec.
        (
          introduce exists (model12':CS.connection_model) (sf':GFin.finished) (cf':GFin.finished)
             (cawm':CS.traffic_key_material) (carm':CS.traffic_key_material)
             (av':CS.connection_model) (aw':CS.connection_model) (ar':CS.connection_model)
             (suffix_sent':B.bytes) (suffix_received':B.bytes) (prefix_sent':B.bytes) (frag':B.bytes)
             (start':CS.handshake_start) (ch':GCH.clientHello) (sh':GSH.serverHello) (client_shared':C.x25519_shared_secret)
             (e4' e5':CS.conn_event) (ee':GEE.encryptedExtensions) (cert':GCert.certificate) (peer':X.peer_identity)
             (cv':GCV.certificateVerify) (e13' e14':CS.conn_event) (prefix_received':B.bytes).
             (Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent' suffix_sent') /\
              W.parse_record_wire prefix_sent' == Some (T.Handshake, frag', B.length prefix_sent') /\
              CS.step_model model12' (ev_vf_of sf') == Some av' /\
              CS.step_model av' (iaw cawm') == Some aw' /\
              CS.step_model aw' (iar carm') == Some ar' /\
              CS.step_model ar' (ev_sent_of cf') == Some client.CS.cs_model /\
              SMReplay.conn_events_sent_seal_replay model12'
                (ev_vf_of sf' :: iaw cawm' :: iar carm' :: ev_sent_of cf' :: [])
                suffix_sent' suffix_received' client.CS.cs_model /\
              SMReplay.conn_events_sent_seal_replay
                (CS.initial_model client.CS.cs_model.CS.model_config)
                (CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh'); }) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
                 e4' :: e5' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert'); }) ::
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf'); }) ::
                 [])
                prefix_sent' prefix_received' model12' /\
              client.CS.cs_event_log ==
                (CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh'); }) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
                 e4' :: e5' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert'); }) ::
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
                 e13' :: e14' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf'); }) ::
                 []))
          with model12 sf cf cawm carm av aw ar suffix_sent suffix_received prefix_sent frag
               start ch sh client_shared e4 e5 ee cert peer cv e13 e14 prefix_received
          and ()
        )
      )
    )
  )
#pop-options


// ============================================================
// HOLE 3 helpers (client-write/server-read alignment) — ported
// ============================================================
#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_client_write_install_normalize
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_write_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures
        (exists (mat:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule m.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
          CS.step_model m
            (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
              { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
            == Some m'))
=
  PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
        == Some m'
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
        == Some m'
    with role_install.CS.install_payload.CS.install_material and ()
#pop-options

#push-options "--z3rlimit 10 --ifuel 2"
noextract
let install_preserves_hs_secret_transcript
  (m m':CS.connection_model) (ev:CS.local_event)
  : Lemma
      (requires
        (CS.LocalInstallTrafficKeys? ev \/ CS.LocalInstallTrafficKeysForRole? ev) /\
        CS.step_model m (CS.ConnLocalEvent ev) == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
        m'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          == m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
= ()
#pop-options

#push-options "--z3rlimit 10 --ifuel 2"
noextract
let lemma_client_read_install_preserves_record_write
  (ev:CS.conn_event)
  : Lemma
      (requires PCPS.client_no_tail_handshake_read_install_event ev)
      (ensures
        CS.ConnLocalEvent? ev /\
        PWL.local_event_preserves_record_write (CS.ConnLocalEvent?._0 ev))
=
  PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
#pop-options

#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_client_identity_determinism
  (initial model4_c client_after_installs_c c_after3 model12_ex:CS.connection_model)
  (pre4 two six:list CS.conn_event)
  (ps pr rs1 rr1 rs2 rr2 rs3 rr3:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay initial
          (L.append pre4 (L.append two six)) ps pr model12_ex /\
        SMReplay.conn_events_received_decode_replay initial pre4 rs1 rr1 model4_c /\
        SMReplay.conn_events_received_decode_replay model4_c two rs2 rr2 client_after_installs_c /\
        SMReplay.conn_events_received_decode_replay client_after_installs_c six rs3 rr3 c_after3)
      (ensures model12_ex == c_after3)
=
  // split P12 = pre4 ++ (two ++ six)
  PWReplay.lemma_conn_events_sent_seal_replay_append_split
    initial pre4 (L.append two six) ps pr model12_ex;
  eliminate exists mid1 ps1 pr1 ss1 sr1.
    Seq.equal ps (B.append ps1 ss1) /\ Seq.equal pr (B.append pr1 sr1) /\
    SMReplay.conn_events_sent_seal_replay initial pre4 ps1 pr1 mid1 /\
    SMReplay.conn_events_sent_seal_replay mid1 (L.append two six) ss1 sr1 model12_ex
  returns model12_ex == c_after3
  with _.
  (
    PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
      initial pre4 ps1 pr1 mid1 rs1 rr1 model4_c;
    // mid1 == model4_c
    PWReplay.lemma_conn_events_sent_seal_replay_append_split
      model4_c two six ss1 sr1 model12_ex;
    eliminate exists mid2 ps2 pr2 ss2 sr2.
      Seq.equal ss1 (B.append ps2 ss2) /\ Seq.equal sr1 (B.append pr2 sr2) /\
      SMReplay.conn_events_sent_seal_replay model4_c two ps2 pr2 mid2 /\
      SMReplay.conn_events_sent_seal_replay mid2 six ss2 sr2 model12_ex
    returns model12_ex == c_after3
    with _.
    (
      PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
        model4_c two ps2 pr2 mid2 rs2 rr2 client_after_installs_c;
      // mid2 == client_after_installs_c
      PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
        client_after_installs_c six ss2 sr2 model12_ex rs3 rr3 c_after3
    )
  )
#pop-options

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_server_read_install_normalize
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PNTSS.server_no_tail_handshake_read_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures
        (exists (mat:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint m.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
          CS.step_model m
            (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }; }))
            == Some m'))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }; }))
        == Some m'
    with role_install.CS.install_payload.CS.install_material and ()
#pop-options

#push-options "--z3rlimit 10 --ifuel 2"
noextract
let lemma_server_write_install_preserves_record_read
  (ev:CS.conn_event)
  : Lemma
      (requires PNTSS.server_no_tail_handshake_write_install_event ev)
      (ensures
        CS.ConnLocalEvent? ev /\
        PWL.local_event_preserves_record_read (CS.ConnLocalEvent?._0 ev))
= ()
#pop-options

#push-options "--z3rlimit 10 --ifuel 2 --split_queries always"
noextract
let lemma_hole3_alignment_covers
  (model5_r server_after_e5_r server_rr:CS.connection_model)
  (e5_r e6_r:CS.conn_event)
  (model4_c client_after_e4_c client_after_installs_c:CS.connection_model)
  (e4_c e5_c:CS.conn_event)
  : Lemma
      (requires
        (match
          model5_r.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
         with
         | Some ss, Some cs -> Seq.equal ss cs
         | _, _ -> False) /\
        Seq.equal
          model5_r.CS.model_handshake.CS.hs_transcript
          model4_c.CS.model_handshake.CS.hs_transcript /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        CS.legal_event model5_r e5_r /\
        CS.step_model model5_r e5_r == Some server_after_e5_r /\
        CS.legal_event server_after_e5_r e6_r /\
        CS.step_model server_after_e5_r e6_r == Some server_rr /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c)
      (ensures PWL.write_read_record_material_aligned client_after_installs_c server_rr)
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5_r e6_r;
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4_c e5_c;
  // helper: apply RA:500 at (cwpre, srpre) -> align(cwpost, srpost)
  let apply_ra (cwpre cwpost srpre srpost:CS.connection_model) (mat_w mat_r:CS.traffic_key_material)
    : Lemma
        (requires
          (match cwpre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
                 srpre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
           | Some a, Some b -> Seq.equal a b | _,_ -> False) /\
          Seq.equal cwpre.CS.model_handshake.CS.hs_transcript srpre.CS.model_handshake.CS.hs_transcript /\
          CS.traffic_install_matches_key_schedule cwpre.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint srpre.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
          CS.step_model cwpre (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some cwpost /\
          CS.step_model srpre (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some srpost)
        (ensures PWL.write_read_record_material_aligned cwpost srpost)
    = RA.lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
        cwpre srpre mat_w mat_r cwpost srpost
  in
  // push client read install (sender) from a->b, keeping receiver r
  let push_client_read (a b r:CS.connection_model) (ev:CS.conn_event)
    : Lemma
        (requires
          PCPS.client_no_tail_handshake_read_install_event ev /\
          CS.step_model a ev == Some b /\
          PWL.write_read_record_material_aligned a r)
        (ensures PWL.write_read_record_material_aligned b r)
    = lemma_client_read_install_preserves_record_write ev;
      (match ev with
       | CS.ConnLocalEvent le ->
         RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment a le b r)
  in
  // push server write install (receiver) from a->b, keeping sender s
  let push_server_write (s a b:CS.connection_model) (ev:CS.conn_event)
    : Lemma
        (requires
          PNTSS.server_no_tail_handshake_write_install_event ev /\
          CS.step_model a ev == Some b /\
          PWL.write_read_record_material_aligned s a)
        (ensures PWL.write_read_record_material_aligned s b)
    = lemma_server_write_install_preserves_record_read ev;
      (match ev with
       | CS.ConnLocalEvent le ->
         RA.lemma_step_receiver_local_event_preserves_write_read_record_material_alignment s a le b)
  in
  eliminate
    (PNTSS.server_no_tail_handshake_write_install_event e5_r /\ PNTSS.server_no_tail_handshake_read_install_event e6_r) \/
    (PNTSS.server_no_tail_handshake_read_install_event e5_r /\ PNTSS.server_no_tail_handshake_write_install_event e6_r)
  returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
  with _sw. (
    // server write-first: e5_r=write, e6_r=read. server read-pre = server_after_e5_r (== model5_r secret via preserve)
    install_preserves_hs_secret_transcript model5_r server_after_e5_r (CS.ConnLocalEvent?._0 e5_r);
    lemma_server_read_install_normalize server_after_e5_r server_rr e6_r;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint server_after_e5_r.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model server_after_e5_r (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some server_rr
    returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
    with _sr2. (
      eliminate
        (PCPS.client_no_tail_handshake_write_install_event e4_c /\ PCPS.client_no_tail_handshake_read_install_event e5_c) \/
        (PCPS.client_no_tail_handshake_read_install_event e4_c /\ PCPS.client_no_tail_handshake_write_install_event e5_c)
      returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
      with _cw. (
        // client write-first: e4_c=write@model4_c
        lemma_client_write_install_normalize model4_c client_after_e4_c e4_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule model4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model model4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_e4_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra model4_c client_after_e4_c server_after_e5_r server_rr mat_w mat_r;
          push_client_read client_after_e4_c client_after_installs_c server_rr e5_c
        )
      )
      and _cr. (
        // client read-first: e4_c=read, e5_c=write@client_after_e4_c
        lemma_read_install_preserves_hs_secret_transcript model4_c client_after_e4_c e4_c;
        lemma_client_write_install_normalize client_after_e4_c client_after_installs_c e5_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule client_after_e4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model client_after_e4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_installs_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra client_after_e4_c client_after_installs_c server_after_e5_r server_rr mat_w mat_r
        )
      )
    )
  )
  and _sr. (
    // server read-first: e5_r=read@model5_r, e6_r=write@server_after_e5_r. server read-pre = model5_r
    lemma_server_read_install_normalize model5_r server_after_e5_r e5_r;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint model5_r.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model model5_r (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some server_after_e5_r
    returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
    with _sr2. (
      eliminate
        (PCPS.client_no_tail_handshake_write_install_event e4_c /\ PCPS.client_no_tail_handshake_read_install_event e5_c) \/
        (PCPS.client_no_tail_handshake_read_install_event e4_c /\ PCPS.client_no_tail_handshake_write_install_event e5_c)
      returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
      with _cw. (
        // client write-first
        lemma_client_write_install_normalize model4_c client_after_e4_c e4_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule model4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model model4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_e4_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra model4_c client_after_e4_c model5_r server_after_e5_r mat_w mat_r;
          push_client_read client_after_e4_c client_after_installs_c server_after_e5_r e5_c;
          push_server_write client_after_installs_c server_after_e5_r server_rr e6_r
        )
      )
      and _cr. (
        // client read-first
        lemma_read_install_preserves_hs_secret_transcript model4_c client_after_e4_c e4_c;
        lemma_client_write_install_normalize client_after_e4_c client_after_installs_c e5_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule client_after_e4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model client_after_e4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_installs_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra client_after_e4_c client_after_installs_c model5_r server_after_e5_r mat_w mat_r;
          push_server_write client_after_installs_c server_after_e5_r server_rr e6_r
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_server_prefix_slots_received
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_client_hello == None /\
        m0.CS.model_handshake.CS.hs_server_hello == None /\
        (exists rs rr.
          SMReplay.conn_events_received_decode_replay m0
            (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
            rs rr model5))
      (ensures
        model5.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model5.CS.model_handshake.CS.hs_server_hello == Some sh /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared)
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  peel_received m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_received m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);
  peel_received m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_received m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared);
  peel_received m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_received m5 model5;
  assert (m5.CS.model_handshake.CS.hs_server_hello == Some sh)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_server_prefix_secret_transcript_received
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_transcript == B.empty /\
        m0.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        (exists rs rr.
          SMReplay.conn_events_received_decode_replay m0
            (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
            rs rr model5))
      (ensures
        model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared) /\
        Seq.equal
          model5.CS.model_handshake.CS.hs_transcript
          (B.append (W.serialize_handshake (M.ClientHello ch))
                    (W.serialize_handshake (M.ServerHello sh))))
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  peel_received m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_received m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  peel_received m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_received m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared));
  peel_received m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_received m5 model5;
  assert (Seq.equal m1.CS.model_handshake.CS.hs_transcript B.empty);
  assert (Seq.equal m2.CS.model_handshake.CS.hs_transcript (W.serialize_handshake (M.ClientHello ch)))
#pop-options

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_cf_client_walk
  (client_after_installs_c receiver final:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:TLS13.X509.Spec.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  : Lemma
      (requires
        PWL.write_read_record_material_aligned client_after_installs_c receiver /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay client_after_installs_c
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr final))
      (ensures PWL.write_read_record_material_aligned final receiver)
=
  let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev2 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev4 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev5 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let m0 = client_after_installs_c in
  peel_received m0 ev0 [ev1;ev2;ev3;ev4;ev5] final;
  let m1 = step_next m0 ev0 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m0 (M.TlsHandshake (M.EncryptedExtensions ee)) m1 receiver;
  peel_received m1 ev1 [ev2;ev3;ev4;ev5] final;
  let m2 = step_next m1 ev1 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m1 (M.TlsHandshake (M.Certificate cert)) m2 receiver;
  peel_received m2 ev2 [ev3;ev4;ev5] final;
  let m3 = step_next m2 ev2 in
  RA.lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment m2 (CS.LocalValidateCertificate peer) m3 receiver;
  peel_received m3 ev3 [ev4;ev5] final;
  let m4 = step_next m3 ev3 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m3 (M.TlsHandshake (M.CertificateVerify cv)) m4 receiver;
  peel_received m4 ev4 [ev5] final;
  let m5 = step_next m4 ev4 in
  RA.lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment m4 (CS.LocalVerifyCertificateSignature cv) m5 receiver;
  peel_received m5 ev5 [] final;
  let m6 = step_next m5 ev5 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m5 (M.TlsHandshake (M.Finished sf)) m6 receiver;
  peel_nil_received m6 final
#pop-options

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_cf_server_walk
  (sender server_rr final:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  : Lemma
      (requires
        PWL.write_read_record_material_aligned sender server_rr /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay server_rr
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr final))
      (ensures PWL.write_read_record_material_aligned sender final)
=
  let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev2 = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let m0 = server_rr in
  peel_received m0 ev0 [ev1;ev2;ev3;ev4] final;
  let m1 = step_next m0 ev0 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m0 (M.TlsHandshake (M.EncryptedExtensions ee)) m1;
  peel_received m1 ev1 [ev2;ev3;ev4] final;
  let m2 = step_next m1 ev1 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m1 (M.TlsHandshake (M.Certificate cert)) m2;
  peel_received m2 ev2 [ev3;ev4] final;
  let m3 = step_next m2 ev2 in
  RA.lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment sender m2 (CS.LocalSignCertificateVerify cv) m3;
  peel_received m3 ev3 [ev4] final;
  let m4 = step_next m3 ev3 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m3 (M.TlsHandshake (M.CertificateVerify cv)) m4;
  peel_received m4 ev4 [] final;
  let m5 = step_next m4 ev4 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m4 (M.TlsHandshake (M.Finished sf)) m5;
  peel_nil_received m5 final
#pop-options

noextract
let cf_six (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
         (cv:GCV.certificateVerify) (sf:GFin.finished) : list CS.conn_event =
  [
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); };
    CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
    CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); };
  ]

// End-to-end combiner: tie _x/_c witnesses via two log-eqs, then determinism

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_extract_client_two_six
  (model4_c client_after_e4_c client_after_installs_c c_after3 finalm:CS.connection_model)
  (e4_c e5_c:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (tail:list CS.conn_event) (rs rr:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c :: (L.append (cf_six ee cert peer cv sf) tail)) rs rr finalm /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }))
      (ensures
        (exists a b. SMReplay.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c) /\
        (exists a b. SMReplay.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3))
=
  let six = cf_six ee cert peer cv sf in
  // e4::e5::(six++tail) == [e4;e5] ++ (six++tail)
  assert (e4_c :: e5_c :: (L.append six tail) == L.append [e4_c; e5_c] (L.append six tail));
  PWReplay.lemma_conn_events_received_decode_replay_append_split
    model4_c [e4_c; e5_c] (L.append six tail) rs rr finalm;
  eliminate exists mid1 ps1 pr1 ss1 sr1.
    Seq.equal rs (B.append ps1 ss1) /\ Seq.equal rr (B.append pr1 sr1) /\
    SMReplay.conn_events_received_decode_replay model4_c [e4_c; e5_c] ps1 pr1 mid1 /\
    SMReplay.conn_events_received_decode_replay mid1 (L.append six tail) ss1 sr1 finalm
  returns
    ((exists a b. SMReplay.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c) /\
     (exists a b. SMReplay.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3))
  with _.
  (
    // mid1 == client_after_installs_c via peel
    peel_received model4_c e4_c [e5_c] mid1;
    peel_received (step_next model4_c e4_c) e5_c [] mid1;
    peel_nil_received (step_next (step_next model4_c e4_c) e5_c) mid1;
    assert (mid1 == client_after_installs_c);
    introduce exists a b. SMReplay.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c
    with ps1 pr1 and ();
    // split six ++ tail
    PWReplay.lemma_conn_events_received_decode_replay_append_split
      client_after_installs_c six tail ss1 sr1 finalm;
    eliminate exists mid2 ps2 pr2 ss2 sr2.
      Seq.equal ss1 (B.append ps2 ss2) /\ Seq.equal sr1 (B.append pr2 sr2) /\
      SMReplay.conn_events_received_decode_replay client_after_installs_c six ps2 pr2 mid2 /\
      SMReplay.conn_events_received_decode_replay mid2 tail ss2 sr2 finalm
    returns (exists a b. SMReplay.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3)
    with _.
    (
      let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
      let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
      let ev2 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
      let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
      let ev4 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
      let ev5 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
      peel_received client_after_installs_c ev0 [ev1;ev2;ev3;ev4;ev5] mid2;
      let n1 = step_next client_after_installs_c ev0 in
      peel_received n1 ev1 [ev2;ev3;ev4;ev5] mid2;
      let n2 = step_next n1 ev1 in
      peel_received n2 ev2 [ev3;ev4;ev5] mid2;
      let n3 = step_next n2 ev2 in
      peel_received n3 ev3 [ev4;ev5] mid2;
      let n4 = step_next n3 ev3 in
      peel_received n4 ev4 [ev5] mid2;
      let n5 = step_next n4 ev4 in
      peel_received n5 ev5 [] mid2;
      let n6 = step_next n5 ev5 in
      peel_nil_received n6 mid2;
      assert (mid2 == c_after3);
      introduce exists a b. SMReplay.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3
      with ps2 pr2 and ()
    )
  )
#pop-options

#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_extract_server_covers_flight
  (model5_r server_rr' server_rr after_server_flight_r:CS.connection_model)
  (e5_r e6_r:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (rs rr:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model5_r
          [
            e5_r;
            e6_r;
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr after_server_flight_r /\
        server_rr' == step_next model5_r e5_r /\
        server_rr == step_next server_rr' e6_r)
      (ensures
        CS.legal_event model5_r e5_r /\
        CS.step_model model5_r e5_r == Some server_rr' /\
        CS.legal_event server_rr' e6_r /\
        CS.step_model server_rr' e6_r == Some server_rr /\
        (exists a b. SMReplay.conn_events_received_decode_replay server_rr
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          a b after_server_flight_r))
=
  let f0 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let f1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let f2 = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let f3 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let f4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  peel_received model5_r e5_r [e6_r; f0; f1; f2; f3; f4] after_server_flight_r;
  peel_received server_rr' e6_r [f0; f1; f2; f3; f4] after_server_flight_r
#pop-options

// server final slots via received-decode _cr chain (two-segment)
#push-options "--z3rlimit 10 --split_queries always --ifuel 2 --fuel 16"
noextract
let lemma_server_final_slots_received
  (server:CS.connection_state)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv:GCV.certificateVerify) (sf:GFin.finished)
  (server_app_write_material server_app_read_material:CS.traffic_key_material) (cf:GFin.finished)
  (model5_r after_server_flight_r:CS.connection_model)
  : Lemma
      (requires
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
           rs rr model5_r) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
           ]
           rs rr after_server_flight_r) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
           ]
           rs rr server.CS.cs_model))
      (ensures
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared)
=
  let m0 = CS.initial_model server.CS.cs_model.CS.model_config in
  assert (m0.CS.model_handshake.CS.hs_client_hello == None);
  assert (m0.CS.model_handshake.CS.hs_server_hello == None);
  lemma_server_prefix_slots_received m0 ch selection server_shared sh model5_r;
  let flight =
    [
      e5_r; e6_r;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
    ] in
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5_r e6_r;
  assert (all_not_hello flight);
  lemma_received_replay_preserves_slots model5_r flight after_server_flight_r;
  let cfin =
    [
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material; }; });
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material; }; });
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
    ] in
  assert (all_not_hello cfin);
  lemma_received_replay_preserves_slots after_server_flight_r cfin server.CS.cs_model
#pop-options



// ============================================================
// HOLE 3 bundle: shared-secret (received), alignment core, client identity
// ============================================================
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2 --split_queries always"
noextract
let lemma_shared_secret_eq_received
  (client server:CS.connection_state)
  (ch_r:GCH.clientHello) (selection_r:CS.server_handshake_selection)
  (server_shared_r:C.x25519_shared_secret) (sh_r:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee_r:GEE.encryptedExtensions) (cert_r:GCert.certificate) (cv_r:GCV.certificateVerify)
  (sf_r:GFin.finished) (cf_r:GFin.finished)
  (server_app_write_material_r server_app_read_material_r:CS.traffic_key_material)
  (model5_r after_server_flight_r:CS.connection_model)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (model4_c:CS.connection_model)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_r selection_r server_shared_r sh_r)
           rs rr model5_r) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_r); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_r); }
           ]
           rs rr after_server_flight_r) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_r; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_r); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_r; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
           ]
           rs rr server.CS.cs_model) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay model4_c
           (e4_c :: e5_c ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
              e13_c;
              e14_c;
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
            ])
           rs rr client.CS.cs_model))
      (ensures Seq.equal server_shared_r client_shared_c)
=
  lemma_server_final_slots_received server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_app_write_material_r server_app_read_material_r cf_r
    model5_r after_server_flight_r;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c
    (e4_c :: e5_c ::
     [
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
       CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
       CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
       e13_c;
       e14_c;
       CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
     ]);
  Pairing.lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
    client server;
  CSL.lemma_paired_x25519_key_shares_shared_secret_agree client server;
  assert (Seq.equal client_shared_c server_shared_r)
#pop-options

// focused congruence: rewrite the client suffix's explicit tail into cf_six ++ tail form
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2"
noextract
let lemma_client_suffix_append_form
  (model4_c finalm:CS.connection_model)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (suffix_sent_c suffix_received_c:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c ::
           [
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
             CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
             CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
             CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
             e13_c;
             e14_c;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
           ])
          suffix_sent_c suffix_received_c finalm)
      (ensures
        SMReplay.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c ::
           (L.append (cf_six ee_c cert_c peer_c cv_c sf_c)
             [
               CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
               e13_c;
               e14_c;
               CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
             ]))
          suffix_sent_c suffix_received_c finalm)
=
  ()
#pop-options

#push-options "--z3rlimit 10 --fuel 16 --ifuel 2 --split_queries always"
noextract
let lemma_pack_cf_align_core
  (client server:CS.connection_state)
  (ch_r:GCH.clientHello) (selection_r:CS.server_handshake_selection)
  (server_shared_r:C.x25519_shared_secret) (sh_r:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee_r:GEE.encryptedExtensions) (cert_r:GCert.certificate) (cv_r:GCV.certificateVerify)
  (sf_r:GFin.finished) (cf_r:GFin.finished)
  (server_app_write_material_r server_app_read_material_r:CS.traffic_key_material)
  (model5_r after_server_flight_r:CS.connection_model)
  (server_flight_sent_r server_flight_received_r:B.bytes)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (model4_c client_after_e4_c client_after_installs_c c_after3:CS.connection_model)
  (suffix_sent_c suffix_received_c:B.bytes)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        clean16_cleartext_final_hello_slot_milestone client server /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_r selection_r server_shared_r sh_r)
           rs rr model5_r) /\
        SMReplay.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_r); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_r); }
           ]
           server_flight_sent_r server_flight_received_r after_server_flight_r /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_r; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_r); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_r; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
           ]
           rs rr server.CS.cs_model) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        SMReplay.conn_events_received_decode_replay model4_c
           (e4_c :: e5_c ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
              e13_c;
              e14_c;
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
            ])
           suffix_sent_c suffix_received_c client.CS.cs_model /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); }))
      (ensures PWL.write_read_record_material_aligned c_after3 after_server_flight_r)
=
  let server_rr' = step_next model5_r e5_r in
  let server_rr = step_next server_rr' e6_r in
  let tail_c =
    [
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
      e13_c;
      e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
    ] in
  // establish model5_r / model4_c handshake-secret + transcript equality
  lemma_shared_secret_eq_received client server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r cf_r server_app_write_material_r server_app_read_material_r
    model5_r after_server_flight_r
    start_c ch_c sh_c client_shared_c e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c model4_c;
  lemma_server_prefix_secret_transcript_received
    (CS.initial_model server.CS.cs_model.CS.model_config)
    ch_r selection_r server_shared_r sh_r model5_r;
  lemma_client_prefix_secret_transcript
    (CS.initial_model client.CS.cs_model.CS.model_config)
    start_c ch_c sh_c client_shared_c model4_c;
  lemma_hs_secret_seq_eq server_shared_r client_shared_c;
  lemma_server_final_slots_received server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_app_write_material_r server_app_read_material_r cf_r
    model5_r after_server_flight_r;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c
    (e4_c :: e5_c ::
     [
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
       CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
       CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
       CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
       e13_c;
       e14_c;
       CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
     ]);
  lemma_checkpoint_th_sh_from_milestone client server;
  lemma_transcript_eq_from_checkpoint client server model5_r model4_c ch_r sh_r ch_c sh_c;
  assert (Seq.equal server_shared_r client_shared_c);
  assert (match
            model5_r.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
            model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          with
          | Some ss, Some cs -> Seq.equal ss cs
          | _, _ -> False);
  assert (Seq.equal model5_r.CS.model_handshake.CS.hs_transcript
                    model4_c.CS.model_handshake.CS.hs_transcript);
  // server covers + flight replay from _cr
  lemma_extract_server_covers_flight model5_r server_rr' server_rr after_server_flight_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_flight_sent_r server_flight_received_r;
  // STEP 1: install-adjacent alignment
  lemma_hole3_alignment_covers model5_r server_rr' server_rr e5_r e6_r
    model4_c client_after_e4_c client_after_installs_c e4_c e5_c;
  // client [e4;e5] and six segments (rewrite explicit tail into cf_six ++ tail form)
  lemma_client_suffix_append_form model4_c client.CS.cs_model
    e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c
    suffix_sent_c suffix_received_c;
  lemma_extract_client_two_six model4_c client_after_e4_c client_after_installs_c c_after3
    client.CS.cs_model e4_c e5_c ee_c cert_c peer_c cv_c sf_c tail_c
    suffix_sent_c suffix_received_c;
  // client walk: client_after_installs_c -> c_after3 (writer), receiver = server_rr
  lemma_cf_client_walk client_after_installs_c server_rr c_after3 ee_c cert_c peer_c cv_c sf_c;
  // server walk: server_rr -> after_server_flight_r (reader), sender = c_after3
  lemma_cf_server_walk c_after3 server_rr after_server_flight_r ee_r cert_r cv_r sf_r
#pop-options

#push-options "--z3rlimit 10 --fuel 16 --ifuel 2"
noextract
let lemma_client_prefix_append_form
  (initial model12:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished) (prefix_sent prefix_received:B.bytes)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay initial
          (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           e4 :: e5 ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
           [])
          prefix_sent prefix_received model12)
      (ensures
        SMReplay.conn_events_sent_seal_replay initial
          (L.append (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
                    (L.append [e4; e5] (cf_six ee cert peer cv sf)))
          prefix_sent prefix_received model12)
= ()
#pop-options

#push-options "--z3rlimit 10 --fuel 16 --ifuel 2 --split_queries always"
noextract
let lemma_cf_client_identity
  (client:CS.connection_state)
  (initial model4_c client_after_e4_c client_after_installs_c c_after3 model12_ex:CS.connection_model)
  // recon witnesses
  (start_x:CS.handshake_start) (ch_x:GCH.clientHello) (sh_x:GSH.serverHello) (shared_x:C.x25519_shared_secret)
  (e4_x e5_x:CS.conn_event) (ee_x:GEE.encryptedExtensions) (cert_x:GCert.certificate) (peer_x:X.peer_identity)
  (cv_x:GCV.certificateVerify) (sf_x:GFin.finished) (e13_x e14_x:CS.conn_event) (cf_x:GFin.finished)
  // _cc witnesses
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello) (shared_c:C.x25519_shared_secret)
  (e4_c e5_c:CS.conn_event) (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (e13_c e14_c:CS.conn_event) (cf_c:GFin.finished)
  (ps pr ps1 pr1 ss sr:B.bytes)
  : Lemma
      (requires
        // recon sent prefix replay over 12 recon events (EXPLICIT-12 form)
        SMReplay.conn_events_sent_seal_replay initial
          (CS.ConnLocalEvent (CS.LocalStartHandshake start_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_x); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared_x) ::
           e4_x :: e5_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_x); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_x); }) ::
           [])
          ps pr model12_ex /\
        // recon log-eq (16 recon events, EXPLICIT-16 form)
        client.CS.cs_event_log ==
          (CS.ConnLocalEvent (CS.LocalStartHandshake start_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_x); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared_x) ::
           e4_x :: e5_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_x); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyFinished sf_x) ::
           e13_x :: e14_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_x); }) ::
           []) /\
        // _cc log-eq (literal ordered_rest form)
        client.CS.cs_event_log ==
          L.append (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
            (e4_c :: e5_c ::
             [
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
               CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
               CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
               CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
               e13_c; e14_c;
               CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
             ]) /\
        // segment 1: prefix received
        SMReplay.conn_events_received_decode_replay initial
          (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c) ps1 pr1 model4_c /\
        // suffix received (literal ordered_rest form)
        SMReplay.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c ::
           [
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
             CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
             CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
             CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
             e13_c; e14_c;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
           ])
          ss sr client.CS.cs_model /\
        // step facts + c_after3 defn
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); }))
      (ensures model12_ex == c_after3)
=
  // convert recon prefix replay to append form
  lemma_client_prefix_append_form initial model12_ex start_x ch_x sh_x shared_x
    e4_x e5_x ee_x cert_x peer_x cv_x sf_x ps pr;
  // injectivity: _x == _c on the 12-event prefix
  assert (L.append (PWSeg.client_cleartext_handshake_prefix_events start_x ch_x sh_x shared_x)
                    (L.append [e4_x; e5_x] (cf_six ee_x cert_x peer_x cv_x sf_x))
          == L.append (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
                    (L.append [e4_c; e5_c] (cf_six ee_c cert_c peer_c cv_c sf_c)));
  // convert suffix to append form and extract segments 2,3
  lemma_client_suffix_append_form model4_c client.CS.cs_model
    e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c ss sr;
  lemma_extract_client_two_six model4_c client_after_e4_c client_after_installs_c c_after3
    client.CS.cs_model e4_c e5_c ee_c cert_c peer_c cv_c sf_c
    [ CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c); e13_c; e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); } ]
    ss sr;
  eliminate exists a2 b2. SMReplay.conn_events_received_decode_replay model4_c [e4_c; e5_c] a2 b2 client_after_installs_c
  returns model12_ex == c_after3
  with _.
  (
    eliminate exists a3 b3. SMReplay.conn_events_received_decode_replay client_after_installs_c (cf_six ee_c cert_c peer_c cv_c sf_c) a3 b3 c_after3
    returns model12_ex == c_after3
    with _.
    (
      lemma_client_identity_determinism initial model4_c client_after_installs_c c_after3 model12_ex
        (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
        [e4_c; e5_c] (cf_six ee_c cert_c peer_c cv_c sf_c)
        ps pr ps1 pr1 a2 b2 a3 b3
    )
  )
#pop-options
#pop-options

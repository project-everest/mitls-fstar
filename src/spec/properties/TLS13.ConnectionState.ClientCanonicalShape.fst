module TLS13.ConnectionState.ClientCanonicalShape

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module C = TLS13.Crypto.Spec
module T = TLS13.Types
module X = TLS13.X509.Spec
module EC = TLS13.Spec.Endpoint.Client
module WStep = TLS13.System.WireStep
module SMCan = TLS13.Spec.StateMachine.Canonical
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module SM = Common.StateMachine
module CW = TLS13.Spec.Endpoint.Wire
module CTy = TLS13.Impl.CanonicalTypes
module EAPI = TLS13.Spec.Endpoint.API
module B = TLS13.Bytes
module L = FStar.List.Tot
module CLem = TLS13.ConnectionState.Lemmas

(* ================================================================== *)
(* Milestone event constructors (match PWSeg prefix + the goal suffix) *)
(* ================================================================== *)

let ev_start (start:CS.handshake_start) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalStartHandshake start)

let ev_sent_ch (ch:GCH.clientHello) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  })

let ev_recv_sh (sh:GSH.serverHello) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  })

let ev_derive (shared:C.x25519_shared_secret) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)

let ev_recv_ee (ee:GEE.encryptedExtensions) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
  })

let ev_recv_cert (cert:GCert.certificate) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  })

let ev_recv_cv (cv:GCV.certificateVerify) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  })

let ev_recv_fin (sf:GFin.finished) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  })

let rec canonical_log_append (left right:list CS.conn_event)
  : Lemma
      (ensures
        canonical_log (L.append left right) ==
        L.append (canonical_log left) (canonical_log right))
      (decreases left)
=
  match left with
  | [] -> ()
  | _ :: rest -> canonical_log_append rest right

let rec lemma_append_nil (events:list CS.conn_event)
  : Lemma (L.append events [] == events)
  = match events with
    | [] -> ()
    | _ :: rest -> lemma_append_nil rest

let lemma_client_hs_install_canonical (ev:CS.conn_event)
  : Lemma
      (requires is_client_hs_install ev)
      (ensures canonical_event ev == ev)
  = match ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> ()
    | _ -> ()

(* The fixed cleartext prefix, as a pure list (matches PWSeg's definition). *)
let prefix (start:CS.handshake_start) (ch:GCH.clientHello)
           (sh:GSH.serverHello) (shared:C.x25519_shared_secret)
  : list CS.conn_event =
  PWSeg.client_cleartext_handshake_prefix_events start ch sh shared

let prefix_unfold (start:CS.handshake_start) (ch:GCH.clientHello)
                  (sh:GSH.serverHello) (shared:C.x25519_shared_secret)
  : Lemma (prefix start ch sh shared ==
           [ ev_start start; ev_sent_ch ch; ev_recv_sh sh; ev_derive shared ])
  = ()

let lemma_prefix_canonical (start:CS.handshake_start) (ch:GCH.clientHello)
                           (sh:GSH.serverHello) (shared:C.x25519_shared_secret)
  : Lemma
      (ensures canonical_log (prefix start ch sh shared) ==
               prefix start ch sh shared)
  = prefix_unfold start ch sh shared

(* The fixed encrypted-flight suffix (complete, through the server Finished),
   with the two local skips kept abstract. *)
let flight_suffix (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                  (validate:CS.local_event) (cv:GCV.certificateVerify)
                  (verifysig:CS.local_event) (sf:GFin.finished)
                  (tail:list CS.conn_event)
  : list CS.conn_event =
  ev_recv_ee ee :: ev_recv_cert cert :: CS.ConnLocalEvent validate ::
  ev_recv_cv cv :: CS.ConnLocalEvent verifysig :: ev_recv_fin sf :: tail

(* ================================================================== *)
(* Region predicates                                                   *)
(* ================================================================== *)

let all_hs_installs (region:list CS.conn_event) : prop =
  forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true

let rec lemma_hs_install_region_canonical (region:list CS.conn_event)
  : Lemma
      (requires all_hs_installs region)
      (ensures canonical_log region == region)
  = match region with
    | [] -> ()
    | ev :: rest ->
      lemma_client_hs_install_canonical ev;
      lemma_hs_install_region_canonical rest

let has_read_install (region:list CS.conn_event) : prop =
  exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er

let has_write_install (region:list CS.conn_event) : prop =
  exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew

#push-options "--fuel 8 --ifuel 2 --z3rlimit 20"
let rec append_left_cancel
  (left right0 right1:list CS.conn_event)
  : Lemma
      (requires L.append left right0 == L.append left right1)
      (ensures right0 == right1)
      (decreases left)
  = match left with
    | [] -> ()
    | _ :: rest -> append_left_cancel rest right0 right1

let rec canonical_log_length (events:list CS.conn_event)
  : Lemma (ensures L.length (canonical_log events) == L.length events)
      (decreases events)
  = match events with
    | [] -> ()
    | _ :: rest -> canonical_log_length rest

let lemma_delivers_handshake_singleton grp msg = ()

(** [canonical_event] only ever rewrites [ConnProtectedHandshake] events, and
    always into a [ConnNetworkEvent]; so a local event in its image was already
    that local event. *)
let lemma_canonical_event_local (ev:CS.conn_event) (le:CS.local_event)
  : Lemma
      (requires canonical_event ev == CS.ConnLocalEvent le)
      (ensures ev == CS.ConnLocalEvent le)
  = ()

let lemma_canonical_flight_raw_spine
  (raw_suffix:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event)
  (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event)
  (sf:GFin.finished)
  (tail:list CS.conn_event)
  : Lemma
      (requires
        canonical_log raw_suffix ==
          flight_suffix ee cert cv_validate cv cv_verify sf tail)
      (ensures
        raw_flight_spine raw_suffix ee cert cv_validate cv cv_verify sf tail)
  =
  canonical_log_length raw_suffix;
  assert (L.length (canonical_log raw_suffix) ==
          L.length (flight_suffix ee cert cv_validate cv cv_verify sf tail));
  assert_norm (L.length
    (flight_suffix ee cert cv_validate cv cv_verify sf tail) ==
    6 + L.length tail);
  match raw_suffix with
  | raw_ee :: raw_cert :: raw_validate :: raw_cv ::
    raw_verify :: raw_sf :: raw_tail ->
    ( assert_norm (canonical_log
          (raw_ee :: raw_cert :: raw_validate :: raw_cv ::
           raw_verify :: raw_sf :: raw_tail) ==
        canonical_event raw_ee :: canonical_event raw_cert ::
        canonical_event raw_validate :: canonical_event raw_cv ::
        canonical_event raw_verify :: canonical_event raw_sf ::
        canonical_log raw_tail);
      assert_norm (flight_suffix ee cert cv_validate cv cv_verify sf tail ==
        ev_recv_ee ee :: ev_recv_cert cert :: CS.ConnLocalEvent cv_validate ::
        ev_recv_cv cv :: CS.ConnLocalEvent cv_verify :: ev_recv_fin sf :: tail);
      assert (canonical_event raw_ee == ev_recv_ee ee);
      assert (canonical_event raw_cert == ev_recv_cert cert);
      assert (canonical_event raw_validate == CS.ConnLocalEvent cv_validate);
      assert (canonical_event raw_cv == ev_recv_cv cv);
      assert (canonical_event raw_verify == CS.ConnLocalEvent cv_verify);
      assert (canonical_event raw_sf == ev_recv_fin sf);
      assert (canonical_log raw_tail == tail);
      lemma_canonical_event_local raw_validate cv_validate;
      lemma_canonical_event_local raw_verify cv_verify;
      assert (L.append [raw_sf] raw_tail == raw_sf :: raw_tail);
      assert (L.append [raw_cv]
                (CS.ConnLocalEvent cv_verify :: L.append [raw_sf] raw_tail) ==
              raw_cv :: CS.ConnLocalEvent cv_verify :: raw_sf :: raw_tail);
      assert (L.append [raw_ee]
                (L.append [raw_cert]
                  (CS.ConnLocalEvent cv_validate ::
                    L.append [raw_cv]
                      (CS.ConnLocalEvent cv_verify ::
                        L.append [raw_sf] raw_tail))) == raw_suffix);
      assert (delivers_handshake [raw_ee] (M.EncryptedExtensions ee));
      assert (delivers_handshake [raw_cert] (M.Certificate cert));
      assert (delivers_handshake [raw_cv] (M.CertificateVerify cv));
      assert (delivers_handshake [raw_sf] (M.Finished sf));
      introduce exists
        (g_ee0 g_cert0 g_cv0 g_sf0 raw_tail0:list CS.conn_event).
        raw_suffix ==
          L.append g_ee0
            (L.append g_cert0
              (CS.ConnLocalEvent cv_validate ::
                L.append g_cv0
                  (CS.ConnLocalEvent cv_verify ::
                    L.append g_sf0 raw_tail0))) /\
        delivers_handshake g_ee0 (M.EncryptedExtensions ee) /\
        delivers_handshake g_cert0 (M.Certificate cert) /\
        delivers_handshake g_cv0 (M.CertificateVerify cv) /\
        delivers_handshake g_sf0 (M.Finished sf) /\
        canonical_log raw_tail0 == tail
      with [raw_ee] [raw_cert] [raw_cv] [raw_sf] raw_tail and () )
  | [] -> assert False
  | _ :: [] -> assert False
  | _ :: _ :: [] -> assert False
  | _ :: _ :: _ :: [] -> assert False
  | _ :: _ :: _ :: _ :: [] ->
    assert (L.length raw_suffix == 4);
    assert False
  | _ :: _ :: _ :: _ :: _ :: [] ->
    assert (L.length raw_suffix == 5);
    assert False
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_client_raw_suffix_flight_spine
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (region raw_suffix log:list CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv_validate:CS.local_event)
  (cv:GCV.certificateVerify)
  (cv_verify:CS.local_event)
  (sf:GFin.finished)
  (tail:list CS.conn_event)
  : Lemma
      (requires
        all_hs_installs region /\
        log == L.append (prefix start ch sh client_shared)
          (L.append region raw_suffix) /\
        canonical_log log == L.append (prefix start ch sh client_shared)
          (L.append region
            (flight_suffix ee cert cv_validate cv cv_verify sf tail)))
      (ensures
        raw_flight_spine raw_suffix ee cert cv_validate cv cv_verify sf tail)
  =
  let pfx = prefix start ch sh client_shared in
  let flight = flight_suffix ee cert cv_validate cv cv_verify sf tail in
  canonical_log_append pfx (L.append region raw_suffix);
  canonical_log_append region raw_suffix;
  lemma_prefix_canonical start ch sh client_shared;
  lemma_hs_install_region_canonical region;
  assert (canonical_log log ==
    L.append pfx (L.append region (canonical_log raw_suffix)));
  append_left_cancel pfx
    (L.append region (canonical_log raw_suffix))
    (L.append region flight);
  append_left_cancel region (canonical_log raw_suffix) flight;
  lemma_canonical_flight_raw_spine
    raw_suffix ee cert cv_validate cv cv_verify sf tail
#pop-options

#restart-solver
let region_installs_ok (keys:CS.key_schedule_state) (region:list CS.conn_event) : prop =
  all_hs_installs region /\
  (Some? keys.CS.ks_server_handshake_traffic ==> has_read_install region) /\
  (Some? keys.CS.ks_client_handshake_traffic ==> has_write_install region)

(* ================================================================== *)
(* The exact canonical log shape, as a function of the model           *)
(* ================================================================== *)

(* HsServerHelloReceived: log == prefix ++ region (after derive), or the fixed
   pre-derive log [start; sent_ch; recv_sh].  Handshake key installs (which grow
   [region]) are only legal at this control state. *)
let shr_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
  hs.CS.hs_validated_peer == None /\ hs.CS.hs_certificate_verify == None /\
  hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None /\
  (match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello with
   | Some start, Some ch, Some sh ->
     (match keys.CS.ks_shared_secret with
      | None ->
        region == [] /\
        keys.CS.ks_handshake_secret == None /\
        keys.CS.ks_client_handshake_traffic == None /\
        keys.CS.ks_server_handshake_traffic == None /\
        log == [ ev_start start; ev_sent_ch ch; ev_recv_sh sh ]
      | Some shared ->
        log == L.append (prefix start ch sh shared) region /\
        region_installs_ok keys region)
   | _ -> False)

(* HsEncryptedExtensionsReceived: region frozen, suffix [recv_ee]. *)
let eer_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions with
  | Some start, Some ch, Some sh, Some shared, Some ee ->
    hs.CS.hs_certificate == None /\ hs.CS.hs_validated_peer == None /\
    hs.CS.hs_certificate_verify == None /\ hs.CS.hs_certificate_verify_verified == false /\
    hs.CS.hs_server_finished == None /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region [ ev_recv_ee ee ])
  | _ -> False

(* HsCertificateReceived: region frozen, suffix [recv_ee; recv_cert]. *)
let cr_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                 (region:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert ->
    hs.CS.hs_validated_peer == None /\
    hs.CS.hs_certificate_verify == None /\ hs.CS.hs_certificate_verify_verified == false /\
    hs.CS.hs_server_finished == None /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region [ ev_recv_ee ee; ev_recv_cert cert ])
  | _ -> False

(* HsCertificateValidated: suffix [recv_ee; recv_cert; validate]. *)
let cvd_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) (validate:CS.local_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate,
        hs.CS.hs_validated_peer with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert, Some _ ->
    hs.CS.hs_certificate_verify == None /\ hs.CS.hs_certificate_verify_verified == false /\
    hs.CS.hs_server_finished == None /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region [ ev_recv_ee ee; ev_recv_cert cert;
                         CS.ConnLocalEvent validate ])
  | _ -> False

(* HsCertificateVerifyReceived: suffix [recv_ee; recv_cert; validate; recv_cv]. *)
let cvr_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) (validate:CS.local_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate,
        hs.CS.hs_validated_peer, hs.CS.hs_certificate_verify with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert, Some _, Some cv ->
    hs.CS.hs_certificate_verify_verified == false /\
    hs.CS.hs_server_finished == None /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region [ ev_recv_ee ee; ev_recv_cert cert;
                         CS.ConnLocalEvent validate; ev_recv_cv cv ])
  | _ -> False

(* HsCertificateVerifyVerified: suffix [recv_ee; recv_cert; validate; recv_cv; verifysig]. *)
let cvv_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event)
                  (validate:CS.local_event) (verifysig:CS.local_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate,
        hs.CS.hs_validated_peer, hs.CS.hs_certificate_verify with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert, Some _, Some cv ->
    hs.CS.hs_certificate_verify_verified == true /\
    hs.CS.hs_server_finished == None /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region [ ev_recv_ee ee; ev_recv_cert cert;
                         CS.ConnLocalEvent validate; ev_recv_cv cv;
                         CS.ConnLocalEvent verifysig ])
  | _ -> False

(* HsServerFinishedVerified: full flight, tail after the received server Finished. *)
let sfv_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event)
                  (validate:CS.local_event) (verifysig:CS.local_event)
                  (tail:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate,
        hs.CS.hs_validated_peer, hs.CS.hs_certificate_verify, hs.CS.hs_server_finished with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert, Some _, Some cv, Some sf ->
    hs.CS.hs_certificate_verify_verified == true /\
    hs.CS.hs_server_finished_verified == true /\
    Some? keys.CS.ks_server_handshake_traffic /\
    region_installs_ok keys region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region (flight_suffix ee cert validate cv verifysig sf tail))
  | _ -> False

(* ControlApplicationData: full flight, both installs present. *)
let appdata_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                      (region:list CS.conn_event)
                      (validate:CS.local_event) (verifysig:CS.local_event)
                      (tail:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_start, hs.CS.hs_client_hello, hs.CS.hs_server_hello,
        keys.CS.ks_shared_secret, hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate,
        hs.CS.hs_validated_peer, hs.CS.hs_certificate_verify, hs.CS.hs_server_finished with
  | Some start, Some ch, Some sh, Some shared, Some ee, Some cert, Some _, Some cv, Some sf ->
    hs.CS.hs_certificate_verify_verified == true /\
    Some? keys.CS.ks_server_handshake_traffic /\
    Some? keys.CS.ks_client_handshake_traffic /\
    all_hs_installs region /\ has_read_install region /\ has_write_install region /\
    (exists (raw_suffix:list CS.conn_event).
       log == L.append (prefix start ch sh shared)
         (L.append region raw_suffix)) /\
    canonical_log log == L.append (prefix start ch sh shared)
      (L.append region (flight_suffix ee cert validate cv verifysig sf tail))
  | _ -> False

let log_shape (m:CS.connection_model) (log:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match m.CS.model_control with
  | CS.ControlNew ->
    log == [] /\
    hs.CS.hs_start == None /\ hs.CS.hs_client_hello == None /\
    hs.CS.hs_server_hello == None /\ keys.CS.ks_shared_secret == None /\
    keys.CS.ks_handshake_secret == None /\
    keys.CS.ks_client_handshake_traffic == None /\ keys.CS.ks_server_handshake_traffic == None /\
    hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
    hs.CS.hs_validated_peer == None /\ hs.CS.hs_certificate_verify == None /\
    hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None
  | CS.ControlHandshaking CS.HsStarted ->
    (hs.CS.hs_client_hello == None /\ hs.CS.hs_server_hello == None /\
     keys.CS.ks_shared_secret == None /\
     keys.CS.ks_handshake_secret == None /\
     keys.CS.ks_client_handshake_traffic == None /\ keys.CS.ks_server_handshake_traffic == None /\
     hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
     hs.CS.hs_validated_peer == None /\ hs.CS.hs_certificate_verify == None /\
     hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None) /\
    (match hs.CS.hs_start with
     | Some start -> log == [ ev_start start ]
     | None -> False)
  | CS.ControlHandshaking CS.HsClientHelloSent ->
    (hs.CS.hs_server_hello == None /\ keys.CS.ks_shared_secret == None /\
     keys.CS.ks_handshake_secret == None /\
     keys.CS.ks_client_handshake_traffic == None /\ keys.CS.ks_server_handshake_traffic == None /\
     hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
     hs.CS.hs_validated_peer == None /\ hs.CS.hs_certificate_verify == None /\
     hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None) /\
    (match hs.CS.hs_start, hs.CS.hs_client_hello with
     | Some start, Some ch -> log == [ ev_start start; ev_sent_ch ch ]
     | _ -> False)
  | CS.ControlHandshaking CS.HsServerHelloReceived ->
    (exists (region:list CS.conn_event). shr_region_ok m log region)
  | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived ->
    (exists (region:list CS.conn_event). eer_region_ok m log region)
  | CS.ControlHandshaking CS.HsCertificateReceived ->
    (exists (region:list CS.conn_event). cr_region_ok m log region)
  | CS.ControlHandshaking CS.HsCertificateValidated ->
    (exists (region:list CS.conn_event) (validate:CS.local_event).
       cvd_region_ok m log region validate)
  | CS.ControlHandshaking CS.HsCertificateVerifyReceived ->
    (exists (region:list CS.conn_event) (validate:CS.local_event).
       cvr_region_ok m log region validate)
  | CS.ControlHandshaking CS.HsCertificateVerifyVerified ->
    (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event).
       cvv_region_ok m log region validate verifysig)
  | CS.ControlHandshaking CS.HsServerFinishedVerified ->
    (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
       (tail:list CS.conn_event).
       sfv_region_ok m log region validate verifysig tail)
  | CS.ControlApplicationData ->
    (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
       (tail:list CS.conn_event).
       appdata_region_ok m log region validate verifysig tail)
  | CS.ControlHandshaking CS.HsServerFinishedReceived -> False
  | _ -> True

(* ================================================================== *)
(* The exact canonical shape invariant                                 *)
(* ================================================================== *)

let client_canonical_shape (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint ==>
  log_shape st.CS.cs_model st.CS.cs_event_log

(* ================================================================== *)
(* Initial state                                                       *)
(* ================================================================== *)

let lemma_shape_initial (cfg:CS.connection_config)
  : Lemma (client_canonical_shape (CS.initial cfg))
  = ()

(* ================================================================== *)
(* Canonical event classification + extraction from client_step        *)
(* ================================================================== *)

let is_client_canonical_event (ev:CS.conn_event) : prop =
  match ev with
  | CS.ConnNetworkEvent msg ->
    (msg.CL.message_direction == CL.Received) \/
    (msg.CL.message_direction == CL.Sent /\
       (match msg.CL.message_value with
        | M.TlsHandshake (M.ClientHello _) -> True
        | M.TlsHandshake (M.Finished _) -> True
        | M.TlsApplicationData _ -> True
        | M.TlsAlert T.Close_notify -> True
        | M.TlsKeyUpdate _ -> True
        | _ -> False))
  | CS.ConnProtectedHandshake _ -> True
  | CS.ConnLocalEvent le ->
    (match le with
     | CS.LocalStartHandshake _ -> True
     | CS.LocalDeriveSharedSecret _ -> True
     | CS.LocalInstallTrafficKeys _ -> True
     | CS.LocalValidateCertificate _ -> True
     | CS.LocalVerifyCertificateSignature _ -> True
     | CS.LocalVerifyFinished _ -> True
     | CS.LocalDeliverApplicationData _ -> True
     | CS.LocalFail _ -> True
     | _ -> False)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_semantic_canonical (st:CS.connection_state) (sem:EC.local_event) (conn_ev:CS.conn_event)
  : Lemma (requires EC.client_local_event_matches st sem conn_ev)
          (ensures is_client_canonical_event conn_ev)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
#restart-solver
let lemma_client_step_facts
  (st0 s':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev s' out)
      (ensures
        (exists (conn_ev:CS.conn_event).
          s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
          CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
          CS.legal_event st0.CS.cs_model conn_ev /\
          is_client_canonical_event conn_ev))
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (EC.client_wire_received_event st0 wire conn_ev /\
         SMCan.canonical_wire_step st0 s' conn_ev
           (Common.WireFormat.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs)
      returns
        (exists (conn_ev:CS.conn_event).
          s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
          CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
          CS.legal_event st0.CS.cs_model conn_ev /\
          is_client_canonical_event conn_ev)
      with _.
      (
        assert (is_client_canonical_event conn_ev)
      )
    | SM.LocalEvent local ->
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (EC.client_representation_matches st0 local conn_ev /\
         EC.client_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         EC.client_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty)
      returns
        (exists (conn_ev:CS.conn_event).
          s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
          CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
          CS.legal_event st0.CS.cs_model conn_ev /\
          is_client_canonical_event conn_ev)
      with _.
      (
        CTy.lemma_client_local_event_semantic_exact st0 local conn_ev;
        lemma_semantic_canonical st0 (CTy.client_local_event_semantic local) conn_ev
      )
#pop-options

(* ================================================================== *)
(* Single-step preservation                                            *)
(* ================================================================== *)

let step_pre (st0 s':CS.connection_state) (conn_ev:CS.conn_event) : prop =
  client_canonical_shape st0 /\
  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
  CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
  CS.legal_event st0.CS.cs_model conn_ev /\
  is_client_canonical_event conn_ev /\
  is_received_ccs conn_ev == false

unfold
let hpre (st0 s':CS.connection_state) (conn_ev:CS.conn_event) : prop =
  log_shape st0.CS.cs_model st0.CS.cs_event_log /\
  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
  CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
  CS.legal_event st0.CS.cs_model conn_ev /\
  is_client_canonical_event conn_ev /\
  is_received_ccs conn_ev == false

(* ------------------------------------------------------------------ *)
(* Append / region snoc lemmas                                         *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let snoc_region (p r:list CS.conn_event) (x:CS.conn_event)
  : Lemma (L.append (L.append p r) [x] == L.append p (L.append r [x]))
  = L.append_assoc p r [x]

let snoc_tail (p r ss:list CS.conn_event) (x:CS.conn_event)
  : Lemma (L.append (L.append p (L.append r ss)) [x] ==
           L.append p (L.append r (L.append ss [x])))
  = L.append_assoc p (L.append r ss) [x];
    L.append_assoc r ss [x]

let raw_suffix_snoc
  (p region:list CS.conn_event)
  (old_log new_log:list CS.conn_event)
  (ev:CS.conn_event)
  : Lemma
      (requires
        (exists (raw_suffix:list CS.conn_event).
           old_log == L.append p (L.append region raw_suffix)) /\
        new_log == L.append old_log [ev])
      (ensures
        (exists (raw_suffix:list CS.conn_event).
           new_log == L.append p (L.append region raw_suffix)))
  = eliminate exists (raw_suffix:list CS.conn_event).
      old_log == L.append p (L.append region raw_suffix)
    returns
      (exists (raw_suffix':list CS.conn_event).
         new_log == L.append p (L.append region raw_suffix'))
    with _.
    ( snoc_tail p region raw_suffix ev;
      introduce exists (raw_suffix':list CS.conn_event).
          new_log == L.append p (L.append region raw_suffix')
      with (L.append raw_suffix [ev]) and () )

let cons_append (h:CS.conn_event) (l m:list CS.conn_event)
  : Lemma (L.append (h :: l) m == h :: (L.append l m))
  = ()

let flight_suffix_snoc (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                       (validate:CS.local_event) (cv:GCV.certificateVerify)
                       (verifysig:CS.local_event) (sf:GFin.finished)
                       (tail:list CS.conn_event) (x:CS.conn_event)
  : Lemma (L.append (flight_suffix ee cert validate cv verifysig sf tail) [x] ==
           flight_suffix ee cert validate cv verifysig sf (L.append tail [x]))
  = cons_append (ev_recv_ee ee)
      (ev_recv_cert cert :: CS.ConnLocalEvent validate :: ev_recv_cv cv ::
       CS.ConnLocalEvent verifysig :: ev_recv_fin sf :: tail) [x];
    cons_append (ev_recv_cert cert)
      (CS.ConnLocalEvent validate :: ev_recv_cv cv ::
       CS.ConnLocalEvent verifysig :: ev_recv_fin sf :: tail) [x];
    cons_append (CS.ConnLocalEvent validate)
      (ev_recv_cv cv :: CS.ConnLocalEvent verifysig :: ev_recv_fin sf :: tail) [x];
    cons_append (ev_recv_cv cv)
      (CS.ConnLocalEvent verifysig :: ev_recv_fin sf :: tail) [x];
    cons_append (CS.ConnLocalEvent verifysig) (ev_recv_fin sf :: tail) [x];
    cons_append (ev_recv_fin sf) tail [x]
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let all_hs_installs_snoc (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires all_hs_installs region /\ is_client_hs_install x == true)
          (ensures all_hs_installs (L.append region [x]))
  = introduce forall (e:CS.conn_event). L.memP e (L.append region [x]) ==> is_client_hs_install e == true
    with introduce _ ==> _
    with _. ( L.append_memP region [x] e )

let has_write_snoc_new (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires is_client_hs_install_dir CS.TrafficWrite x == true)
          (ensures has_write_install (L.append region [x]))
  = L.append_memP region [x] x;
    introduce exists (ew:CS.conn_event). L.memP ew (L.append region [x]) /\ is_client_hs_install_dir CS.TrafficWrite ew
    with x and ()

let has_write_snoc_mono (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires has_write_install region)
          (ensures has_write_install (L.append region [x]))
  = eliminate exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew
    returns has_write_install (L.append region [x])
    with _.
    ( L.append_memP region [x] ew;
      introduce exists (ew2:CS.conn_event). L.memP ew2 (L.append region [x]) /\ is_client_hs_install_dir CS.TrafficWrite ew2
      with ew and () )

let has_read_snoc_new (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires is_client_hs_install_dir CS.TrafficRead x == true)
          (ensures has_read_install (L.append region [x]))
  = L.append_memP region [x] x;
    introduce exists (er:CS.conn_event). L.memP er (L.append region [x]) /\ is_client_hs_install_dir CS.TrafficRead er
    with x and ()

let has_read_snoc_mono (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires has_read_install region)
          (ensures has_read_install (L.append region [x]))
  = eliminate exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er
    returns has_read_install (L.append region [x])
    with _.
    ( L.append_memP region [x] er;
      introduce exists (er2:CS.conn_event). L.memP er2 (L.append region [x]) /\ is_client_hs_install_dir CS.TrafficRead er2
      with er and () )

(* Preserve the conditional region-install invariant when appending a single
   application (non-handshake) event that does not touch handshake keys. *)
let region_installs_ok_key_frame
  (keys keys':CS.key_schedule_state) (region:list CS.conn_event)
  : Lemma
      (requires
        region_installs_ok keys region /\
        keys'.CS.ks_server_handshake_traffic == keys.CS.ks_server_handshake_traffic /\
        keys'.CS.ks_client_handshake_traffic == keys.CS.ks_client_handshake_traffic)
      (ensures region_installs_ok keys' region)
  = ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Per-control single-step preservation helpers                        *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 4 --ifuel 4 --z3rlimit 40 --split_queries always"

let step_from_new (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlNew)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = match conn_ev with
    | CS.ConnLocalEvent (CS.LocalStartHandshake start) ->
      L.append_l_nil [ev_start start];
      assert (s'.CS.cs_event_log == [ ev_start start ]);
      assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsStarted)
    | _ -> ()

let step_from_started (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsStarted)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    match conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsHandshake (M.ClientHello ch) ->
         (match hs.CS.hs_start with
          | Some start ->
            assert (st0.CS.cs_event_log == [ ev_start start ]);
            assert (conn_ev == ev_sent_ch ch);
            cons_append (ev_start start) [] [conn_ev];
            assert (s'.CS.cs_event_log == [ ev_start start; ev_sent_ch ch ]);
            assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent)
          | None -> ())
       | _ -> ())
    | _ -> ()

let step_from_chs (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloSent)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    match conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Received, M.TlsHandshake (M.ServerHello sh) ->
         (match hs.CS.hs_start, hs.CS.hs_client_hello with
          | Some start, Some ch ->
            assert (st0.CS.cs_event_log == [ ev_start start; ev_sent_ch ch ]);
            assert (conn_ev == ev_recv_sh sh);
            cons_append (ev_start start) [ ev_sent_ch ch ] [conn_ev];
            cons_append (ev_sent_ch ch) [] [conn_ev];
            assert (s'.CS.cs_event_log == [ ev_start start; ev_sent_ch ch; ev_recv_sh sh ]);
            assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
            introduce exists (region:list CS.conn_event).
                shr_region_ok s'.CS.cs_model s'.CS.cs_event_log region
            with [] and ()
          | _ -> ())
       | _ -> ())
    | _ -> ()

let step_from_shr (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event). shr_region_ok m0 st0.CS.cs_event_log region);
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) ->
      eliminate exists (region:list CS.conn_event). shr_region_ok m0 st0.CS.cs_event_log region
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( (* legal derive requires ks_shared_secret == None: we are in the None branch *)
        let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        assert (keys.CS.ks_shared_secret == None);
        assert (st0.CS.cs_event_log == [ ev_start start; ev_sent_ch ch; ev_recv_sh sh ]);
        assert (conn_ev == ev_derive shared);
        prefix_unfold start ch sh shared;
        cons_append (ev_start start) [ ev_sent_ch ch; ev_recv_sh sh ] [conn_ev];
        cons_append (ev_sent_ch ch) [ ev_recv_sh sh ] [conn_ev];
        cons_append (ev_recv_sh sh) [] [conn_ev];
        assert (s'.CS.cs_event_log == prefix start ch sh shared);
        L.append_l_nil (prefix start ch sh shared);
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
        introduce exists (region2:list CS.conn_event).
            shr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
        with [] and () )
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys ri) ->
      eliminate exists (region:list CS.conn_event). shr_region_ok m0 st0.CS.cs_event_log region
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( (* legal install at HsServerHelloReceived forces ks_shared_secret == Some and
           epoch == TrafficHandshake: we are in the Some branch *)
        assert (Some? keys.CS.ks_shared_secret);
        assert (ri.CS.install_epoch == CS.TrafficHandshake);
        assert (is_client_hs_install conn_ev == true);
        let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let pfx = prefix start ch sh shared in
        let region' = L.append region [conn_ev] in
        let keys' = s'.CS.cs_model.CS.model_handshake.CS.hs_keys in
        snoc_region pfx region conn_ev;
        all_hs_installs_snoc region conn_ev;
        introduce (Some? keys'.CS.ks_server_handshake_traffic) ==> has_read_install region'
        with _.
          (match ri.CS.install_direction with
           | CS.TrafficRead -> has_read_snoc_new region conn_ev
           | CS.TrafficWrite -> has_read_snoc_mono region conn_ev);
        introduce (Some? keys'.CS.ks_client_handshake_traffic) ==> has_write_install region'
        with _.
          (match ri.CS.install_direction with
           | CS.TrafficWrite -> has_write_snoc_new region conn_ev
           | CS.TrafficRead -> has_write_snoc_mono region conn_ev);
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
        introduce exists (region2:list CS.conn_event).
            shr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
        with region' and () )
    | _ ->
      (match canonical_event conn_ev with
       | CS.ConnNetworkEvent msg ->
         (match msg.CL.message_direction, msg.CL.message_value with
          | CL.Received, M.TlsHandshake (M.EncryptedExtensions ee) ->
            eliminate exists (region:list CS.conn_event). shr_region_ok m0 st0.CS.cs_event_log region
            returns log_shape s'.CS.cs_model s'.CS.cs_event_log
            with _.
            ( (* legal recv EE forces ks_server_handshake_traffic == Some, hence shared derived *)
              assert (Some? keys.CS.ks_server_handshake_traffic);
              assert (Some? keys.CS.ks_shared_secret);
              let start = Some?.v hs.CS.hs_start in
              let ch = Some?.v hs.CS.hs_client_hello in
              let sh = Some?.v hs.CS.hs_server_hello in
              let shared = Some?.v keys.CS.ks_shared_secret in
              let pfx = prefix start ch sh shared in
              assert (has_read_install region);
              assert (all_hs_installs region);
              lemma_hs_install_region_canonical region;
              lemma_prefix_canonical start ch sh shared;
              canonical_log_append pfx region;
              assert (canonical_log st0.CS.cs_event_log == L.append pfx region);
              canonical_log_append st0.CS.cs_event_log [conn_ev];
              lemma_append_nil region;
              introduce exists (raw_suffix:list CS.conn_event).
                  st0.CS.cs_event_log == L.append pfx (L.append region raw_suffix)
              with [] and ();
              raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
              snoc_region pfx region conn_ev;
              introduce exists (raw_suffix:list CS.conn_event).
                  s'.CS.cs_event_log == L.append pfx (L.append region raw_suffix)
              with [conn_ev] and ();
              assert (canonical_event conn_ev == ev_recv_ee ee);
              snoc_region pfx region (canonical_event conn_ev);
              assert (canonical_log s'.CS.cs_event_log ==
                      L.append pfx (L.append region [ev_recv_ee ee]));
              let hs' = s'.CS.cs_model.CS.model_handshake in
              let keys' = hs'.CS.hs_keys in
              assert (hs'.CS.hs_start == Some start);
              assert (hs'.CS.hs_client_hello == Some ch);
              assert (hs'.CS.hs_server_hello == Some sh);
              assert (keys'.CS.ks_shared_secret == Some shared);
              assert (hs'.CS.hs_encrypted_extensions == Some ee);
              assert (hs'.CS.hs_certificate == None);
              assert (hs'.CS.hs_validated_peer == None);
              assert (hs'.CS.hs_certificate_verify == None);
              assert (hs'.CS.hs_certificate_verify_verified == false);
              assert (hs'.CS.hs_server_finished == None);
              assert (Some? keys'.CS.ks_server_handshake_traffic);
              assert (region_installs_ok keys' region);
              assert (s'.CS.cs_model.CS.model_control ==
                      CS.ControlHandshaking CS.HsEncryptedExtensionsReceived);
              introduce exists (region2:list CS.conn_event).
                  eer_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
              with region and () )
          | _ -> ())
       | _ -> ())

#restart-solver
let step_from_eer (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event). eer_region_ok m0 st0.CS.cs_event_log region);
    match canonical_event conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Received, M.TlsHandshake (M.Certificate cert) ->
         eliminate exists (region:list CS.conn_event). eer_region_ok m0 st0.CS.cs_event_log region
         returns log_shape s'.CS.cs_model s'.CS.cs_event_log
         with _.
         ( let start = Some?.v hs.CS.hs_start in
           let ch = Some?.v hs.CS.hs_client_hello in
           let sh = Some?.v hs.CS.hs_server_hello in
           let shared = Some?.v keys.CS.ks_shared_secret in
           let ee = Some?.v hs.CS.hs_encrypted_extensions in
           let pfx = prefix start ch sh shared in
           canonical_log_append st0.CS.cs_event_log [conn_ev];
           raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
           assert (canonical_event conn_ev == ev_recv_cert cert);
           cons_append (ev_recv_ee ee) [] [canonical_event conn_ev];
           snoc_tail pfx region [ ev_recv_ee ee ] (canonical_event conn_ev);
           assert (canonical_log s'.CS.cs_event_log ==
                   L.append pfx
                     (L.append region [ev_recv_ee ee; ev_recv_cert cert]));
           let hs' = s'.CS.cs_model.CS.model_handshake in
           let keys' = hs'.CS.hs_keys in
           assert (hs'.CS.hs_start == Some start);
           assert (hs'.CS.hs_client_hello == Some ch);
           assert (hs'.CS.hs_server_hello == Some sh);
           assert (keys'.CS.ks_shared_secret == Some shared);
           assert (hs'.CS.hs_encrypted_extensions == Some ee);
           assert (hs'.CS.hs_certificate == Some cert);
           assert (hs'.CS.hs_validated_peer == None);
           assert (hs'.CS.hs_certificate_verify == None);
           assert (hs'.CS.hs_certificate_verify_verified == false);
           assert (hs'.CS.hs_server_finished == None);
           assert (Some? keys'.CS.ks_server_handshake_traffic);
           assert (region_installs_ok keys' region);
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived);
           match conn_ev with
           | CS.ConnNetworkEvent _ ->
             introduce exists (region2:list CS.conn_event).
                 cr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
             with region and ()
           | CS.ConnProtectedHandshake _ ->
             introduce exists (region2:list CS.conn_event).
                 cr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
             with region and ()
           | _ -> assert False )
       | _ -> ())
    | _ -> ()

let step_from_cr (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event). cr_region_ok m0 st0.CS.cs_event_log region);
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ->
      eliminate exists (region:list CS.conn_event). cr_region_ok m0 st0.CS.cs_event_log region
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let pfx = prefix start ch sh shared in
        let validate = CS.LocalValidateCertificate peer in
        assert (conn_ev == CS.ConnLocalEvent validate);
        canonical_log_append st0.CS.cs_event_log [conn_ev];
        raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
        cons_append (ev_recv_ee ee) [ ev_recv_cert cert ] [conn_ev];
        cons_append (ev_recv_cert cert) [] [conn_ev];
        snoc_tail pfx region [ ev_recv_ee ee; ev_recv_cert cert ] conn_ev;
        assert (canonical_log s'.CS.cs_event_log ==
                L.append pfx
                  (L.append region [ev_recv_ee ee; ev_recv_cert cert;
                                    CS.ConnLocalEvent validate]));
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated);
        introduce exists (region2:list CS.conn_event) (validate2:CS.local_event).
            cvd_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2
        with region validate and () )
    | _ -> ()

let step_from_cvd (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (validate:CS.local_event).
              cvd_region_ok m0 st0.CS.cs_event_log region validate);
    match canonical_event conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Received, M.TlsHandshake (M.CertificateVerify cv) ->
         eliminate exists (region:list CS.conn_event) (validate:CS.local_event).
             cvd_region_ok m0 st0.CS.cs_event_log region validate
         returns log_shape s'.CS.cs_model s'.CS.cs_event_log
         with _.
         ( let start = Some?.v hs.CS.hs_start in
           let ch = Some?.v hs.CS.hs_client_hello in
           let sh = Some?.v hs.CS.hs_server_hello in
           let shared = Some?.v keys.CS.ks_shared_secret in
           let ee = Some?.v hs.CS.hs_encrypted_extensions in
           let cert = Some?.v hs.CS.hs_certificate in
           let pfx = prefix start ch sh shared in
           canonical_log_append st0.CS.cs_event_log [conn_ev];
           raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
           assert (canonical_event conn_ev == ev_recv_cv cv);
           cons_append (ev_recv_ee ee) [ ev_recv_cert cert; CS.ConnLocalEvent validate ]
             [canonical_event conn_ev];
           cons_append (ev_recv_cert cert) [ CS.ConnLocalEvent validate ]
             [canonical_event conn_ev];
           cons_append (CS.ConnLocalEvent validate) [] [canonical_event conn_ev];
           snoc_tail pfx region
             [ ev_recv_ee ee; ev_recv_cert cert; CS.ConnLocalEvent validate ]
             (canonical_event conn_ev);
           assert (canonical_log s'.CS.cs_event_log ==
                   L.append pfx
                     (L.append region
                       [ev_recv_ee ee; ev_recv_cert cert; CS.ConnLocalEvent validate;
                        ev_recv_cv cv]));
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived);
           match conn_ev with
           | CS.ConnNetworkEvent _ ->
             introduce exists (region2:list CS.conn_event) (validate2:CS.local_event).
                 cvr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2
             with region validate and ()
           | CS.ConnProtectedHandshake _ ->
             introduce exists (region2:list CS.conn_event) (validate2:CS.local_event).
                 cvr_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2
             with region validate and ()
           | _ -> assert False )
       | _ -> ())
    | _ -> ()

let step_from_cvr (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (validate:CS.local_event).
              cvr_region_ok m0 st0.CS.cs_event_log region validate);
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv0) ->
      eliminate exists (region:list CS.conn_event) (validate:CS.local_event).
          cvr_region_ok m0 st0.CS.cs_event_log region validate
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let cv = Some?.v hs.CS.hs_certificate_verify in
        let pfx = prefix start ch sh shared in
        let verifysig = CS.LocalVerifyCertificateSignature cv0 in
        assert (conn_ev == CS.ConnLocalEvent verifysig);
        canonical_log_append st0.CS.cs_event_log [conn_ev];
        raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
        cons_append (ev_recv_ee ee)
          [ ev_recv_cert cert; CS.ConnLocalEvent validate; ev_recv_cv cv ] [conn_ev];
        cons_append (ev_recv_cert cert)
          [ CS.ConnLocalEvent validate; ev_recv_cv cv ] [conn_ev];
        cons_append (CS.ConnLocalEvent validate) [ ev_recv_cv cv ] [conn_ev];
        cons_append (ev_recv_cv cv) [] [conn_ev];
        snoc_tail pfx region
          [ ev_recv_ee ee; ev_recv_cert cert; CS.ConnLocalEvent validate; ev_recv_cv cv ] conn_ev;
        assert (canonical_log s'.CS.cs_event_log ==
                L.append pfx
                  (L.append region
                    [ev_recv_ee ee; ev_recv_cert cert; CS.ConnLocalEvent validate;
                     ev_recv_cv cv; CS.ConnLocalEvent verifysig]));
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified);
        introduce exists (region2:list CS.conn_event) (validate2:CS.local_event) (verifysig2:CS.local_event).
            cvv_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2
        with region validate verifysig and () )
    | _ -> ()

let step_from_cvv (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event).
              cvv_region_ok m0 st0.CS.cs_event_log region validate verifysig);
    match canonical_event conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Received, M.TlsHandshake (M.Finished sf) ->
         eliminate exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event).
             cvv_region_ok m0 st0.CS.cs_event_log region validate verifysig
         returns log_shape s'.CS.cs_model s'.CS.cs_event_log
         with _.
         ( let start = Some?.v hs.CS.hs_start in
           let ch = Some?.v hs.CS.hs_client_hello in
           let sh = Some?.v hs.CS.hs_server_hello in
           let shared = Some?.v keys.CS.ks_shared_secret in
           let ee = Some?.v hs.CS.hs_encrypted_extensions in
           let cert = Some?.v hs.CS.hs_certificate in
           let cv = Some?.v hs.CS.hs_certificate_verify in
           let pfx = prefix start ch sh shared in
           let ps = [ ev_recv_ee ee; ev_recv_cert cert; CS.ConnLocalEvent validate;
                      ev_recv_cv cv; CS.ConnLocalEvent verifysig ] in
           canonical_log_append st0.CS.cs_event_log [conn_ev];
           raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
           assert (canonical_event conn_ev == ev_recv_fin sf);
           (* flight_suffix ... [] == ps ++ [ev_recv_fin sf] *)
           cons_append (ev_recv_ee ee)
             [ ev_recv_cert cert; CS.ConnLocalEvent validate; ev_recv_cv cv; CS.ConnLocalEvent verifysig ]
             [canonical_event conn_ev];
           cons_append (ev_recv_cert cert)
             [ CS.ConnLocalEvent validate; ev_recv_cv cv; CS.ConnLocalEvent verifysig ]
             [canonical_event conn_ev];
           cons_append (CS.ConnLocalEvent validate)
             [ ev_recv_cv cv; CS.ConnLocalEvent verifysig ] [canonical_event conn_ev];
           cons_append (ev_recv_cv cv) [ CS.ConnLocalEvent verifysig ]
             [canonical_event conn_ev];
           cons_append (CS.ConnLocalEvent verifysig) [] [canonical_event conn_ev];
           snoc_tail pfx region ps (canonical_event conn_ev);
           assert (canonical_log s'.CS.cs_event_log ==
                   L.append pfx (L.append region (flight_suffix ee cert validate cv verifysig sf [])));
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
           match conn_ev with
           | CS.ConnNetworkEvent _ ->
             introduce exists (region2:list CS.conn_event) (validate2:CS.local_event)
                 (verifysig2:CS.local_event) (tail2:list CS.conn_event).
                 sfv_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2 tail2
             with region validate verifysig [] and ()
           | CS.ConnProtectedHandshake _ ->
             let hs' = s'.CS.cs_model.CS.model_handshake in
             let keys' = hs'.CS.hs_keys in
             assert (hs'.CS.hs_start == Some start);
             assert (hs'.CS.hs_client_hello == Some ch);
             assert (hs'.CS.hs_server_hello == Some sh);
             assert (keys'.CS.ks_shared_secret == Some shared);
             assert (hs'.CS.hs_encrypted_extensions == Some ee);
             assert (hs'.CS.hs_certificate == Some cert);
             assert (Some? hs'.CS.hs_validated_peer);
             assert (hs'.CS.hs_certificate_verify == Some cv);
             assert (hs'.CS.hs_certificate_verify_verified == true);
             assert (hs'.CS.hs_server_finished == Some sf);
             assert (hs'.CS.hs_server_finished_verified == true);
             assert (Some? keys'.CS.ks_server_handshake_traffic);
             assert (region_installs_ok keys' region);
             introduce exists (region2:list CS.conn_event) (validate2:CS.local_event)
                 (verifysig2:CS.local_event) (tail2:list CS.conn_event).
                 sfv_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2 tail2
             with region validate verifysig [] and ()
           | _ -> assert False )
       | _ -> ())
    | _ -> ()

let step_from_sfv (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
              (tail:list CS.conn_event).
              sfv_region_ok m0 st0.CS.cs_event_log region validate verifysig tail);
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys ri) ->
      (* application-key install: stays at HsServerFinishedVerified, extends tail *)
      eliminate exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
          (tail:list CS.conn_event).
          sfv_region_ok m0 st0.CS.cs_event_log region validate verifysig tail
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let cv = Some?.v hs.CS.hs_certificate_verify in
        let sf = Some?.v hs.CS.hs_server_finished in
        let pfx = prefix start ch sh shared in
        let tail' = L.append tail [canonical_event conn_ev] in
        let keys' = s'.CS.cs_model.CS.model_handshake.CS.hs_keys in
        region_installs_ok_key_frame keys keys' region;
        canonical_log_append st0.CS.cs_event_log [conn_ev];
        raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
        let hs' = s'.CS.cs_model.CS.model_handshake in
        assert (hs'.CS.hs_start == Some start);
        assert (hs'.CS.hs_client_hello == Some ch);
        assert (hs'.CS.hs_server_hello == Some sh);
        assert (keys'.CS.ks_shared_secret == Some shared);
        assert (exists (raw_suffix:list CS.conn_event).
          s'.CS.cs_event_log == L.append pfx (L.append region raw_suffix));
        flight_suffix_snoc ee cert validate cv verifysig sf tail (canonical_event conn_ev);
        snoc_tail pfx region (flight_suffix ee cert validate cv verifysig sf tail)
          (canonical_event conn_ev);
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
        introduce exists (region2:list CS.conn_event) (validate2:CS.local_event)
            (verifysig2:CS.local_event) (tail2:list CS.conn_event).
            sfv_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2 tail2
        with region validate verifysig tail' and () )
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsHandshake (M.Finished cf) ->
         eliminate exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
             (tail:list CS.conn_event).
             sfv_region_ok m0 st0.CS.cs_event_log region validate verifysig tail
         returns log_shape s'.CS.cs_model s'.CS.cs_event_log
         with _.
         ( (* legal Sent Finished forces ks_client_handshake_traffic == Some -> has_write *)
           assert (Some? keys.CS.ks_client_handshake_traffic);
           assert (has_write_install region);
           assert (Some? keys.CS.ks_server_handshake_traffic);
           assert (has_read_install region);
           let start = Some?.v hs.CS.hs_start in
           let ch = Some?.v hs.CS.hs_client_hello in
           let sh = Some?.v hs.CS.hs_server_hello in
           let shared = Some?.v keys.CS.ks_shared_secret in
           let ee = Some?.v hs.CS.hs_encrypted_extensions in
           let cert = Some?.v hs.CS.hs_certificate in
           let cv = Some?.v hs.CS.hs_certificate_verify in
           let sf = Some?.v hs.CS.hs_server_finished in
           let pfx = prefix start ch sh shared in
           let tail' = L.append tail [canonical_event conn_ev] in
           canonical_log_append st0.CS.cs_event_log [conn_ev];
           raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
           let hs' = s'.CS.cs_model.CS.model_handshake in
           let keys' = hs'.CS.hs_keys in
           assert (hs'.CS.hs_start == Some start);
           assert (hs'.CS.hs_client_hello == Some ch);
           assert (hs'.CS.hs_server_hello == Some sh);
           assert (keys'.CS.ks_shared_secret == Some shared);
           assert (exists (raw_suffix:list CS.conn_event).
             s'.CS.cs_event_log == L.append pfx (L.append region raw_suffix));
           flight_suffix_snoc ee cert validate cv verifysig sf tail (canonical_event conn_ev);
           snoc_tail pfx region (flight_suffix ee cert validate cv verifysig sf tail)
             (canonical_event conn_ev);
           assert (s'.CS.cs_model.CS.model_control == CS.ControlApplicationData);
           introduce exists (region2:list CS.conn_event) (validate2:CS.local_event)
               (verifysig2:CS.local_event) (tail2:list CS.conn_event).
               appdata_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2 tail2
           with region validate verifysig tail' and () )
       | _ -> ())
    | _ -> ()

#restart-solver
let step_from_appdata (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
              (tail:list CS.conn_event).
              appdata_region_ok m0 st0.CS.cs_event_log region validate verifysig tail);
    let handle () : Lemma
      (requires
        (exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
           (tail:list CS.conn_event).
           appdata_region_ok m0 st0.CS.cs_event_log region validate verifysig tail) /\
        s'.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_start == hs.CS.hs_start /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_client_hello == hs.CS.hs_client_hello /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_server_hello == hs.CS.hs_server_hello /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == hs.CS.hs_encrypted_extensions /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_certificate == hs.CS.hs_certificate /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_validated_peer == hs.CS.hs_validated_peer /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == hs.CS.hs_certificate_verify /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify_verified == hs.CS.hs_certificate_verify_verified /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_server_finished == hs.CS.hs_server_finished /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == keys.CS.ks_shared_secret /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == keys.CS.ks_server_handshake_traffic /\
        s'.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == keys.CS.ks_client_handshake_traffic /\
        s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev])
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
      =
      eliminate exists (region:list CS.conn_event) (validate:CS.local_event) (verifysig:CS.local_event)
          (tail:list CS.conn_event).
          appdata_region_ok m0 st0.CS.cs_event_log region validate verifysig tail
      returns log_shape s'.CS.cs_model s'.CS.cs_event_log
      with _.
      ( let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let cv = Some?.v hs.CS.hs_certificate_verify in
        let sf = Some?.v hs.CS.hs_server_finished in
        let pfx = prefix start ch sh shared in
        let tail' = L.append tail [canonical_event conn_ev] in
        canonical_log_append st0.CS.cs_event_log [conn_ev];
        raw_suffix_snoc pfx region st0.CS.cs_event_log s'.CS.cs_event_log conn_ev;
        let hs' = s'.CS.cs_model.CS.model_handshake in
        let keys' = hs'.CS.hs_keys in
        assert (hs'.CS.hs_start == Some start);
        assert (hs'.CS.hs_client_hello == Some ch);
        assert (hs'.CS.hs_server_hello == Some sh);
        assert (keys'.CS.ks_shared_secret == Some shared);
        assert (exists (raw_suffix:list CS.conn_event).
          s'.CS.cs_event_log == L.append pfx (L.append region raw_suffix));
        flight_suffix_snoc ee cert validate cv verifysig sf tail (canonical_event conn_ev);
        snoc_tail pfx region (flight_suffix ee cert validate cv verifysig sf tail)
          (canonical_event conn_ev);
        introduce exists (region2:list CS.conn_event) (validate2:CS.local_event)
            (verifysig2:CS.local_event) (tail2:list CS.conn_event).
            appdata_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 validate2 verifysig2 tail2
        with region validate verifysig tail' and () )
    in
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalDeliverApplicationData _) -> handle ()
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsApplicationData _ -> handle ()
       | M.TlsIgnoredPostHandshake _ -> handle ()
       | M.TlsKeyUpdate _ -> handle ()
       | _ -> ())
    | _ -> ()

#pop-options

#push-options "--fuel 4 --ifuel 4 --z3rlimit 40 --split_queries always"
let lemma_step_preserves_shape (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma (requires step_pre st0 s' conn_ev)
          (ensures client_canonical_shape s')
  = match st0.CS.cs_model.CS.model_control with
    | CS.ControlNew -> step_from_new st0 s' conn_ev
    | CS.ControlHandshaking CS.HsStarted -> step_from_started st0 s' conn_ev
    | CS.ControlHandshaking CS.HsClientHelloSent -> step_from_chs st0 s' conn_ev
    | CS.ControlHandshaking CS.HsServerHelloReceived -> step_from_shr st0 s' conn_ev
    | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived -> step_from_eer st0 s' conn_ev
    | CS.ControlHandshaking CS.HsCertificateReceived -> step_from_cr st0 s' conn_ev
    | CS.ControlHandshaking CS.HsCertificateValidated -> step_from_cvd st0 s' conn_ev
    | CS.ControlHandshaking CS.HsCertificateVerifyReceived -> step_from_cvr st0 s' conn_ev
    | CS.ControlHandshaking CS.HsCertificateVerifyVerified -> step_from_cvv st0 s' conn_ev
    | CS.ControlHandshaking CS.HsServerFinishedVerified -> step_from_sfv st0 s' conn_ev
    | CS.ControlApplicationData -> step_from_appdata st0 s' conn_ev
    | CS.ControlHandshaking CS.HsNotStarted -> ()
    | CS.ControlHandshaking CS.HsAwaitingClientHello -> ()
    | CS.ControlHandshaking CS.HsClientHelloReceived -> ()
    | CS.ControlHandshaking CS.HsServerHelloSent -> ()
    | CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> ()
    | CS.ControlHandshaking CS.HsServerFinishedSent -> ()
    | CS.ControlHandshaking CS.HsServerFinishedReceived -> ()
    | CS.ControlHandshaking CS.HsClientFinishedReceived -> ()
    | CS.ControlHandshaking CS.HsClientFinishedSent -> ()
    | CS.ControlHandshaking CS.HsClientFinishedVerified -> ()
    | CS.ControlClosing -> ()
    | CS.ControlClosed -> ()
    | CS.ControlFailed _ -> ()
#pop-options

(* ================================================================== *)
(* Config preservation for one client step (role-agnostic)             *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_client_step_config
  (st0 s':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires EC.client_step st0 ev s' out)
      (ensures
        s'.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  = lemma_client_step_facts st0 s' ev out;
    eliminate exists (conn_ev:CS.conn_event).
      (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
       CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
       CS.legal_event st0.CS.cs_model conn_ev /\
       is_client_canonical_event conn_ev)
    returns (s'.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
    with _.
      CLem.lemma_step_model_preserves_config st0.CS.cs_model conn_ev s'.CS.cs_model
#pop-options

(* ================================================================== *)
(* Trace induction                                                     *)
(* ================================================================== *)

(* Lemma A: the log only grows along a trace. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_trace_log_extends
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires SM.trace_reaches (WStep.client_sm init) st0 trace st1)
      (ensures
        (exists (ext:list CS.conn_event).
          st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext))
      (decreases trace)
  = match trace with
    | [] ->
        L.append_l_nil st0.CS.cs_event_log;
        introduce exists (ext:list CS.conn_event).
          st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext
        with [] and ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_client_step_facts st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_log_extends init s' st1 rest;
        eliminate exists (conn_ev:CS.conn_event).
          (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
           CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
           CS.legal_event st0.CS.cs_model conn_ev /\
           is_client_canonical_event conn_ev)
        returns
          (exists (ext:list CS.conn_event).
            st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext)
        with _.
          eliminate exists (ext':list CS.conn_event).
            st1.CS.cs_event_log == L.append s'.CS.cs_event_log ext'
          returns
            (exists (ext:list CS.conn_event).
              st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext)
          with _.
          ( L.append_assoc st0.CS.cs_event_log [conn_ev] ext';
            introduce exists (ext:list CS.conn_event).
              st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext
            with (L.append [conn_ev] ext') and () )
#pop-options

(* Lemma C: model_config is preserved along a trace. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_trace_config
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires SM.trace_reaches (WStep.client_sm init) st0 trace st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_client_step_config st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_config init s' st1 rest
#pop-options

(* Lemma B: shape is preserved along a CCS-free trace. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_trace_shape
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.client_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
        client_canonical_shape st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        log_has_no_received_ccs st1.CS.cs_event_log)
      (ensures client_canonical_shape st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_client_step_facts st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_client_step_config st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_log_extends init s' st1 rest;
        eliminate exists (conn_ev:CS.conn_event).
          (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
           CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
           CS.legal_event st0.CS.cs_model conn_ev /\
           is_client_canonical_event conn_ev)
        returns client_canonical_shape st1
        with _.
          eliminate exists (ext':list CS.conn_event).
            st1.CS.cs_event_log == L.append s'.CS.cs_event_log ext'
          returns client_canonical_shape st1
          with _.
          (
            L.append_memP st0.CS.cs_event_log [conn_ev] conn_ev;
            L.append_memP s'.CS.cs_event_log ext' conn_ev;
            assert (is_received_ccs conn_ev == false);
            lemma_step_preserves_shape st0 s' conn_ev;
            lemma_trace_shape init s' st1 rest
          )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_client_canonical_appdata_exact_spine
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.client_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures
       (exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
          (client_shared:C.x25519_shared_secret)
          (region:list CS.conn_event)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_validate:CS.local_event)
          (cv:GCV.certificateVerify)
          (cv_verify:CS.local_event)
          (sf:GFin.finished)
          (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew) /\
          (exists (raw_suffix:list CS.conn_event).
             s.CS.cs_event_log ==
               L.append
                 (PWSeg.client_cleartext_handshake_prefix_events
                   start ch sh client_shared)
                 (L.append region raw_suffix)) /\
          canonical_log s.CS.cs_event_log ==
            L.append
              (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_validate ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnLocalEvent cv_verify ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail))))
  = let init = CS.initial cfg in
    lemma_shape_initial cfg;
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                                 CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches (WStep.client_sm init) init trace s
    returns
       (exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
          (client_shared:C.x25519_shared_secret)
          (region:list CS.conn_event)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_validate:CS.local_event)
          (cv:GCV.certificateVerify)
          (cv_verify:CS.local_event)
          (sf:GFin.finished)
          (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew) /\
          (exists (raw_suffix:list CS.conn_event).
             s.CS.cs_event_log ==
               L.append
                 (PWSeg.client_cleartext_handshake_prefix_events
                   start ch sh client_shared)
                 (L.append region raw_suffix)) /\
          canonical_log s.CS.cs_event_log ==
            L.append
              (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_validate ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnLocalEvent cv_verify ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail)))
    with _.
    (
      lemma_trace_config init init s trace;
      lemma_trace_shape init init s trace;
      assert (client_canonical_shape s);
      eliminate exists (region:list CS.conn_event) (validate:CS.local_event)
          (verifysig:CS.local_event) (tail:list CS.conn_event).
          appdata_region_ok s.CS.cs_model s.CS.cs_event_log region validate verifysig tail
      returns
         (exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
            (client_shared:C.x25519_shared_secret)
            (region:list CS.conn_event)
            (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
            (cv_validate:CS.local_event)
            (cv:GCV.certificateVerify)
            (cv_verify:CS.local_event)
            (sf:GFin.finished)
            (tail:list CS.conn_event).
            (forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true) /\
            (exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er) /\
            (exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew) /\
            (exists (raw_suffix:list CS.conn_event).
               s.CS.cs_event_log ==
                 L.append
                   (PWSeg.client_cleartext_handshake_prefix_events
                     start ch sh client_shared)
                   (L.append region raw_suffix)) /\
            canonical_log s.CS.cs_event_log ==
              L.append
                (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
                (L.append region
                   (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                    CS.ConnLocalEvent cv_validate ::
                    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                    CS.ConnLocalEvent cv_verify ::
                    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                    tail)))
      with _.
      (
        let hs = s.CS.cs_model.CS.model_handshake in
        let keys = hs.CS.hs_keys in
        let start = Some?.v hs.CS.hs_start in
        let ch = Some?.v hs.CS.hs_client_hello in
        let sh = Some?.v hs.CS.hs_server_hello in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let cv = Some?.v hs.CS.hs_certificate_verify in
        let sf = Some?.v hs.CS.hs_server_finished in
        introduce exists (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
            (client_shared:C.x25519_shared_secret)
            (region:list CS.conn_event)
            (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
            (cv_validate:CS.local_event)
            (cv:GCV.certificateVerify)
            (cv_verify:CS.local_event)
            (sf:GFin.finished)
            (tail:list CS.conn_event).
            (forall (e:CS.conn_event). L.memP e region ==> is_client_hs_install e == true) /\
            (exists (er:CS.conn_event). L.memP er region /\ is_client_hs_install_dir CS.TrafficRead er) /\
            (exists (ew:CS.conn_event). L.memP ew region /\ is_client_hs_install_dir CS.TrafficWrite ew) /\
            (exists (raw_suffix:list CS.conn_event).
               s.CS.cs_event_log ==
                 L.append
                   (PWSeg.client_cleartext_handshake_prefix_events
                     start ch sh client_shared)
                   (L.append region raw_suffix)) /\
            canonical_log s.CS.cs_event_log ==
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
        with start ch sh shared region ee cert validate cv verifysig sf tail
        and ()
      )
    )
#pop-options

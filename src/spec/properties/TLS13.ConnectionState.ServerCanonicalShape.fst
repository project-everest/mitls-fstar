module TLS13.ConnectionState.ServerCanonicalShape

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module C = TLS13.Crypto.Spec
module T = TLS13.Types
module ES = TLS13.Spec.Endpoint.Server
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

let ev_start : CS.conn_event = CS.ConnLocalEvent CS.LocalStartServer

let ev_recv_ch (ch:GCH.clientHello) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.ClientHello ch);
  })

let ev_select (sel:CS.server_handshake_selection) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalSelectServerParameters sel)

let ev_derive (shared:C.x25519_shared_secret) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)

let ev_sent_sh (sh:GSH.serverHello) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.ServerHello sh);
  })

let ev_ee (ee:GEE.encryptedExtensions) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
  })

let ev_cert (cert:GCert.certificate) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  })

let ev_cv_local (cv:GCV.certificateVerify) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv)

let ev_cv (cv:GCV.certificateVerify) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  })

let ev_fin (sf:GFin.finished) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  })

(* The fixed cleartext prefix, as a pure list (matches PWSeg's definition). *)
let prefix (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
           (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  : list CS.conn_event =
  PWSeg.server_cleartext_handshake_prefix_events ch sel shared sh

let prefix_unfold (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
                  (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  : Lemma (prefix ch sel shared sh ==
           [ ev_start; ev_recv_ch ch; ev_select sel; ev_derive shared; ev_sent_sh sh ])
  = ()

(* The fixed encrypted-flight suffix, in cons form matching the goal. *)
let suffix (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
           (cv:GCV.certificateVerify) (sf:GFin.finished)
           (tail:list CS.conn_event)
  : list CS.conn_event =
  ev_ee ee :: ev_cert cert :: ev_cv_local cv :: ev_cv cv :: ev_fin sf :: tail

(* ================================================================== *)
(* Region predicates                                                   *)
(* ================================================================== *)

let all_hs_installs (region:list CS.conn_event) : prop =
  forall (e:CS.conn_event). L.memP e region ==> is_server_hs_install e == true

let has_write_install (region:list CS.conn_event) : prop =
  exists (ew:CS.conn_event). L.memP ew region /\ is_server_hs_install_dir CS.TrafficWrite ew

let has_read_install (region:list CS.conn_event) : prop =
  exists (er:CS.conn_event). L.memP er region /\ is_server_hs_install_dir CS.TrafficRead er

(* ================================================================== *)
(* The exact canonical log shape, as a function of the model           *)
(* ================================================================== *)

(* All witnesses (ch, sel, shared, sh, ee, cert, cv, sf) are recoverable
   directly from the model fields (mirroring ServerLogShape.expected_milestones);
   only [region] (the unbounded run of server handshake key installs) and
   [tail] (post-flight events) are genuinely existential.  The region is
   factored into named [*_region_ok] predicates so that single-step
   preservation can eliminate/re-introduce it as one clean predicate. *)

(* HsServerHelloSent: log == prefix ++ region, region a run of hs installs. *)
let shs_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_server_selection, keys.CS.ks_shared_secret, hs.CS.hs_server_hello with
  | Some sel, Some shared, Some sh ->
    hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
    hs.CS.hs_certificate_verify == None /\ hs.CS.hs_certificate_verify_verified == false /\
    hs.CS.hs_server_finished == None /\
    log == L.append (prefix sel.CS.server_selected_client_hello sel shared sh) region /\
    all_hs_installs region /\
    (Some? keys.CS.ks_server_handshake_traffic ==> has_write_install region) /\
    (Some? keys.CS.ks_client_handshake_traffic ==> has_read_install region)
  | _ -> False

(* HsServerEncryptedFlightSent: four substages of the encrypted flight. *)
let sefs_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                   (region:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_server_selection, keys.CS.ks_shared_secret,
        hs.CS.hs_server_hello, hs.CS.hs_encrypted_extensions with
  | Some sel, Some shared, Some sh, Some ee ->
    all_hs_installs region /\ has_write_install region /\
    (Some? keys.CS.ks_client_handshake_traffic ==> has_read_install region) /\
    (let pfx = prefix sel.CS.server_selected_client_hello sel shared sh in
     (match hs.CS.hs_certificate, hs.CS.hs_certificate_verify,
            hs.CS.hs_certificate_verify_verified with
      | None, None, false ->
        log == L.append pfx (L.append region [ ev_ee ee ])
      | Some cert, None, false ->
        log == L.append pfx (L.append region [ ev_ee ee; ev_cert cert ])
      | Some cert, Some cv, false ->
        hs.CS.hs_certificate_verify == Some cv /\
        log == L.append pfx (L.append region [ ev_ee ee; ev_cert cert; ev_cv_local cv ])
      | Some cert, Some cv, true ->
        hs.CS.hs_certificate_verify == Some cv /\
        log == L.append pfx (L.append region [ ev_ee ee; ev_cert cert; ev_cv_local cv; ev_cv cv ])
      | _ -> False))
  | _ -> False

(* HsServerFinishedSent: full flight, tail after the server Finished, region frozen. *)
let sfs_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                  (region:list CS.conn_event) (tail:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_server_selection, keys.CS.ks_shared_secret, hs.CS.hs_server_hello,
        hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate, hs.CS.hs_certificate_verify,
        hs.CS.hs_server_finished with
  | Some sel, Some shared, Some sh, Some ee, Some cert, Some cv, Some sf ->
    hs.CS.hs_certificate_verify_verified == true /\
    all_hs_installs region /\ has_write_install region /\
    (Some? keys.CS.ks_client_handshake_traffic ==> has_read_install region) /\
    log == L.append (prefix sel.CS.server_selected_client_hello sel shared sh)
                    (L.append region (suffix ee cert cv sf tail))
  | _ -> False

(* ControlApplicationData: full flight, both installs present. *)
let appdata_region_ok (m:CS.connection_model) (log:list CS.conn_event)
                      (region:list CS.conn_event) (tail:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match hs.CS.hs_server_selection, keys.CS.ks_shared_secret, hs.CS.hs_server_hello,
        hs.CS.hs_encrypted_extensions, hs.CS.hs_certificate, hs.CS.hs_certificate_verify,
        hs.CS.hs_server_finished with
  | Some sel, Some shared, Some sh, Some ee, Some cert, Some cv, Some sf ->
    hs.CS.hs_certificate_verify_verified == true /\
    all_hs_installs region /\ has_write_install region /\ has_read_install region /\
    log == L.append (prefix sel.CS.server_selected_client_hello sel shared sh)
                    (L.append region (suffix ee cert cv sf tail))
  | _ -> False

let log_shape (m:CS.connection_model) (log:list CS.conn_event) : prop =
  let hs = m.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  match m.CS.model_control with
  | CS.ControlNew ->
    log == [] /\
    hs.CS.hs_server_selection == None /\ keys.CS.ks_shared_secret == None /\
    hs.CS.hs_server_hello == None /\ keys.CS.ks_server_handshake_traffic == None /\
    keys.CS.ks_client_handshake_traffic == None /\ hs.CS.hs_encrypted_extensions == None /\
    hs.CS.hs_certificate == None /\ hs.CS.hs_certificate_verify == None /\
    hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None /\
    hs.CS.hs_client_hello == None
  | CS.ControlHandshaking CS.HsAwaitingClientHello ->
    log == [ ev_start ] /\
    hs.CS.hs_server_selection == None /\ keys.CS.ks_shared_secret == None /\
    hs.CS.hs_server_hello == None /\ keys.CS.ks_server_handshake_traffic == None /\
    keys.CS.ks_client_handshake_traffic == None /\ hs.CS.hs_encrypted_extensions == None /\
    hs.CS.hs_certificate == None /\ hs.CS.hs_certificate_verify == None /\
    hs.CS.hs_certificate_verify_verified == false /\ hs.CS.hs_server_finished == None /\
    hs.CS.hs_client_hello == None
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    (hs.CS.hs_server_hello == None /\ keys.CS.ks_server_handshake_traffic == None /\
     keys.CS.ks_client_handshake_traffic == None /\
     hs.CS.hs_encrypted_extensions == None /\ hs.CS.hs_certificate == None /\
     hs.CS.hs_certificate_verify == None /\ hs.CS.hs_certificate_verify_verified == false /\
     hs.CS.hs_server_finished == None) /\
    (match hs.CS.hs_server_selection with
     | None ->
       (match hs.CS.hs_client_hello with
        | Some ch -> log == [ ev_start; ev_recv_ch ch ]
        | None -> False)
     | Some sel ->
       (match keys.CS.ks_shared_secret with
        | None ->
          log == [ ev_start; ev_recv_ch sel.CS.server_selected_client_hello; ev_select sel ]
        | Some shared ->
          log == [ ev_start; ev_recv_ch sel.CS.server_selected_client_hello;
                   ev_select sel; ev_derive shared ]))
  | CS.ControlHandshaking CS.HsServerHelloSent ->
    (exists (region:list CS.conn_event). shs_region_ok m log region)
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent ->
    (exists (region:list CS.conn_event). sefs_region_ok m log region)
  | CS.ControlHandshaking CS.HsServerFinishedSent ->
    (exists (region:list CS.conn_event) (tail:list CS.conn_event). sfs_region_ok m log region tail)
  | CS.ControlHandshaking CS.HsClientFinishedReceived ->
    (* unreachable: no transition produces this control for a server *)
    False
  | CS.ControlApplicationData ->
    (exists (region:list CS.conn_event) (tail:list CS.conn_event). appdata_region_ok m log region tail)
  | _ -> True

(* ================================================================== *)
(* The exact canonical shape invariant                                 *)
(* ================================================================== *)

#restart-solver
let server_canonical_shape (st:CS.connection_state) : prop =
  st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
  log_shape st.CS.cs_model st.CS.cs_event_log

(* ================================================================== *)
(* Initial state                                                       *)
(* ================================================================== *)

let lemma_shape_initial (cfg:CS.connection_config)
  : Lemma (server_canonical_shape (CS.initial cfg))
  = ()

(* ================================================================== *)
(* Canonical event classification + extraction from server_step        *)
(* ================================================================== *)

let is_server_canonical_event (ev:CS.conn_event) : prop =
  match ev with
  | CS.ConnNetworkEvent msg ->
    (msg.CL.message_direction == CL.Received) \/
    (msg.CL.message_direction == CL.Sent /\
       (match msg.CL.message_value with
        | M.TlsHandshake (M.ServerHello _) -> True
        | M.TlsHandshake (M.EncryptedExtensions _) -> True
        | M.TlsHandshake (M.Certificate _) -> True
        | M.TlsHandshake (M.CertificateVerify _) -> True
        | M.TlsHandshake (M.Finished _) -> True
        | M.TlsApplicationData _ -> True
        | M.TlsKeyUpdate _ -> True
        | M.TlsAlert T.Close_notify -> True
        | _ -> False))
  | CS.ConnProtectedHandshake _ -> False
  (* Cleartext reassembly steps are not yet emitted by [server_step]; see the
     staging note on [ConnCleartextHandshake] in TLS13.Spec.StateMachine. *)
  | CS.ConnCleartextHandshake _ -> False
  | CS.ConnLocalEvent le ->
    (match le with
     | CS.LocalStartServer -> True
     | CS.LocalSelectServerParameters _ -> True
     | CS.LocalDeriveSharedSecret _ -> True
     | CS.LocalInstallTrafficKeysForRole ri -> ri.CS.install_role == CS.ServerEndpoint
     | CS.LocalSignCertificateVerify _ -> True
     | CS.LocalVerifyClientFinished _ -> True
     | CS.LocalDeliverApplicationData _ -> True
     | CS.LocalFail _ -> True
     | _ -> False)

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_semantic_canonical (sem:ES.local_event) (conn_ev:CS.conn_event)
  : Lemma (requires ES.server_local_event_matches sem conn_ev)
          (ensures is_server_canonical_event conn_ev)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_step_facts
  (st0 s':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        ES.server_step_nonbuffering st0 ev s' out)
      (ensures
        (exists (conn_ev:CS.conn_event).
          s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
          CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
          CS.legal_event st0.CS.cs_model conn_ev /\
          is_server_canonical_event conn_ev))
  = match ev with
    | SM.WireEvent wire ->
      (* [server_step] admits a cleartext BUFFERING step, which is not a
         canonical shape event; the non-buffering post-state emptiness rules it
         out and recovers the received-message reading. *)
      ES.lemma_server_wire_step_received_msg #CTy.server_local_event st0 wire s' out;
      eliminate exists (msg:M.tls_message).
        (let conn_ev =
           CS.ConnNetworkEvent {
             CL.message_direction = CL.Received;
             CL.message_value = msg;
           } in
         SMCan.canonical_wire_step st0 s' conn_ev
           (Common.WireFormat.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      with
      (
        let conn_ev =
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = msg;
          } in
        assert (is_server_canonical_event conn_ev)
      )
    | SM.LocalEvent local ->
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (ES.server_representation_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty)
      with
      (
        CTy.lemma_server_local_event_semantic_exact local conn_ev;
        lemma_semantic_canonical (CTy.server_local_event_semantic local) conn_ev
      )
#pop-options

(* ================================================================== *)
(* Single-step preservation                                            *)
(* ================================================================== *)

let step_pre (st0 s':CS.connection_state) (conn_ev:CS.conn_event) : prop =
  server_canonical_shape st0 /\
  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
  CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
  CS.legal_event st0.CS.cs_model conn_ev /\
  is_server_canonical_event conn_ev /\
  is_received_ccs conn_ev == false

(* Precondition of the per-control helpers (step_pre with [log_shape st0]
   already exposed instead of the [server_canonical_shape] wrapper). *)
unfold
let hpre (st0 s':CS.connection_state) (conn_ev:CS.conn_event) : prop =
  log_shape st0.CS.cs_model st0.CS.cs_event_log /\
  st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
  s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
  CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
  CS.legal_event st0.CS.cs_model conn_ev /\
  is_server_canonical_event conn_ev /\
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

let cons_append (h:CS.conn_event) (l m:list CS.conn_event)
  : Lemma (L.append (h :: l) m == h :: (L.append l m))
  = ()

let suffix_snoc (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
                (cv:GCV.certificateVerify) (sf:GFin.finished)
                (tail:list CS.conn_event) (x:CS.conn_event)
  : Lemma (L.append (suffix ee cert cv sf tail) [x] ==
           suffix ee cert cv sf (L.append tail [x]))
  = cons_append (ev_ee ee) (ev_cert cert :: ev_cv_local cv :: ev_cv cv :: ev_fin sf :: tail) [x];
    cons_append (ev_cert cert) (ev_cv_local cv :: ev_cv cv :: ev_fin sf :: tail) [x];
    cons_append (ev_cv_local cv) (ev_cv cv :: ev_fin sf :: tail) [x];
    cons_append (ev_cv cv) (ev_fin sf :: tail) [x];
    cons_append (ev_fin sf) tail [x]
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let all_hs_installs_snoc (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires all_hs_installs region /\ is_server_hs_install x == true)
          (ensures all_hs_installs (L.append region [x]))
  = introduce forall (e:CS.conn_event). L.memP e (L.append region [x]) ==> is_server_hs_install e == true
    with introduce _ ==> _
    with ( L.append_memP region [x] e )

let has_write_snoc_new (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires is_server_hs_install_dir CS.TrafficWrite x == true)
          (ensures has_write_install (L.append region [x]))
  = L.append_memP region [x] x;
    introduce exists (ew:CS.conn_event). L.memP ew (L.append region [x]) /\ is_server_hs_install_dir CS.TrafficWrite ew
    with x and ()

let has_write_snoc_mono (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires has_write_install region)
          (ensures has_write_install (L.append region [x]))
  = eliminate exists (ew:CS.conn_event). L.memP ew region /\ is_server_hs_install_dir CS.TrafficWrite ew
    with
    ( L.append_memP region [x] ew;
      introduce exists (ew2:CS.conn_event). L.memP ew2 (L.append region [x]) /\ is_server_hs_install_dir CS.TrafficWrite ew2
      with ew and () )

let has_read_snoc_new (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires is_server_hs_install_dir CS.TrafficRead x == true)
          (ensures has_read_install (L.append region [x]))
  = L.append_memP region [x] x;
    introduce exists (er:CS.conn_event). L.memP er (L.append region [x]) /\ is_server_hs_install_dir CS.TrafficRead er
    with x and ()

let has_read_snoc_mono (region:list CS.conn_event) (x:CS.conn_event)
  : Lemma (requires has_read_install region)
          (ensures has_read_install (L.append region [x]))
  = eliminate exists (er:CS.conn_event). L.memP er region /\ is_server_hs_install_dir CS.TrafficRead er
    with
    ( L.append_memP region [x] er;
      introduce exists (er2:CS.conn_event). L.memP er2 (L.append region [x]) /\ is_server_hs_install_dir CS.TrafficRead er2
      with er and () )
#pop-options

(* ------------------------------------------------------------------ *)
(* Per-control single-step preservation helpers                        *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 4 --ifuel 4 --z3rlimit 40"
#push-options "--fuel 4 --ifuel 4 --z3rlimit 40"
#restart-solver
let lemma_chr_log
  (m:CS.connection_model) (log:list CS.conn_event)
  (sel:CS.server_handshake_selection) (shared:C.x25519_shared_secret)
  : Lemma
      (requires
        log_shape m log /\
        m.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived /\
        m.CS.model_handshake.CS.hs_server_selection == Some sel /\
        m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some shared)
      (ensures
        log == [ ev_start; ev_recv_ch sel.CS.server_selected_client_hello;
                 ev_select sel; ev_derive shared ])
  = ()
#pop-options

let step_from_new (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlNew)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = match conn_ev with
    | _ -> ()

let step_from_awaiting (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsAwaitingClientHello)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = match conn_ev with
    | _ -> ()

let step_from_chr (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    match conn_ev with
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsHandshake (M.ServerHello sh) ->
         (match hs.CS.hs_server_selection, keys.CS.ks_shared_secret with
          | Some sel, Some shared ->
            let ch = sel.CS.server_selected_client_hello in
            lemma_chr_log m0 st0.CS.cs_event_log sel shared;
            assert (st0.CS.cs_event_log ==
                    [ ev_start; ev_recv_ch ch; ev_select sel; ev_derive shared ]);
            prefix_unfold ch sel shared sh;
            assert (conn_ev == ev_sent_sh sh);
            cons_append ev_start [ ev_recv_ch ch; ev_select sel; ev_derive shared ] [conn_ev];
            cons_append (ev_recv_ch ch) [ ev_select sel; ev_derive shared ] [conn_ev];
            cons_append (ev_select sel) [ ev_derive shared ] [conn_ev];
            cons_append (ev_derive shared) [] [conn_ev];
            assert (s'.CS.cs_event_log == prefix ch sel shared sh);
            L.append_l_nil (prefix ch sel shared sh);
            assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
            introduce exists (region:list CS.conn_event).
                shs_region_ok s'.CS.cs_model s'.CS.cs_event_log region
            with [] and ()
          | _ -> ())
       | _ -> ())
    | _ -> ()

let step_from_shs (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event). shs_region_ok m0 st0.CS.cs_event_log region);
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole ri) ->
      eliminate exists (region:list CS.conn_event). shs_region_ok m0 st0.CS.cs_event_log region
      with
      ( let sel = Some?.v hs.CS.hs_server_selection in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let sh = Some?.v hs.CS.hs_server_hello in
        let ch = sel.CS.server_selected_client_hello in
        let pfx = prefix ch sel shared sh in
        let region' = L.append region [conn_ev] in
        let keys' = s'.CS.cs_model.CS.model_handshake.CS.hs_keys in
        assert (is_server_hs_install conn_ev == true);
        snoc_region pfx region conn_ev;
        all_hs_installs_snoc region conn_ev;
        introduce (Some? keys'.CS.ks_server_handshake_traffic) ==> has_write_install region'
        with
          (match ri.CS.install_payload.CS.install_direction with
           | CS.TrafficWrite -> has_write_snoc_new region conn_ev
           | CS.TrafficRead -> has_write_snoc_mono region conn_ev);
        introduce (Some? keys'.CS.ks_client_handshake_traffic) ==> has_read_install region'
        with
          (match ri.CS.install_payload.CS.install_direction with
           | CS.TrafficRead -> has_read_snoc_new region conn_ev
           | CS.TrafficWrite -> has_read_snoc_mono region conn_ev);
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
        introduce exists (region2:list CS.conn_event).
            shs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
        with region' and () )
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsHandshake (M.EncryptedExtensions ee) ->
         eliminate exists (region:list CS.conn_event). shs_region_ok m0 st0.CS.cs_event_log region
         with
         ( let sel = Some?.v hs.CS.hs_server_selection in
           let shared = Some?.v keys.CS.ks_shared_secret in
           let sh = Some?.v hs.CS.hs_server_hello in
           let ch = sel.CS.server_selected_client_hello in
           let pfx = prefix ch sel shared sh in
           assert (Some? keys.CS.ks_server_handshake_traffic);
           assert (has_write_install region);
           snoc_region pfx region conn_ev;
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           introduce exists (region2:list CS.conn_event).
               sefs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
           with region and () )
       | _ -> ())
    | _ -> ()

let step_from_sefs (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event). sefs_region_ok m0 st0.CS.cs_event_log region);
    let sel = Some?.v hs.CS.hs_server_selection in
    let shared = Some?.v keys.CS.ks_shared_secret in
    let sh = Some?.v hs.CS.hs_server_hello in
    let ee = Some?.v hs.CS.hs_encrypted_extensions in
    let ch = sel.CS.server_selected_client_hello in
    let pfx = prefix ch sel shared sh in
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) ->
      eliminate exists (region:list CS.conn_event). sefs_region_ok m0 st0.CS.cs_event_log region
      with
      ( let cert = Some?.v hs.CS.hs_certificate in
        assert (conn_ev == ev_cv_local cv);
        cons_append (ev_ee ee) [ ev_cert cert ] [conn_ev];
        cons_append (ev_cert cert) [] [conn_ev];
        snoc_tail pfx region [ ev_ee ee; ev_cert cert ] conn_ev;
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
        introduce exists (region2:list CS.conn_event).
            sefs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
        with region and () )
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Sent, M.TlsHandshake (M.Certificate cert) ->
         eliminate exists (region:list CS.conn_event). sefs_region_ok m0 st0.CS.cs_event_log region
         with
         ( assert (conn_ev == ev_cert cert);
           assert (hs.CS.hs_certificate == None);
           assert (st0.CS.cs_event_log == L.append pfx (L.append region [ ev_ee ee ]));
           cons_append (ev_ee ee) [] [conn_ev];
           snoc_tail pfx region [ ev_ee ee ] conn_ev;
           assert (s'.CS.cs_event_log == L.append pfx (L.append region [ ev_ee ee; ev_cert cert ]));
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           introduce exists (region2:list CS.conn_event).
               sefs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
           with region and () )
       | CL.Sent, M.TlsHandshake (M.CertificateVerify cv) ->
         eliminate exists (region:list CS.conn_event). sefs_region_ok m0 st0.CS.cs_event_log region
         with
         ( let cert = Some?.v hs.CS.hs_certificate in
           let cv0 = Some?.v hs.CS.hs_certificate_verify in
           assert (cv0 == cv);
           assert (conn_ev == ev_cv cv);
           cons_append (ev_ee ee) [ ev_cert cert; ev_cv_local cv0 ] [conn_ev];
           cons_append (ev_cert cert) [ ev_cv_local cv0 ] [conn_ev];
           cons_append (ev_cv_local cv0) [] [conn_ev];
           snoc_tail pfx region [ ev_ee ee; ev_cert cert; ev_cv_local cv0 ] conn_ev;
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
           introduce exists (region2:list CS.conn_event).
               sefs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2
           with region and () )
       | CL.Sent, M.TlsHandshake (M.Finished sf) ->
         eliminate exists (region:list CS.conn_event). sefs_region_ok m0 st0.CS.cs_event_log region
         with
         ( let cert = Some?.v hs.CS.hs_certificate in
           let cv = Some?.v hs.CS.hs_certificate_verify in
           assert (conn_ev == ev_fin sf);
           cons_append (ev_ee ee) [ ev_cert cert; ev_cv_local cv; ev_cv cv ] [conn_ev];
           cons_append (ev_cert cert) [ ev_cv_local cv; ev_cv cv ] [conn_ev];
           cons_append (ev_cv_local cv) [ ev_cv cv ] [conn_ev];
           cons_append (ev_cv cv) [] [conn_ev];
           snoc_tail pfx region [ ev_ee ee; ev_cert cert; ev_cv_local cv; ev_cv cv ] conn_ev;
           assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
           introduce exists (region2:list CS.conn_event) (tail2:list CS.conn_event).
               sfs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 tail2
           with region [] and () )
       | _ -> ())
    | _ -> ()

#restart-solver
let step_from_sfs (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (tail:list CS.conn_event).
              sfs_region_ok m0 st0.CS.cs_event_log region tail);
    let sel = Some?.v hs.CS.hs_server_selection in
    let shared = Some?.v keys.CS.ks_shared_secret in
    let sh = Some?.v hs.CS.hs_server_hello in
    let ee = Some?.v hs.CS.hs_encrypted_extensions in
    let cert = Some?.v hs.CS.hs_certificate in
    let cv = Some?.v hs.CS.hs_certificate_verify in
    let sf = Some?.v hs.CS.hs_server_finished in
    let ch = sel.CS.server_selected_client_hello in
    let pfx = prefix ch sel shared sh in
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole ri) ->
      eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
          sfs_region_ok m0 st0.CS.cs_event_log region tail
      with
      ( let tail' = L.append tail [conn_ev] in
        suffix_snoc ee cert cv sf tail conn_ev;
        snoc_tail pfx region (suffix ee cert cv sf tail) conn_ev;
        assert (s'.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
        introduce exists (region2:list CS.conn_event) (tail2:list CS.conn_event).
            sfs_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 tail2
        with region tail' and () )
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_direction, msg.CL.message_value with
       | CL.Received, M.TlsHandshake (M.Finished cf) ->
         eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
             sfs_region_ok m0 st0.CS.cs_event_log region tail
         with
         ( let tail' = L.append tail [conn_ev] in
           assert (Some? keys.CS.ks_client_handshake_traffic);
           assert (has_read_install region);
           suffix_snoc ee cert cv sf tail conn_ev;
           snoc_tail pfx region (suffix ee cert cv sf tail) conn_ev;
           assert (s'.CS.cs_model.CS.model_control == CS.ControlApplicationData);
           introduce exists (region2:list CS.conn_event) (tail2:list CS.conn_event).
               appdata_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 tail2
           with region tail' and () )
       | _ -> ())
    | _ -> ()

let step_from_appdata (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma
      (requires hpre st0 s' conn_ev /\
                st0.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures log_shape s'.CS.cs_model s'.CS.cs_event_log)
  = let m0 = st0.CS.cs_model in
    let hs = m0.CS.model_handshake in
    let keys = hs.CS.hs_keys in
    assert (exists (region:list CS.conn_event) (tail:list CS.conn_event).
              appdata_region_ok m0 st0.CS.cs_event_log region tail);
    let sel = Some?.v hs.CS.hs_server_selection in
    let shared = Some?.v keys.CS.ks_shared_secret in
    let sh = Some?.v hs.CS.hs_server_hello in
    let ee = Some?.v hs.CS.hs_encrypted_extensions in
    let cert = Some?.v hs.CS.hs_certificate in
    let cv = Some?.v hs.CS.hs_certificate_verify in
    let sf = Some?.v hs.CS.hs_server_finished in
    let ch = sel.CS.server_selected_client_hello in
    let pfx = prefix ch sel shared sh in
    match conn_ev with
    | CS.ConnLocalEvent (CS.LocalDeliverApplicationData _) ->
      eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
          appdata_region_ok m0 st0.CS.cs_event_log region tail
      with
      ( let tail' = L.append tail [conn_ev] in
        suffix_snoc ee cert cv sf tail conn_ev;
        snoc_tail pfx region (suffix ee cert cv sf tail) conn_ev;
        assert (s'.CS.cs_model.CS.model_control == CS.ControlApplicationData);
        introduce exists (region2:list CS.conn_event) (tail2:list CS.conn_event).
            appdata_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 tail2
        with region tail' and () )
    | CS.ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsApplicationData _
       | M.TlsKeyUpdate _ ->
         (* A KeyUpdate is now legal for a server too.  Like application data it
            keeps the control state at ControlApplicationData and merely extends
            the log tail, so the canonical shape is re-established with the same
            region and a one-longer tail. *)
         eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
             appdata_region_ok m0 st0.CS.cs_event_log region tail
         with
         ( let tail' = L.append tail [conn_ev] in
           suffix_snoc ee cert cv sf tail conn_ev;
           snoc_tail pfx region (suffix ee cert cv sf tail) conn_ev;
           assert (s'.CS.cs_model.CS.model_control == CS.ControlApplicationData);
           introduce exists (region2:list CS.conn_event) (tail2:list CS.conn_event).
               appdata_region_ok s'.CS.cs_model s'.CS.cs_event_log region2 tail2
           with region tail' and () )
       | _ -> ())
    | _ -> ()
#pop-options

#push-options "--fuel 4 --ifuel 4 --z3rlimit 40"
let lemma_step_preserves_shape (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma (requires step_pre st0 s' conn_ev)
          (ensures server_canonical_shape s')
  = match st0.CS.cs_model.CS.model_control with
    | CS.ControlNew -> step_from_new st0 s' conn_ev
    | CS.ControlHandshaking CS.HsAwaitingClientHello -> step_from_awaiting st0 s' conn_ev
    | CS.ControlHandshaking CS.HsClientHelloReceived -> step_from_chr st0 s' conn_ev
    | CS.ControlHandshaking CS.HsServerHelloSent -> step_from_shs st0 s' conn_ev
    | CS.ControlHandshaking CS.HsServerEncryptedFlightSent -> step_from_sefs st0 s' conn_ev
    | CS.ControlHandshaking CS.HsServerFinishedSent -> step_from_sfs st0 s' conn_ev
    | CS.ControlApplicationData -> step_from_appdata st0 s' conn_ev
    | CS.ControlHandshaking CS.HsClientFinishedReceived -> ()
    | CS.ControlHandshaking CS.HsNotStarted -> ()
    | CS.ControlHandshaking CS.HsStarted -> ()
    | CS.ControlHandshaking CS.HsClientHelloSent -> ()
    | CS.ControlHandshaking CS.HsServerHelloReceived -> ()
    | CS.ControlHandshaking CS.HsEncryptedExtensionsReceived -> ()
    | CS.ControlHandshaking CS.HsCertificateReceived -> ()
    | CS.ControlHandshaking CS.HsCertificateValidated -> ()
    | CS.ControlHandshaking CS.HsCertificateVerifyReceived -> ()
    | CS.ControlHandshaking CS.HsCertificateVerifyVerified -> ()
    | CS.ControlHandshaking CS.HsServerFinishedReceived -> ()
    | CS.ControlHandshaking CS.HsServerFinishedVerified -> ()
    | CS.ControlHandshaking CS.HsClientFinishedSent -> ()
    | CS.ControlHandshaking CS.HsClientFinishedVerified -> ()
    | CS.ControlClosing -> ()
    | CS.ControlClosed -> ()
    | CS.ControlFailed _ -> ()
#pop-options

(* ================================================================== *)
(* Config preservation for one server step (role-agnostic)             *)
(* ================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_step_config
  (st0 s':CS.connection_state)
  (ev:SM.event CW.wire_message CTy.server_local_event)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires ES.server_step st0 ev s' out)
      (ensures
        s'.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
  (* Config preservation holds for EVERY server step, buffering included (a
     buffering step is inert on the config), so this one does not go through
     [lemma_server_step_facts]'s canonical-event classification. *)
  = match ev with
    | SM.WireEvent wire ->
      eliminate exists (conn_ev:CS.conn_event).
        (ES.server_wire_received_event conn_ev /\
         SMCan.canonical_wire_step st0 s' conn_ev
           (Common.WireFormat.serialize_all CW.tls_record_wire_format out.SM.so_wire_outputs)
           (CW.wire_serialize wire) /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs)
      with
        CLem.lemma_step_model_preserves_config st0.CS.cs_model conn_ev s'.CS.cs_model
    | SM.LocalEvent local ->
      eliminate exists (conn_ev:CS.conn_event) (raw_sent:B.bytes).
        (ES.server_representation_matches local conn_ev /\
         ES.server_wire_outputs_match raw_sent out.SM.so_wire_outputs /\
         ES.server_local_outputs_match conn_ev out.SM.so_local_outputs /\
         SMCan.canonical_wire_step st0 s' conn_ev raw_sent B.empty)
      with
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
                             CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires SM.trace_reaches (WStep.server_sm init) st0 trace st1)
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
        lemma_server_step_facts st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_log_extends init s' st1 rest;
        eliminate exists (conn_ev:CS.conn_event).
          (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
           CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
           CS.legal_event st0.CS.cs_model conn_ev /\
           is_server_canonical_event conn_ev)
        with
          eliminate exists (ext':list CS.conn_event).
            st1.CS.cs_event_log == L.append s'.CS.cs_event_log ext'
          with
          ( L.append_assoc st0.CS.cs_event_log [conn_ev] ext';
            introduce exists (ext:list CS.conn_event).
              st1.CS.cs_event_log == L.append st0.CS.cs_event_log ext
            with (L.append [conn_ev] ext') and () )
#pop-options

(* Lemma C: model_config is preserved along a trace. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
#restart-solver
let rec lemma_trace_config
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires SM.trace_reaches (WStep.server_sm init) st0 trace st1)
      (ensures
        st1.CS.cs_model.CS.model_config == st0.CS.cs_model.CS.model_config)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_server_step_config st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_config init s' st1 rest
#pop-options

(* Lemma B: shape is preserved along a CCS-free trace. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_trace_shape
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
        server_canonical_shape st0 /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        log_has_no_received_ccs st1.CS.cs_event_log)
      (ensures server_canonical_shape st1)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_server_step_facts st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_server_step_config st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_log_extends init s' st1 rest;
        eliminate exists (conn_ev:CS.conn_event).
          (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
           CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
           CS.legal_event st0.CS.cs_model conn_ev /\
           is_server_canonical_event conn_ev)
        with
          eliminate exists (ext':list CS.conn_event).
            st1.CS.cs_event_log == L.append s'.CS.cs_event_log ext'
          with
          (
            L.append_memP st0.CS.cs_event_log [conn_ev] conn_ev;
            L.append_memP s'.CS.cs_event_log ext' conn_ev;
            assert (is_received_ccs conn_ev == false);
            lemma_step_preserves_shape st0 s' conn_ev;
            lemma_trace_shape init s' st1 rest
          )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_canonical_appdata_exact_spine
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures
       (exists (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
          (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
          (region:list CS.conn_event) (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_server_hs_install e == true) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_server_hs_install_dir CS.TrafficWrite ew) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_server_hs_install_dir CS.TrafficRead er) /\
          s.CS.cs_event_log ==
            L.append
              (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_local ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail))))
  = let init = CS.initial cfg in
    lemma_shape_initial cfg;
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                                 CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches (WStep.server_sm init) init trace s
    with
    (
      lemma_trace_config init init s trace;
      lemma_trace_shape init init s trace;
      (* server_canonical_shape s, role Server, control ControlApplicationData
         gives exactly the AppData existential; instantiate cv_local. *)
      (* server_canonical_shape s at ControlApplicationData gives the region/tail existential. *)
      assert (server_canonical_shape s);
      eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
        appdata_region_ok s.CS.cs_model s.CS.cs_event_log region tail
      with
      (
        let hs = s.CS.cs_model.CS.model_handshake in
        let keys = hs.CS.hs_keys in
        let sel = Some?.v hs.CS.hs_server_selection in
        let shared = Some?.v keys.CS.ks_shared_secret in
        let sh = Some?.v hs.CS.hs_server_hello in
        let ee = Some?.v hs.CS.hs_encrypted_extensions in
        let cert = Some?.v hs.CS.hs_certificate in
        let cv = Some?.v hs.CS.hs_certificate_verify in
        let sf = Some?.v hs.CS.hs_server_finished in
        let ch = sel.CS.server_selected_client_hello in
        introduce exists (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
          (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
          (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
          (cv_local:CS.local_event) (cv:GCV.certificateVerify) (sf:GFin.finished)
          (region:list CS.conn_event) (tail:list CS.conn_event).
          (forall (e:CS.conn_event). L.memP e region ==> is_server_hs_install e == true) /\
          (exists (ew:CS.conn_event). L.memP ew region /\ is_server_hs_install_dir CS.TrafficWrite ew) /\
          (exists (er:CS.conn_event). L.memP er region /\ is_server_hs_install_dir CS.TrafficRead er) /\
          s.CS.cs_event_log ==
            L.append
              (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
              (L.append region
                 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert) } ::
                  CS.ConnLocalEvent cv_local ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv) } ::
                  CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf) } ::
                  tail))
        with ch sel shared sh ee cert (CS.LocalSignCertificateVerify cv) cv sf region tail
        and ()
      )
    )
#pop-options

(* ================================================================== *)
(* Shared-secret PRESENCE at HsServerFinishedSent.                     *)
(*                                                                     *)
(* Server mirror of                                                    *)
(* [ClientCanonicalShape.lemma_client_reachable_sfv_shared_secret_present]. *)
(* [sfs_region_ok] matches [Some shared] and every other case is       *)
(* [False], so the canonical shape pins [Some? ks_shared_secret] at    *)
(* [HsServerFinishedSent] — non-ready, from canonical reachability +   *)
(* no-received-CCS.                                                     *)
(* ================================================================== *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_sfs_shared_secret_present
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       s.CS.cs_model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
  = let init = CS.initial cfg in
    lemma_shape_initial cfg;
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                                 CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches (WStep.server_sm init) init trace s
    with
    (
      lemma_trace_config init init s trace;
      lemma_trace_shape init init s trace;
      assert (server_canonical_shape s);
      eliminate exists (region:list CS.conn_event) (tail:list CS.conn_event).
          sfs_region_ok s.CS.cs_model s.CS.cs_event_log region tail
      with ()
    )
#pop-options

(* ================================================================== *)
(* Traffic-slot PRESENCE forces both hellos, monotonically.            *)
(*                                                                     *)
(* The server READ handshake key ([ks_client_handshake_traffic]) is    *)
(* installed only at [HsServerHelloSent] (via                          *)
(* [traffic_install_allowed_at_stage_for_role]); at every server       *)
(* control from [HsServerHelloSent] onward the ServerHello and the     *)
(* ClientHello are already present, and no step ever clears those      *)
(* fields or the slot (in particular [fail_model] preserves            *)
(* [model_handshake]).  Unlike [server_canonical_shape] (control-keyed, *)
(* [True] at [ControlFailed]) this invariant survives ControlFailed.   *)
(* ================================================================== *)

(* At every server control where the READ slot can already be present,
   the two hellos are recorded.  [HsServerHelloSent] onward forces both;
   [HsClientHelloReceived] forces only the client hello (server hello is
   sent later).  All other controls carry no constraint. *)
let control_forces_hellos (m:CS.connection_model) : prop =
  match m.CS.model_control with
  | CS.ControlHandshaking CS.HsServerHelloSent
  | CS.ControlHandshaking CS.HsServerEncryptedFlightSent
  | CS.ControlHandshaking CS.HsServerFinishedSent
  | CS.ControlApplicationData ->
    Some? m.CS.model_handshake.CS.hs_server_hello /\
    Some? m.CS.model_handshake.CS.hs_client_hello
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    Some? m.CS.model_handshake.CS.hs_client_hello
  | _ -> True

(* The monotone invariant carried through the canonical trace. *)
let hellos_inv (m:CS.connection_model) : prop =
  m.CS.model_config.CS.config_role == CS.ServerEndpoint ==>
    ( (Some? m.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic ==>
         (Some? m.CS.model_handshake.CS.hs_server_hello /\
          Some? m.CS.model_handshake.CS.hs_client_hello)) /\
      control_forces_hellos m )

(* Single-step preservation of [hellos_inv].  [step_pre] provides
   [server_canonical_shape st0], which is used only to exclude the
   canonically-unreachable [HsClientFinishedReceived] control (whose
   [log_shape] is [False]); every other case is field monotonicity plus the
   install-stage constraint from [legal_event]. *)
#push-options "--fuel 4 --ifuel 6 --z3rlimit 40"
let lemma_step_preserves_hellos (st0 s':CS.connection_state) (conn_ev:CS.conn_event)
  : Lemma (requires step_pre st0 s' conn_ev /\ hellos_inv st0.CS.cs_model)
          (ensures hellos_inv s'.CS.cs_model)
  = CLem.lemma_step_model_preserves_config st0.CS.cs_model conn_ev s'.CS.cs_model
#pop-options

(* Trace induction: carry both [server_canonical_shape] and [hellos_inv]. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec lemma_trace_hellos
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                             CTy.server_local_event EAPI.local_output))
  : Lemma
      (requires
        SM.trace_reaches (WStep.server_sm init) st0 trace st1 /\
        server_canonical_shape st0 /\
        hellos_inv st0.CS.cs_model /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        log_has_no_received_ccs st1.CS.cs_event_log)
      (ensures hellos_inv st1.CS.cs_model)
      (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
        let s' = tr.SM.tr_next_state in
        lemma_server_step_facts st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_server_step_config st0 s' tr.SM.tr_event tr.SM.tr_output;
        lemma_trace_log_extends init s' st1 rest;
        eliminate exists (conn_ev:CS.conn_event).
          (s'.CS.cs_event_log == L.append st0.CS.cs_event_log [conn_ev] /\
           CS.step_model st0.CS.cs_model conn_ev == Some s'.CS.cs_model /\
           CS.legal_event st0.CS.cs_model conn_ev /\
           is_server_canonical_event conn_ev)
        with
          eliminate exists (ext':list CS.conn_event).
            st1.CS.cs_event_log == L.append s'.CS.cs_event_log ext'
          with
          (
            L.append_memP st0.CS.cs_event_log [conn_ev] conn_ev;
            L.append_memP s'.CS.cs_event_log ext' conn_ev;
            assert (is_received_ccs conn_ev == false);
            lemma_step_preserves_shape st0 s' conn_ev;
            lemma_step_preserves_hellos st0 s' conn_ev;
            lemma_trace_hellos init s' st1 rest
          )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_server_reachable_traffic_slot_hellos_present
  (cfg:CS.connection_config) (s:CS.connection_state)
  : Lemma
    (requires
       WStep.server_reachable (CS.initial cfg) s /\
       s.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
       log_has_no_received_ccs s.CS.cs_event_log)
    (ensures
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
       Some? s.CS.cs_model.CS.model_handshake.CS.hs_client_hello)
  = let init = CS.initial cfg in
    lemma_shape_initial cfg;
    assert (hellos_inv init.CS.cs_model);
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                                 CTy.server_local_event EAPI.local_output)).
      SM.trace_reaches (WStep.server_sm init) init trace s
    with
    (
      lemma_trace_config init init s trace;
      lemma_trace_hellos init init s trace
    )
#pop-options

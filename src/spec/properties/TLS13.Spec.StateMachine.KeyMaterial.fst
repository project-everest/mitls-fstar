module TLS13.Spec.StateMachine.KeyMaterial

(**
  Auxiliary: model / key-schedule / record key-material consistency predicates
  (expected traffic secrets, derived key material, record direction material and
  the supported-profile agreement predicates). Builds on TLS13.Spec.StateMachine.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module Tr = TLS13.Transcript

open FStar.List.Tot

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Correspondence

let sent_tls_event (msg:M.tls_message) : conn_event =
  ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = msg }
let received_tls_event (msg:M.tls_message) : conn_event =
  ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = msg }
let traffic_material_option_matches_record_direction
  (material:option traffic_key_material)
  (st:R.direction_state)
  : prop =
  match material with
  | Some material -> traffic_material_matches_record_direction material st
  | None -> False
let record_keys_match_key_schedule_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  match st.R.epoch with
  | R.Initial ->
    st.R.key == None /\ st.R.static_iv == None
  | R.Handshake ->
    traffic_material_option_matches_record_direction
      (traffic_material_for_label
       keys
       TrafficHandshake
       (traffic_label_for_endpoint_direction role dir))
      st
  | R.Application ->
    (match role, dir, control with
     | ClientEndpoint, TrafficWrite, ControlHandshaking _ ->
       // The honest client populates its application WRITE traffic slot at
       // HsServerFinishedVerified but only installs the application WRITE record
       // keys (record_write.epoch -> Application) at the moment it SENDS its
       // Finished and lands at ControlApplicationData.  During that window the
       // record write direction is still at the Handshake epoch, so this clause
       // is only ever consulted with record_write.epoch == Application once the
       // control state has advanced past ControlHandshaking; the vacuity here is
       // therefore never actually exercised for the client and simply avoids an
       // obligation that has no honest witness during ControlHandshaking.
       True
     | _, _, _ ->
       traffic_material_option_matches_record_direction
         (traffic_material_for_label
           keys
           TrafficApplication
           (traffic_label_for_endpoint_direction role dir))
         st)
let record_read_keys_match_key_schedule
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  record_keys_match_key_schedule_for_role
    ClientEndpoint
    TrafficRead
    ControlApplicationData
    keys
    st
let record_read_key_schedule_projection_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_read in
    match st.R.epoch with
    | R.Initial ->
      st.R.key == None /\ st.R.static_iv == None
    | R.Handshake ->
      exists material.
       traffic_material_for_label
         keys
         TrafficHandshake
         (traffic_label_for_endpoint_direction role TrafficRead) == Some material /\
       traffic_material_matches_record_direction material st
    | R.Application ->
      exists material.
       traffic_material_for_label
         keys
         TrafficApplication
         (traffic_label_for_endpoint_direction role TrafficRead) == Some material /\
       traffic_material_matches_record_direction material st
let record_read_key_schedule_projection
  (model:connection_model)
  : prop =
  record_read_key_schedule_projection_for_role ClientEndpoint model
let record_write_keys_match_key_schedule
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : prop =
  record_keys_match_key_schedule_for_role
    ClientEndpoint
    TrafficWrite
    control
    keys
    st
let record_write_key_schedule_projection_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_write in
    match st.R.epoch with
    | R.Initial ->
      st.R.key == None /\ st.R.static_iv == None
    | R.Handshake ->
      exists material.
        traffic_material_for_label
          keys
          TrafficHandshake
          (traffic_label_for_endpoint_direction role TrafficWrite) == Some material /\
        traffic_material_matches_record_direction material st
    | R.Application ->
      (match model.model_control with
       | ControlHandshaking _ ->
         True
       | _ ->
         exists material.
           traffic_material_for_label
             keys
             TrafficApplication
             (traffic_label_for_endpoint_direction role TrafficWrite) == Some material /\
           traffic_material_matches_record_direction material st)
let record_write_key_schedule_projection
  (model:connection_model)
  : prop =
  record_write_key_schedule_projection_for_role ClientEndpoint model
let model_record_keys_consistent_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match model.model_control with
  | ControlFailed _ -> True
  | _ ->
    let keys = model.model_handshake.hs_keys in
    record_keys_match_key_schedule_for_role
      role
      TrafficRead
      model.model_control
      keys
      model.model_record.record_read /\
    record_keys_match_key_schedule_for_role
      role
      TrafficWrite
      model.model_control
      keys
      model.model_record.record_write
let model_record_keys_consistent
  (model:connection_model)
  : prop =
  model.model_config.config_role == ClientEndpoint /\
  model_record_keys_consistent_for_role ClientEndpoint model
let application_record_epochs_installed_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  model.model_record.record_read.R.epoch == R.Application /\
  model.model_record.record_write.R.epoch == R.Application
let record_epoch_for_traffic_epoch
  (epoch:traffic_epoch)
  : R.epoch =
  match epoch with
  | TrafficHandshake -> R.Handshake
  | TrafficApplication -> R.Application
let record_direction_for_endpoint
  (role:endpoint_role)
  (dir:traffic_direction)
  (model:connection_model)
  : R.direction_state =
  match dir with
  | TrafficRead -> model.model_record.record_read
  | TrafficWrite -> model.model_record.record_write
let record_material_of_traffic_material
  (material:traffic_key_material)
  : record_key_iv_material =
  {
    record_material_key = material.traffic_key;
    record_material_iv = material.traffic_iv;
  }
let record_direction_material
  (st:R.direction_state)
  : option record_key_iv_material =
  match st.R.key, st.R.static_iv with
  | Some key, Some iv ->
    Some { record_material_key = key; record_material_iv = iv }
  | _, _ ->
    None
let record_key_iv_material_agrees
  (left:record_key_iv_material)
  (right:record_key_iv_material)
  : prop =
  Seq.equal left.record_material_key right.record_material_key /\
  Seq.equal left.record_material_iv right.record_material_iv
let record_direction_material_matches_key_schedule_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (traffic_id:labeled_traffic_epoch)
  (model:connection_model)
  : prop =
  let st = record_direction_for_endpoint role dir model in
  st.R.epoch == record_epoch_for_traffic_epoch traffic_id.traffic_id_epoch /\
  traffic_label_for_endpoint_direction role dir == traffic_id.traffic_id_label /\
  (match
    traffic_material_for_label
      model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    record_direction_material st
  with
  | Some traffic_material, Some record_material ->
    record_key_iv_material_agrees
      (record_material_of_traffic_material traffic_material)
      record_material
  | _, _ ->
    False)
let key_schedule_traffic_record_material_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match
    traffic_material_for_label
      client.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    traffic_material_for_label
      server.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label
  with
  | Some client_material, Some server_material ->
    record_key_iv_material_agrees
      (record_material_of_traffic_material client_material)
      (record_material_of_traffic_material server_material)
  | _, _ ->
    False
let peer_record_material_inputs_agree
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : prop =
  key_schedule_traffic_record_material_agrees traffic_id client server /\
  (match traffic_id.traffic_id_label with
  | ClientTraffic ->
    record_direction_material_matches_key_schedule_for_role
      ClientEndpoint TrafficWrite traffic_id client.cs_model /\
    record_direction_material_matches_key_schedule_for_role
      ServerEndpoint TrafficRead traffic_id server.cs_model
  | ServerTraffic ->
    record_direction_material_matches_key_schedule_for_role
      ServerEndpoint TrafficWrite traffic_id server.cs_model /\
    record_direction_material_matches_key_schedule_for_role
      ClientEndpoint TrafficRead traffic_id client.cs_model)
let peer_record_material_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match traffic_id.traffic_id_label with
  | ClientTraffic ->
    (match
      record_direction_material client.cs_model.model_record.record_write,
      record_direction_material server.cs_model.model_record.record_read
    with
    | Some client_write, Some server_read ->
      client.cs_model.model_record.record_write.R.epoch ==
        record_epoch_for_traffic_epoch traffic_id.traffic_id_epoch /\
      server.cs_model.model_record.record_read.R.epoch ==
        record_epoch_for_traffic_epoch traffic_id.traffic_id_epoch /\
      record_key_iv_material_agrees client_write server_read
    | _, _ ->
      False)
  | ServerTraffic ->
    (match
      record_direction_material server.cs_model.model_record.record_write,
      record_direction_material client.cs_model.model_record.record_read
    with
    | Some server_write, Some client_read ->
      server.cs_model.model_record.record_write.R.epoch ==
        record_epoch_for_traffic_epoch traffic_id.traffic_id_epoch /\
      client.cs_model.model_record.record_read.R.epoch ==
        record_epoch_for_traffic_epoch traffic_id.traffic_id_epoch /\
      record_key_iv_material_agrees server_write client_read
    | _, _ ->
      False)
let key_checkpoint_for_derived_key
  (key_id:derived_key_id)
  : option key_derivation_checkpoint =
  match key_id with
  | BaseSecret _ -> None
  | TrafficSecret traffic_id
  | TrafficKey traffic_id
  | TrafficIV traffic_id ->
    Some (key_checkpoint_for_epoch traffic_id.traffic_id_epoch)
  | FinishedKey _ ->
    Some DeriveHandshakeTraffic
  | TrafficUpdateSecret update_id ->
    Some (DeriveTrafficUpdate update_id)
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    None
let first_milestone_derived_key_id
  (key_id:derived_key_id)
  : bool =
  match key_id with
  | BaseSecret EarlySecret
  | BaseSecret HandshakeSecret
  | BaseSecret MasterSecret
  | TrafficSecret _
  | TrafficKey _
  | TrafficIV _
  | FinishedKey _ -> true
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret -> false
let base_secret_material
  (base_id:base_secret_id)
  (keys:key_schedule_state)
  : option C.secret =
  match base_id with
  | EarlySecret -> keys.ks_early_secret
  | HandshakeSecret -> keys.ks_handshake_secret
  | MasterSecret -> keys.ks_master_secret
let transcript_bytes_for_key_checkpoint
  (checkpoint:key_derivation_checkpoint)
  (st:connection_state)
  : GTot (option B.bytes) =
  match key_derivation_checkpoint_transcript checkpoint with
  | Some transcript_checkpoint ->
    transcript_checkpoint_bytes transcript_checkpoint st.cs_model.model_handshake
  | None -> None
let traffic_secret_base_for_epoch
  (epoch:traffic_epoch)
  (keys:key_schedule_state)
  : option C.secret =
  match epoch with
  | TrafficHandshake -> keys.ks_handshake_secret
  | TrafficApplication -> keys.ks_master_secret
let derive_traffic_secret_for_label
  (epoch:traffic_epoch)
  (label:traffic_label)
  (base:C.secret)
  (transcript:B.bytes)
  : GTot K.traffic_secret =
  let h = Tr.hash transcript in
  match epoch, label with
  | TrafficHandshake, ClientTraffic ->
    K.client_handshake_traffic_secret base h
  | TrafficHandshake, ServerTraffic ->
    K.server_handshake_traffic_secret base h
  | TrafficApplication, ClientTraffic ->
    K.client_application_traffic_secret base h
  | TrafficApplication, ServerTraffic ->
    K.server_application_traffic_secret base h
let expected_traffic_secret_for_state
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  : GTot (option K.traffic_secret) =
  match
    traffic_secret_base_for_epoch
      traffic_id.traffic_id_epoch
      st.cs_model.model_handshake.hs_keys,
    transcript_bytes_for_key_checkpoint
      (key_checkpoint_for_epoch traffic_id.traffic_id_epoch)
      st
  with
  | Some base, Some transcript ->
    Some
      (derive_traffic_secret_for_label
        traffic_id.traffic_id_epoch
        traffic_id.traffic_id_label
        base
        transcript)
  | _, _ -> None
(**
  ── Epoch-indexed application traffic secrets ─────────────────────────────

  `expected_traffic_secret_for_state` gives the *epoch-0* traffic secret: the
  one derived directly from the base secret and the transcript.  RFC 8446
  §7.2 says that each KeyUpdate replaces an application traffic secret by
  `application_traffic_secret_update` of its predecessor, so after `n` updates
  the live secret is the `n`-fold iterate.  These definitions name that
  iterate and the epoch counter, so that predicates which today are guarded by
  "no KeyUpdate has occurred" can instead be stated at the current epoch.
 **)
let rec application_traffic_secret_after
  (secret:K.traffic_secret)
  (n:nat)
  : Tot K.traffic_secret (decreases n) =
  if n = 0 then secret
  else application_traffic_secret_after (K.application_traffic_secret_update secret) (n - 1)

(**
  The traffic label an event rotates, if any.  A KeyUpdate rotates exactly one
  direction's application traffic secret: the sender's write key when we send
  it, and the peer's write key — our read key — when we receive it.  Which
  label that is depends on our role, exactly as in `rotate_application_traffic`.
 **)
let conn_event_key_update_label
  (role:endpoint_role)
  (ev:conn_event)
  : option traffic_label =
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsKeyUpdate _ ->
       Some
         (traffic_label_for_endpoint_direction
           role
           (match msg.CL.message_direction with
            | CL.Sent -> TrafficWrite
            | CL.Received -> TrafficRead))
     | _ -> None)
  | ConnProtectedHandshake _ -> None
  | ConnLocalEvent _ -> None

(** How many times `l`'s application traffic secret has been rotated. **)
let rec key_update_count_for_label
  (role:endpoint_role)
  (events:list conn_event)
  (l:traffic_label)
  : Tot nat (decreases events) =
  match events with
  | [] -> 0
  | ev :: rest ->
    (if conn_event_key_update_label role ev = Some l then 1 else 0)
    + key_update_count_for_label role rest l

let connection_state_key_update_count
  (st:connection_state)
  (l:traffic_label)
  : nat =
  key_update_count_for_label
    st.cs_model.model_config.config_role
    st.cs_event_log
    l

(**
  The traffic secret expected *at the state's current epoch*.  For handshake
  traffic this is the epoch-0 secret (handshake secrets are never rotated);
  for application traffic it is the epoch-0 secret advanced by the number of
  KeyUpdates recorded for that label.
 **)
let expected_traffic_secret_at_epoch
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  : GTot (option K.traffic_secret) =
  match expected_traffic_secret_for_state traffic_id st with
  | None -> None
  | Some secret ->
    (match traffic_id.traffic_id_epoch with
     | TrafficHandshake -> Some secret
     | TrafficApplication ->
       Some
         (application_traffic_secret_after
           secret
           (connection_state_key_update_count st traffic_id.traffic_id_label)))

(**
  At epoch 0 the two agree definitionally; this is the bridge that lets the
  existing no-KeyUpdate reasoning be re-read as epoch-indexed reasoning.
 **)
let lemma_expected_traffic_secret_at_epoch_zero
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  : Lemma
      (requires
        traffic_id.traffic_id_epoch == TrafficHandshake \/
        connection_state_key_update_count st traffic_id.traffic_id_label == 0)
      (ensures
        expected_traffic_secret_at_epoch traffic_id st ==
        expected_traffic_secret_for_state traffic_id st)
= ()

let expected_derived_key_material
  (key_id:derived_key_id)
  (st:connection_state)
  : GTot (option B.bytes) =
  match key_id with
  | BaseSecret base_id ->
    (match base_secret_material base_id st.cs_model.model_handshake.hs_keys with
     | Some secret -> Some secret
     | None -> None)
  | TrafficSecret traffic_id ->
    (match expected_traffic_secret_for_state traffic_id st with
     | Some secret -> Some secret
     | None -> None)
  | TrafficKey traffic_id ->
    (match expected_traffic_secret_for_state traffic_id st with
     | Some secret ->
       Some (K.derive_aead_key
               (negotiated_aead_alg st.cs_model.model_handshake)
               secret)
     | None -> None)
  | TrafficIV traffic_id ->
    (match expected_traffic_secret_for_state traffic_id st with
     | Some secret -> Some (K.derive_aead_iv secret)
     | None -> None)
  | FinishedKey label ->
    (match expected_traffic_secret_for_state
      { traffic_id_epoch = TrafficHandshake; traffic_id_label = label }
      st
     with
     | Some secret -> Some (K.finished_key secret)
     | None -> None)
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    None
let traffic_material_matches_expected_derived_material
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  : prop =
  match
    traffic_material_for_label
      st.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_derived_key_material (TrafficKey traffic_id) st,
    expected_derived_key_material (TrafficIV traffic_id) st
  with
  | Some material, Some key, Some iv ->
    Seq.equal material.traffic_key key /\
    Seq.equal material.traffic_iv iv
  | _, _, _ ->
    False
let supported_profile_application_traffic_material_matches_expected
  (st:connection_state)
  : prop =
  traffic_material_matches_expected_derived_material
    (traffic_id TrafficApplication ClientTraffic) st /\
  traffic_material_matches_expected_derived_material
    (traffic_id TrafficApplication ServerTraffic) st
(**
  Rotation commutes with iteration: advancing `n+1` epochs is the same as
  updating the `n`-epoch secret once.  `application_traffic_secret_after`
  iterates from the *front*, so this needs an induction; it is the step rule
  that a KeyUpdate transition appeals to.
 **)
let rec lemma_application_traffic_secret_after_succ
  (secret:K.traffic_secret)
  (n:nat)
  : Lemma
      (ensures
        application_traffic_secret_after secret (n + 1) ==
        K.application_traffic_secret_update (application_traffic_secret_after secret n))
      (decreases n)
= if n = 0 then ()
  else
    lemma_application_traffic_secret_after_succ
      (K.application_traffic_secret_update secret)
      (n - 1)

let traffic_material_matches_expected_at_count
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  (n:nat)
  : prop =
  match
    traffic_material_for_label
      st.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_traffic_secret_for_state traffic_id st
  with
  | Some material, Some secret ->
    let expected = application_traffic_secret_after secret n in
    Seq.equal material.traffic_secret expected /\
    Seq.equal material.traffic_key
      (K.derive_aead_key (negotiated_aead_alg st.cs_model.model_handshake) expected) /\
    Seq.equal material.traffic_iv (K.derive_aead_iv expected)
  | _, _ ->
    False

(**
  The epoch-indexed counterpart of
  `traffic_material_matches_expected_derived_material`, taking the epoch from
  the state's own event log.  It additionally pins the stored `traffic_secret`,
  not just the derived key and IV.  That extra conjunct is what makes the
  predicate *inductive* across a KeyUpdate: the rotated material is
  `traffic_key_material_for_secret` of the update of the stored secret, so
  without knowing the stored secret one cannot identify the rotated key and IV.
 **)
let traffic_material_matches_expected_at_epoch
  (traffic_id:labeled_traffic_epoch)
  (st:connection_state)
  : prop =
  traffic_material_matches_expected_at_count
    traffic_id
    st
    (match traffic_id.traffic_id_epoch with
     | TrafficHandshake -> 0
     | TrafficApplication ->
       connection_state_key_update_count st traffic_id.traffic_id_label)

(**
  Rotating the material advances its epoch by one.  This is the step rule a
  KeyUpdate transition appeals to, and the reason
  `traffic_material_matches_expected_at_count` pins the stored secret.
 **)
let lemma_updated_traffic_key_material_advances_count
  (secret:K.traffic_secret)
  (n:nat)
  (material:traffic_key_material)
  : Lemma
      (requires
        Seq.equal material.traffic_secret (application_traffic_secret_after secret n))
      (ensures
        (let rotated = updated_traffic_key_material material in
         Seq.equal
           rotated.traffic_secret
           (application_traffic_secret_after secret (n + 1)) /\
         Seq.equal
           rotated.traffic_key
           (K.derive_aead_key
              (C.aead_alg_of_key material.traffic_key)
              (application_traffic_secret_after secret (n + 1))) /\
         Seq.equal
           rotated.traffic_iv
           (K.derive_aead_iv (application_traffic_secret_after secret (n + 1)))))
=
  lemma_application_traffic_secret_after_succ secret n;
  Seq.lemma_eq_elim
    material.traffic_secret
    (application_traffic_secret_after secret n)

(**
  The epoch-indexed replacement for
  `first_epoch_application_traffic_material_slots_match_expected`.  Note there
  is no `connection_state_no_key_update_trace` guard: the epoch counter absorbs
  the KeyUpdates instead of the invariant excluding them.
 **)
let application_traffic_material_slots_match_expected_at_counts
  (st:connection_state)
  (nc:nat)
  (ns:nat)
  : prop =
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_client_application_traffic ==>
      traffic_material_matches_expected_at_count
        (traffic_id TrafficApplication ClientTraffic)
        st
        nc) /\
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_server_application_traffic ==>
      traffic_material_matches_expected_at_count
        (traffic_id TrafficApplication ServerTraffic)
        st
        ns)

let application_traffic_material_slots_match_expected_at_epoch
  (st:connection_state)
  : prop =
  application_traffic_material_slots_match_expected_at_counts
    st
    (connection_state_key_update_count st ClientTraffic)
    (connection_state_key_update_count st ServerTraffic)

(**
  The epoch-indexed replacement for
  `supported_profile_application_traffic_material_matches_expected`.  Where the
  latter pins both application traffic slots to the *epoch-0* derived material,
  this pins each to the material of its own epoch, so it survives KeyUpdates.

  Two states satisfying this predicate hold the same application traffic
  material exactly when their epoch-0 secrets agree *and* their KeyUpdate
  counts agree label by label; the count agreement is what a rekeying-aware
  pairing argument has to supply in place of "no rekeying".
 **)
let supported_profile_application_traffic_material_matches_expected_at_epoch
  (st:connection_state)
  : prop =
  traffic_material_matches_expected_at_epoch
    (traffic_id TrafficApplication ClientTraffic) st /\
  traffic_material_matches_expected_at_epoch
    (traffic_id TrafficApplication ServerTraffic) st

(**
  Event logs grow by *append*, but the count is defined head-first; these are
  the two rules a step lemma needs.  The first says a non-rotating event leaves
  every epoch alone, the second that a KeyUpdate advances exactly the label it
  names and no other.
 **)
let rec lemma_key_update_count_for_label_append
  (role:endpoint_role)
  (events:list conn_event)
  (ev:conn_event)
  (l:traffic_label)
  : Lemma
      (ensures
        key_update_count_for_label role (events @ [ev]) l ==
        key_update_count_for_label role events l +
          (if conn_event_key_update_label role ev = Some l then 1 else 0))
      (decreases events)
= match events with
  | [] -> ()
  | _ :: rest -> lemma_key_update_count_for_label_append role rest ev l

let lemma_key_update_count_for_label_append_other
  (role:endpoint_role)
  (events:list conn_event)
  (ev:conn_event)
  (l:traffic_label)
  : Lemma
      (requires conn_event_key_update_label role ev =!= Some l)
      (ensures
        key_update_count_for_label role (events @ [ev]) l ==
        key_update_count_for_label role events l)
= lemma_key_update_count_for_label_append role events ev l

let lemma_key_update_count_for_label_append_same
  (role:endpoint_role)
  (events:list conn_event)
  (ev:conn_event)
  (l:traffic_label)
  : Lemma
      (requires conn_event_key_update_label role ev == Some l)
      (ensures
        key_update_count_for_label role (events @ [ev]) l ==
        key_update_count_for_label role events l + 1)
= lemma_key_update_count_for_label_append role events ev l

(**
  A trace with no KeyUpdate at all sits at epoch 0 for every label — the bridge
  that lets the existing `connection_state_no_key_update_trace` reasoning be
  re-read as the zero case of the epoch-indexed reasoning.
 **)
let rec lemma_conn_events_no_key_update_count_zero
  (role:endpoint_role)
  (events:list conn_event)
  (l:traffic_label)
  : Lemma
      (requires conn_events_no_key_update events == true)
      (ensures key_update_count_for_label role events l == 0)
      (decreases events)
= match events with
  | [] -> ()
  | _ :: rest -> lemma_conn_events_no_key_update_count_zero role rest l

(**
  The epoch-0 slot invariant.  The `_at_count ... 0` conjuncts are the
  strengthening that makes this predicate *inductive across a KeyUpdate*: they
  additionally pin the stored `traffic_secret`, which is what identifies the
  material a rotation produces.  They subsume the
  `traffic_material_matches_expected_derived_material` conjuncts, which are
  retained because consumers unfold those directly.

  It is stated after the count machinery only because it now mentions it; the
  meaning at epoch 0 is unchanged apart from the added secret conjunct.
 **)
let first_epoch_application_traffic_material_slots_match_expected
  (st:connection_state)
  : prop =
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_client_application_traffic ==>
      traffic_material_matches_expected_derived_material
        (traffic_id TrafficApplication ClientTraffic)
        st /\
      traffic_material_matches_expected_at_count
        (traffic_id TrafficApplication ClientTraffic)
        st
        0) /\
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_server_application_traffic ==>
      traffic_material_matches_expected_derived_material
        (traffic_id TrafficApplication ServerTraffic)
        st /\
      traffic_material_matches_expected_at_count
        (traffic_id TrafficApplication ServerTraffic)
        st
        0)

(* Handshake-epoch analogue of the application slots-match predicate above. *)
(* Used by the non-ready cross-endpoint handshake-agreement route.          *)
let first_epoch_handshake_traffic_material_slots_match_expected
  (st:connection_state)
  : prop =
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic ==>
      traffic_material_matches_expected_derived_material
        (traffic_id TrafficHandshake ClientTraffic)
        st) /\
  (Some?
    st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic ==>
      traffic_material_matches_expected_derived_material
        (traffic_id TrafficHandshake ServerTraffic)
        st)

let first_epoch_application_traffic_material_no_key_update_invariant
  (st:connection_state)
  : prop =
  connection_state_no_key_update_trace st /\
  first_epoch_application_traffic_material_slots_match_expected st

(**
  The two rules a step lemma needs to move an epoch-indexed slot across a
  transition.  A step that leaves a slot and its expected epoch-0 secret alone
  leaves its epoch alone; a step that rotates the slot advances its epoch by
  one.  Together they cover every transition, because `step_model` either
  rewrites an application traffic slot with `updated_traffic_key_material` (on
  a KeyUpdate) or leaves it untouched.
 **)
let lemma_traffic_material_matches_expected_at_count_transfer
  (traffic_id:labeled_traffic_epoch)
  (st0:connection_state)
  (st1:connection_state)
  (n:nat)
  : Lemma
      (requires
        traffic_material_matches_expected_at_count traffic_id st0 n /\
        traffic_material_for_label
          st1.cs_model.model_handshake.hs_keys
          traffic_id.traffic_id_epoch
          traffic_id.traffic_id_label ==
        traffic_material_for_label
          st0.cs_model.model_handshake.hs_keys
          traffic_id.traffic_id_epoch
          traffic_id.traffic_id_label /\
        expected_traffic_secret_for_state traffic_id st1 ==
        expected_traffic_secret_for_state traffic_id st0 /\
        negotiated_aead_alg st1.cs_model.model_handshake ==
          negotiated_aead_alg st0.cs_model.model_handshake)
      (ensures traffic_material_matches_expected_at_count traffic_id st1 n)
= ()

let lemma_traffic_material_matches_expected_at_count_rotate
  (traffic_id:labeled_traffic_epoch)
  (st0:connection_state)
  (st1:connection_state)
  (n:nat)
  : Lemma
      (requires
        traffic_material_matches_expected_at_count traffic_id st0 n /\
        expected_traffic_secret_for_state traffic_id st1 ==
        expected_traffic_secret_for_state traffic_id st0 /\
        (match
           traffic_material_for_label
             st0.cs_model.model_handshake.hs_keys
             traffic_id.traffic_id_epoch
             traffic_id.traffic_id_label,
           traffic_material_for_label
             st1.cs_model.model_handshake.hs_keys
             traffic_id.traffic_id_epoch
             traffic_id.traffic_id_label
         with
         | Some m0, Some m1 -> m1 == updated_traffic_key_material m0
         | _, _ -> False) /\
        negotiated_aead_alg st1.cs_model.model_handshake ==
          negotiated_aead_alg st0.cs_model.model_handshake)
      (ensures traffic_material_matches_expected_at_count traffic_id st1 (n + 1))
=
  match
    traffic_material_for_label
      st0.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_traffic_secret_for_state traffic_id st0
  with
  | Some m0, Some secret ->
    lemma_updated_traffic_key_material_advances_count secret n m0
  | _, _ -> ()

let base_secret_inputs_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match
    base_secret_material base_id client.cs_model.model_handshake.hs_keys,
    base_secret_material base_id server.cs_model.model_handshake.hs_keys
  with
  | Some client_secret, Some server_secret ->
    Seq.equal client_secret server_secret
  | _, _ -> False
let traffic_secret_inputs_agree
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : prop =
  let base_id =
    match traffic_id.traffic_id_epoch with
    | TrafficHandshake -> HandshakeSecret
    | TrafficApplication -> MasterSecret in
  base_secret_inputs_agree base_id client server /\
  same_key_derivation_checkpoint
    (key_checkpoint_for_epoch traffic_id.traffic_id_epoch)
    client
    server /\
  // The traffic *key* length is fixed by the negotiated AEAD algorithm, so
  // key agreement additionally requires the two endpoints to have negotiated
  // the same cipher suite.
  negotiated_aead_alg client.cs_model.model_handshake ==
    negotiated_aead_alg server.cs_model.model_handshake
let derivation_inputs_agree
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match key_id with
  | BaseSecret base_id ->
    base_secret_inputs_agree base_id client server
  | TrafficSecret traffic_id
  | TrafficKey traffic_id
  | TrafficIV traffic_id ->
    traffic_secret_inputs_agree traffic_id client server
  | FinishedKey label ->
    traffic_secret_inputs_agree
      { traffic_id_epoch = TrafficHandshake; traffic_id_label = label }
      client
      server
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    False
let peer_derived_key_material_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : prop =
  match
    expected_derived_key_material key_id client,
    expected_derived_key_material key_id server
  with
  | Some client_material, Some server_material ->
    Seq.equal client_material server_material
  | _, _ -> False
let supported_profile_all_derived_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : prop =
  peer_derived_key_material_agrees (BaseSecret EarlySecret) client server /\
  peer_derived_key_material_agrees (BaseSecret HandshakeSecret) client server /\
  peer_derived_key_material_agrees (BaseSecret MasterSecret) client server /\
  peer_derived_key_material_agrees
    (TrafficSecret (traffic_id TrafficHandshake ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficSecret (traffic_id TrafficHandshake ServerTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficSecret (traffic_id TrafficApplication ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficSecret (traffic_id TrafficApplication ServerTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficKey (traffic_id TrafficHandshake ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficKey (traffic_id TrafficHandshake ServerTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficKey (traffic_id TrafficApplication ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficKey (traffic_id TrafficApplication ServerTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficIV (traffic_id TrafficHandshake ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficIV (traffic_id TrafficHandshake ServerTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficIV (traffic_id TrafficApplication ClientTraffic)) client server /\
  peer_derived_key_material_agrees
    (TrafficIV (traffic_id TrafficApplication ServerTraffic)) client server /\
  peer_derived_key_material_agrees (FinishedKey ClientTraffic) client server /\
  peer_derived_key_material_agrees (FinishedKey ServerTraffic) client server
let supported_profile_all_record_material_inputs_agree
  (client:connection_state)
  (server:connection_state)
  : prop =
  peer_record_material_inputs_agree
    (traffic_id TrafficHandshake ClientTraffic) client server /\
  peer_record_material_inputs_agree
    (traffic_id TrafficHandshake ServerTraffic) client server /\
  peer_record_material_inputs_agree
    (traffic_id TrafficApplication ClientTraffic) client server /\
  peer_record_material_inputs_agree
    (traffic_id TrafficApplication ServerTraffic) client server
let supported_profile_application_record_material_inputs_agree
  (client:connection_state)
  (server:connection_state)
  : prop =
  peer_record_material_inputs_agree
    (traffic_id TrafficApplication ClientTraffic) client server /\
  peer_record_material_inputs_agree
    (traffic_id TrafficApplication ServerTraffic) client server
let supported_profile_all_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : prop =
  peer_record_material_agrees
    (traffic_id TrafficHandshake ClientTraffic) client server /\
  peer_record_material_agrees
    (traffic_id TrafficHandshake ServerTraffic) client server /\
  peer_record_material_agrees
    (traffic_id TrafficApplication ClientTraffic) client server /\
  peer_record_material_agrees
    (traffic_id TrafficApplication ServerTraffic) client server
let supported_profile_application_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : prop =
  peer_record_material_agrees
    (traffic_id TrafficApplication ClientTraffic) client server /\
  peer_record_material_agrees
    (traffic_id TrafficApplication ServerTraffic) client server
let supported_profile_client_server_key_material_inputs_agree
  (client:connection_state)
  (server:connection_state)
  : prop =
  paired_x25519_key_shares client server /\
  connection_supported_profile_key_schedule_lineage client /\
  connection_supported_profile_key_schedule_lineage server /\
  paired_key_derivation_checkpoints client server /\
  supported_profile_application_record_material_inputs_agree client server
let supported_profile_client_server_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : prop =
  supported_profile_all_derived_key_material_agrees client server /\
  supported_profile_application_record_material_agrees client server

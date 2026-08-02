module TLS13.ConnectionState.ServerHelloSelectionLink

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module T = TLS13.Types
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module Sem = TLS13.Wire.Semantics
module W = TLS13.Wire.Spec

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.ConnectionState.Lemmas

let server_hello_selection_link_shape (st:connection_state) : prop =
  st.cs_model.model_config.config_role == ServerEndpoint ==>
  (match st.cs_model.model_handshake.hs_server_hello,
         st.cs_model.model_handshake.hs_server_selection with
   | Some sh, Some sel -> server_hello_matches_selection sel sh
   | Some sh, None -> False
   | _, _ -> True)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"

let lemma_connection_delta_server_hello_selection_link
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_hello_selection_link_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_hello_selection_link_shape st1)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  if st0.cs_model.model_config.config_role = ServerEndpoint then begin
    let hs0 = st0.cs_model.model_handshake in
    match delta.delta_event with
    | ConnLocalEvent local ->
      assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
        step_local_event st0.cs_model local);
      assert (step_local_event st0.cs_model local == Some st1.cs_model);
      (match local, st0.cs_model.model_control with
       | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
         assert (legal_local_event st0.cs_model local);
         // legality forces hs_server_selection st0 == None
         assert (hs0.hs_server_selection == None);
         // the link shape then forces hs_server_hello st0 == None
         assert (hs0.hs_server_hello == None);
         assert (st1.cs_model.model_handshake.hs_server_hello == None);
         assert (server_hello_selection_link_shape st1)
       | LocalFail err, _ ->
         assert (st1.cs_model == fail_model st0.cs_model err);
         assert (st1.cs_model.model_handshake == hs0);
         assert (server_hello_selection_link_shape st1)
       | _, _ ->
         assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
         assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
         assert (server_hello_selection_link_shape st1))
    | ConnNetworkEvent msg ->
      assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
        step_tls_message
          st0.cs_model
          msg.CL.message_direction
          msg.CL.message_value);
      assert (step_tls_message
        st0.cs_model
        msg.CL.message_direction
        msg.CL.message_value == Some st1.cs_model);
      (match msg.CL.message_direction, msg.CL.message_value, st0.cs_model.model_control with
       | CL.Sent, M.TlsHandshake (M.ServerHello sh), ControlHandshaking HsClientHelloReceived ->
         assert (legal_tls_message
           st0.cs_model
           msg.CL.message_direction
           msg.CL.message_value);
         // legality: hs_server_selection st0 == Some selection /\ matches
         (match hs0.hs_server_selection with
          | Some selection ->
            assert (server_hello_matches_selection selection sh);
            assert (st1.cs_model.model_handshake.hs_server_hello == Some sh);
            assert (st1.cs_model.model_handshake.hs_server_selection == Some selection);
            assert (server_hello_selection_link_shape st1)
          | None -> assert False)
       | CL.Received, M.TlsHandshake (M.ServerHello sh), ControlHandshaking HsClientHelloSent ->
         // legal only for ClientEndpoint; contradicts role == Server
         assert (legal_tls_message
           st0.cs_model
           msg.CL.message_direction
           msg.CL.message_value);
         assert (st0.cs_model.model_config.config_role == ClientEndpoint);
         assert False
       | _, _, _ ->
         assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
         assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
         assert (server_hello_selection_link_shape st1))
  end
  else ()

#pop-options

let lemma_initial_server_hello_selection_link
  (cfg:connection_config)
  : Lemma
      (ensures server_hello_selection_link_shape (initial cfg))
=
  ()

(* A companion reachable shape: on the server, before the ServerHello is sent
   (controls ControlNew / HsAwaitingClientHello / HsClientHelloReceived) the
   field hs_server_hello is still None.  Used to exclude the HsClientHelloReceived
   control in lemma 2. *)
let server_hello_none_pre_send_shape (st:connection_state) : prop =
  st.cs_model.model_config.config_role == ServerEndpoint ==>
  (match st.cs_model.model_control with
   | ControlNew
   | ControlHandshaking HsAwaitingClientHello
   | ControlHandshaking HsClientHelloReceived ->
     st.cs_model.model_handshake.hs_server_hello == None
   | _ -> True)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"

let lemma_connection_delta_server_hello_none_pre_send
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_hello_none_pre_send_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_hello_none_pre_send_shape st1)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  if st0.cs_model.model_config.config_role = ServerEndpoint then begin
    let hs0 = st0.cs_model.model_handshake in
    match delta.delta_event with
    | ConnLocalEvent local ->
      assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
        step_local_event st0.cs_model local);
      assert (step_local_event st0.cs_model local == Some st1.cs_model);
      (match local, st0.cs_model.model_control with
       | LocalFail err, _ ->
         assert (st1.cs_model == fail_model st0.cs_model err);
         assert (server_hello_none_pre_send_shape st1)
       | _, _ ->
         assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
         assert (server_hello_none_pre_send_shape st1))
    | ConnNetworkEvent msg ->
      assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
        step_tls_message
          st0.cs_model
          msg.CL.message_direction
          msg.CL.message_value);
      assert (step_tls_message
        st0.cs_model
        msg.CL.message_direction
        msg.CL.message_value == Some st1.cs_model);
      (match msg.CL.message_direction, msg.CL.message_value, st0.cs_model.model_control with
       | CL.Sent, M.TlsHandshake (M.ServerHello sh), ControlHandshaking HsClientHelloReceived ->
         // moves to HsServerHelloSent (outside the pre-send set)
         assert (server_hello_none_pre_send_shape st1)
       | CL.Received, M.TlsHandshake (M.ServerHello sh), ControlHandshaking HsClientHelloSent ->
         assert (legal_tls_message
           st0.cs_model
           msg.CL.message_direction
           msg.CL.message_value);
         assert (st0.cs_model.model_config.config_role == ClientEndpoint);
         assert False
       | _, _, _ ->
         assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
         assert (server_hello_none_pre_send_shape st1))
  end
  else ()

#pop-options

let lemma_initial_server_hello_none_pre_send
  (cfg:connection_config)
  : Lemma
      (ensures server_hello_none_pre_send_shape (initial cfg))
=
  ()

let lemma_connection_state_single_step_server_hello_none_pre_send
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (server_hello_none_pre_send_shape y);
            (connection_state_single_step x y)}
          server_hello_none_pre_send_shape x /\
          connection_state_single_step x y ==>
          server_hello_none_pre_send_shape y)
=
  introduce forall x y.
    server_hello_none_pre_send_shape x /\
    connection_state_single_step x y ==>
    server_hello_none_pre_send_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_server_hello_none_pre_send x y

let lemma_consistent_server_hello_none_pre_send (st:connection_state)
  : Lemma (requires connection_state_consistent st)
          (ensures server_hello_none_pre_send_shape st)
=
  let p = server_hello_none_pre_send_shape in
  lemma_initial_server_hello_none_pre_send st.cs_model.model_config;
  lemma_connection_state_single_step_server_hello_none_pre_send ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_connection_state_single_step_server_hello_selection_link
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (server_hello_selection_link_shape y);
            (connection_state_single_step x y)}
          server_hello_selection_link_shape x /\
          connection_state_single_step x y ==>
          server_hello_selection_link_shape y)
=
  introduce forall x y.
    server_hello_selection_link_shape x /\
    connection_state_single_step x y ==>
    server_hello_selection_link_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_server_hello_selection_link x y

let lemma_consistent_server_hello_selection_link (st:connection_state)
  : Lemma (requires connection_state_consistent st)
          (ensures server_hello_selection_link_shape st)
=
  let p = server_hello_selection_link_shape in
  lemma_initial_server_hello_selection_link st.cs_model.model_config;
  lemma_connection_state_single_step_server_hello_selection_link ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)


(* ---------------------------------------------------------------------- *)
(* Local copy of the server x25519 reachable-shape invariant.             *)
(* The originals live in TLS13.ConnectionState.Lemmas.fst but are NOT     *)
(* exposed through its .fsti, so they are re-established here from the     *)
(* same single-step + stable_on_closure harness, reusing the EXPORTED     *)
(* helpers lemma_step_model_preserves_config,                             *)
(* lemma_step_model_from_failed_results_failed and                        *)
(* lemma_legal_connection_delta_stable_server_x25519_key_share_projection.*)
(* ---------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"

let server_selected_client_hello_reachable_shape
  (st:connection_state)
  : prop =
  let hs = st.cs_model.model_handshake in
  match hs.hs_server_selection with
  | Some selection ->
    hs.hs_client_hello == Some selection.server_selected_client_hello /\
    (match selection.server_key_share_private with
     | Some server_sk ->
       C.x25519_public_from_private server_sk ==
         selection.server_key_share_public
     | None ->
       True)
  | None ->
    True

let server_x25519_reachable_shape
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ServerEndpoint ==>
  (match st.cs_model.model_handshake.hs_keys.ks_shared_secret with
   | Some _ ->
     (match st.cs_model.model_control with
      | ControlHandshaking HsClientHelloReceived ->
        server_x25519_pre_server_hello_projection st
      | ControlFailed _ ->
        server_x25519_pre_server_hello_projection st \/
        server_x25519_key_share_projection st
      | _ ->
        stable_server_x25519_key_share_projection st)
   | None ->
     (match st.cs_model.model_control with
      | ControlNew
      | ControlHandshaking HsAwaitingClientHello ->
        st.cs_model.model_handshake.hs_server_selection == None
      | ControlHandshaking HsClientHelloReceived ->
        server_selected_client_hello_reachable_shape st
      | _ ->
        True))


let lemma_legal_local_event_server_x25519_reachable_shape
  (st0:connection_state)
  (local:local_event)
  (st1:connection_state)
  : Lemma
      (requires
        server_x25519_reachable_shape st0 /\
        st0.cs_model.model_config.config_role == ServerEndpoint /\
        st0.cs_model.model_handshake.hs_keys.ks_shared_secret == None /\
        legal_local_event st0.cs_model local /\
        step_local_event st0.cs_model local == Some st1.cs_model)
      (ensures server_x25519_reachable_shape st1)
=
  let hs0 = st0.cs_model.model_handshake in
  match local, st0.cs_model.model_control with
  | LocalStartServer, ControlNew ->
    assert (st1.cs_model.model_handshake.hs_server_selection == None);
    assert (server_x25519_reachable_shape st1)
  | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
    assert (hs0.hs_keys.ks_shared_secret == None);
    assert (hs0.hs_client_hello == Some selection.server_selected_client_hello);
    (match selection.server_key_share_private with
     | Some server_sk ->
       assert (C.x25519_public_from_private server_sk ==
         selection.server_key_share_public)
     | None ->
       ());
    assert (server_x25519_reachable_shape st1)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
    assert (server_selected_client_hello_reachable_shape st0);
    (match hs0.hs_server_selection with
     | Some selection ->
       (match selection.server_key_share_private with
        | Some server_sk ->
          assert (hs0.hs_client_hello ==
            Some selection.server_selected_client_hello);
          assert (C.x25519_public_from_private server_sk ==
            selection.server_key_share_public);
          (match client_hello_key_share selection.server_selected_client_hello with
           | Some ch_ks ->
             assert (C.x25519_shared server_sk ch_ks == Some shared)
           | None -> assert False)
        | None ->
          assert False)
     | None ->
       assert False);
    assert (server_x25519_reachable_shape st1)
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalSignCertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalVerifyClientFinished fin, ControlHandshaking HsClientFinishedReceived ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake == hs0);
    assert (server_x25519_reachable_shape st1)
  | LocalFail err, _ ->
    assert (st1.cs_model == fail_model st0.cs_model err);
    assert (server_x25519_reachable_shape st1)
  | _, _ ->
    assert False

let lemma_connection_delta_server_x25519_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_x25519_reachable_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_x25519_reachable_shape st1)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config
    st0.cs_model
    delta.delta_event
    st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  if st0.cs_model.model_config.config_role == ServerEndpoint then
    match st0.cs_model.model_handshake.hs_keys.ks_shared_secret with
    | Some _ ->
      (match st0.cs_model.model_control with
       | ControlHandshaking HsClientHelloReceived ->
         (match delta.delta_event with
          | ConnNetworkEvent msg ->
            assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
              step_tls_message
                st0.cs_model
                msg.CL.message_direction
                msg.CL.message_value);
            assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
            (match msg.CL.message_direction, msg.CL.message_value with
             | CL.Sent, M.TlsHandshake (M.ServerHello sh) ->
               assert (server_x25519_pre_server_hello_projection st0);
               assert (legal_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value);
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               (match
                 st0.cs_model.model_handshake.hs_server_selection,
                 st0.cs_model.model_handshake.hs_client_hello,
                 st0.cs_model.model_handshake.hs_keys.ks_shared_secret
               with
               | Some selection, Some ch, Some shared ->
                 (match selection.server_key_share_private with
                  | Some server_sk ->
                    assert (server_hello_key_share sh ==
                      Some selection.server_key_share_public);
                    assert (C.x25519_public_from_private server_sk ==
                      selection.server_key_share_public);
                    (match client_hello_key_share ch with
                     | Some ch_ks ->
                       assert (C.x25519_shared server_sk ch_ks == Some shared)
                     | None -> assert False)
                  | None ->
                    assert False)
               | _, _, _ ->
                 assert False);
               assert (stable_server_x25519_key_share_projection st1);
               assert (server_x25519_reachable_shape st1)
             | _, _ ->
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               assert (server_x25519_reachable_shape st1))
          | ConnLocalEvent local ->
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (server_x25519_reachable_shape st1))
       | ControlFailed _ ->
         lemma_step_model_from_failed_results_failed
           st0.cs_model
           delta.delta_event
           st1.cs_model;
        // A step from a failed state lands in `fail_model`, which preserves the
        // handshake state; hence the server x25519 key-share projections (which
        // depend only on the handshake state) are transported from st0 to st1.
        (match delta.delta_event with
         | ConnLocalEvent local ->
           (match local with
            | LocalFail err ->
              assert (st1.cs_model == fail_model st0.cs_model err)
            | _ -> assert False)
         | ConnNetworkEvent msg ->
           (match msg.CL.message_value with
            | M.TlsAlert alert ->
              assert (st1.cs_model == fail_model st0.cs_model (T.AlertError alert))
            | _ -> assert False));
        assert (st1.cs_model.model_handshake == st0.cs_model.model_handshake);
        assert (server_x25519_reachable_shape st1)
       | _ ->
         lemma_legal_connection_delta_stable_server_x25519_key_share_projection
           st0
           delta
           st1;
         assert (server_x25519_reachable_shape st1))
    | None ->
      (match delta.delta_event with
       | ConnLocalEvent local ->
         assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
           step_local_event st0.cs_model local);
         assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
         (match local, st0.cs_model.model_control with
          | LocalStartServer, ControlNew ->
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (server_x25519_reachable_shape st1)
          | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (st0.cs_model.model_handshake.hs_keys.ks_shared_secret == None);
            assert (server_x25519_reachable_shape st1)
          | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
            assert (server_selected_client_hello_reachable_shape st0);
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            (match st0.cs_model.model_handshake.hs_server_selection with
            | Some selection ->
              (match selection.server_key_share_private with
               | Some server_sk ->
                 assert (st0.cs_model.model_handshake.hs_client_hello ==
                   Some selection.server_selected_client_hello);
                 assert (C.x25519_public_from_private server_sk ==
                   selection.server_key_share_public);
                 (match client_hello_key_share selection.server_selected_client_hello with
                  | Some ch_ks ->
                    assert (C.x25519_shared server_sk ch_ks == Some shared)
                  | None -> assert False)
               | None ->
                 assert False)
            | None ->
              assert False);
            assert (server_x25519_reachable_shape st1)
          | _, _ ->
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            lemma_legal_local_event_server_x25519_reachable_shape st0 local st1)
       | ConnNetworkEvent msg ->
         assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
           step_tls_message
             st0.cs_model
             msg.CL.message_direction
             msg.CL.message_value);
         assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
         (match msg.CL.message_direction, msg.CL.message_value, st0.cs_model.model_control with
          | CL.Received, M.TlsHandshake (M.ClientHello _), ControlHandshaking HsAwaitingClientHello ->
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st0.cs_model.model_handshake.hs_server_selection == None);
            assert (server_x25519_reachable_shape st1)
          | _, M.TlsChangeCipherSpec, ControlHandshaking _ ->
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st1.cs_model == st0.cs_model);
            assert (server_x25519_reachable_shape st1)
          | _, _, _ ->
            (match msg.CL.message_value, msg.CL.message_direction, st0.cs_model.model_control with
             | M.TlsHandshake (M.ClientHello _), CL.Sent, ControlHandshaking HsStarted
             | M.TlsHandshake (M.ClientHello _), CL.Received, ControlHandshaking HsAwaitingClientHello
             | M.TlsHandshake (M.ServerHello _), CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsHandshake (M.ServerHello _), CL.Sent, ControlHandshaking HsClientHelloReceived
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent, ControlHandshaking HsServerHelloSent
             | M.TlsHandshake (M.Certificate _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.CertificateVerify _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Received, ControlHandshaking HsServerHelloReceived
             | M.TlsHandshake (M.Certificate _), CL.Received, ControlHandshaking HsEncryptedExtensionsReceived
             | M.TlsHandshake (M.CertificateVerify _), CL.Received, ControlHandshaking HsCertificateValidated
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsCertificateVerifyVerified
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsServerFinishedSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerFinishedVerified
             | M.TlsHandshake M.HelloRetryRequest, CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsApplicationData _, _, ControlApplicationData
             | M.TlsIgnoredPostHandshake _, CL.Received, ControlApplicationData
             | M.TlsKeyUpdate _, CL.Received, ControlApplicationData
             | M.TlsKeyUpdate M.UpdateNotRequested, CL.Sent, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Sent, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlClosing
             | M.TlsAlert _, _, _
             | M.TlsChangeCipherSpec, _, ControlHandshaking _ ->
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               assert (server_x25519_reachable_shape st1)
             | _, _, _ ->
               assert False)))


let lemma_initial_server_x25519_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures server_x25519_reachable_shape (initial cfg))
=
  ()

let lemma_connection_state_single_step_server_x25519_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (server_x25519_reachable_shape y);
            (connection_state_single_step x y)}
          server_x25519_reachable_shape x /\
          connection_state_single_step x y ==>
          server_x25519_reachable_shape y)
=
  introduce forall x y.
    server_x25519_reachable_shape x /\
    connection_state_single_step x y ==>
    server_x25519_reachable_shape y
  with
    introduce _ ==> _ with _.
    lemma_connection_delta_server_x25519_reachable_shape x y

let lemma_connection_state_consistent_server_x25519_reachable_shape
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures server_x25519_reachable_shape st)
=
  let p = server_x25519_reachable_shape in
  lemma_initial_server_x25519_reachable_shape st.cs_model.model_config;
  lemma_connection_state_single_step_server_x25519_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40 --split_queries always"

let lemma_server_x25519_key_share_projection_of_hello_present (server:connection_state)
  : Lemma
      (requires
        connection_state_consistent server /\
        server.cs_model.model_config.config_role == ServerEndpoint /\
        Some? server.cs_model.model_handshake.hs_server_hello /\
        Some? server.cs_model.model_handshake.hs_server_selection /\
        Some? server.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures server_x25519_key_share_projection server)
=
  lemma_connection_state_consistent_server_x25519_reachable_shape server;
  lemma_consistent_server_hello_selection_link server;
  lemma_consistent_server_hello_none_pre_send server;
  let hs = server.cs_model.model_handshake in
  assert (server_x25519_reachable_shape server);
  match server.cs_model.model_control with
  | ControlHandshaking HsClientHelloReceived ->
    // shape2 forces hs_server_hello == None, contradicting Some?
    assert (server_hello_none_pre_send_shape server);
    assert (hs.hs_server_hello == None);
    assert False
  | ControlFailed _ ->
    assert (server_x25519_pre_server_hello_projection server \/
            server_x25519_key_share_projection server);
    eliminate
      server_x25519_pre_server_hello_projection server \/
      server_x25519_key_share_projection server
    returns server_x25519_key_share_projection server
    with _hpre. begin
      (match
         hs.hs_server_selection, hs.hs_client_hello,
         hs.hs_server_hello, hs.hs_keys.ks_shared_secret
       with
       | Some selection, Some ch, Some sh, Some shared ->
         (match selection.server_key_share_private with
          | Some server_sk ->
            // from the link shape (hello Some, selection Some)
            assert (server_hello_matches_selection selection sh);
            assert (server_hello_key_share sh ==
              Some selection.server_key_share_public);
            // from the pre-projection
            (match client_hello_key_share ch with
             | Some ch_ks ->
               assert (C.x25519_public_from_private server_sk ==
                 selection.server_key_share_public);
               assert (C.x25519_shared server_sk ch_ks == Some shared)
             | None -> assert False)
          | None -> assert False)
       | _, _, _, _ -> assert False);
      assert (server_x25519_key_share_projection server)
      end
    and _hfull. ()
  | _ ->
    assert (stable_server_x25519_key_share_projection server);
    assert (server_x25519_key_share_projection server)

#pop-options

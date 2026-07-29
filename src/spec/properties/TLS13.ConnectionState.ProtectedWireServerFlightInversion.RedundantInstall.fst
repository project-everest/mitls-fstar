module TLS13.ConnectionState.ProtectedWireServerFlightInversion.RedundantInstall

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module R = TLS13.Record.Spec
module SMReplay = TLS13.Spec.StateMachine.Replay
module SMCan = TLS13.Spec.StateMachine.Canonical
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module Seq = FStar.Seq

(* ------------------------------------------------------------------ *)
(* Model-neutrality + legality.                                        *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_redundant_server_hs_write_install_identity m material =
  (* step_model on a ConnLocalEvent (install) at ControlHandshaking _ rebuilds
     the model, updating only [model_record] and [model_handshake.hs_keys];
     both are rewritten to the values they already hold, since [R.install_keys]
     is a constant of (epoch, key, iv) and the key-schedule field already holds
     [Some material]. *)
  assert (CS.step_model m (server_hs_write_install_event material) == Some m);
  assert (CS.legal_event m (server_hs_write_install_event material))
#pop-options

#push-options "--fuel 1 --ifuel 2 --z3rlimit 30"
let lemma_redundant_client_hs_read_install_identity m material =
  assert (CS.step_model m (client_hs_read_install_event material) == Some m);
  assert (CS.legal_event m (client_hs_read_install_event material))
#pop-options

(* ------------------------------------------------------------------ *)
(* Byte-neutral prepend.                                              *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_server_hs_write_install_sent m material rest rs rr final =
  lemma_redundant_server_hs_write_install_identity m material;
  let ev = server_hs_write_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (SMCan.sent_event_nonempty_seal_projection m ev B.empty);
  PWReplay.lemma_conn_events_sent_seal_replay_cons
    m ev rest rs rr final
    m B.empty B.empty rs rr
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let lemma_prepend_redundant_client_hs_read_install_received m material rest rs rr final =
  lemma_redundant_client_hs_read_install_identity m material;
  let ev = client_hs_read_install_event material in
  Seq.append_empty_l rs;
  Seq.append_empty_l rr;
  assert (CS.event_raw_delta_legal m ev B.empty B.empty);
  assert (SMCan.received_event_nonempty_decode_projection m ev B.empty);
  PWReplay.lemma_conn_events_received_decode_replay_cons
    m ev rest rs rr final
    m B.empty B.empty rs rr
#pop-options

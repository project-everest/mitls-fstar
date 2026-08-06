module TLS13.ConnectionState.RecordKeyEpoch

module CS  = TLS13.Spec.StateMachine
module R   = TLS13.Record.Spec
module CL  = TLS13.ConnectionLog
module M   = TLS13.Messages
module SMR = TLS13.Spec.StateMachine.Reachability
module RTC = FStar.ReflexiveTransitiveClosure
module ID  = FStar.IndefiniteDescription

(* ------------------------------------------------------------------ *)
(* The step-stable shape: a present key forces a non-Initial epoch.    *)
(* ------------------------------------------------------------------ *)

let dir_shape (st:R.direction_state) : prop =
  Some? st.R.key ==> ~(R.Initial? st.R.epoch)

let model_shape (m:CS.connection_model) : prop =
  dir_shape m.CS.model_record.CS.record_read /\
  dir_shape m.CS.model_record.CS.record_write

let conn_shape (st:CS.connection_state) : prop = model_shape st.CS.cs_model

(* ------------------------------------------------------------------ *)
(* Field-preservation helpers, exposed as SMT-pattern quantifiers.     *)
(* [next_seq]/[advance_direction_records] preserve (epoch,key);         *)
(* [install_keys] with a non-Initial epoch establishes the shape;       *)
(* [traffic_record_epoch] never yields [Initial].                       *)
(* ------------------------------------------------------------------ *)

let rec lemma_advance (st:R.direction_state) (n:nat)
  : Lemma (ensures dir_shape st ==> dir_shape (CS.advance_direction_records st n))
          (decreases n)
  = if n > 0 then lemma_advance st (n-1)

let helpers () : Lemma (ensures
  (forall (st:R.direction_state). {:pattern (R.next_seq st)}
     dir_shape st ==> dir_shape (R.next_seq st)) /\
  (forall (st:R.direction_state) (n:nat). {:pattern (CS.advance_direction_records st n)}
     dir_shape st ==> dir_shape (CS.advance_direction_records st n)) /\
  (forall (st:R.direction_state) (ep:R.epoch) (k iv:TLS13.Bytes.bytes).
     {:pattern (R.install_keys st ep k iv)}
     ~(R.Initial? ep) ==> dir_shape (R.install_keys st ep k iv)) /\
  (forall (te:CS.traffic_epoch). {:pattern (CS.traffic_record_epoch te)}
     ~(R.Initial? (CS.traffic_record_epoch te))))
  =
  introduce forall (st:R.direction_state) (n:nat).
     dir_shape st ==> dir_shape (CS.advance_direction_records st n)
  with lemma_advance st n

(* ------------------------------------------------------------------ *)
(* Per-step preservation.  Every [step_model] arm leaves each record    *)
(* direction preserved / [next_seq]'d / [advance]'d / [install_keys]'d   *)
(* (never with an [Initial] epoch); the pattern helpers discharge each.  *)
(* ------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 3 --z3rlimit 150 --split_queries always"
let lemma_step_model_shape
  (model:CS.connection_model) (ev:CS.conn_event) (model':CS.connection_model)
  : Lemma (requires model_shape model /\ CS.step_model model ev == Some model')
          (ensures model_shape model')
=
  helpers ();
  match ev with
  | CS.ConnNetworkEvent msg -> ()
  | CS.ConnProtectedHandshake step ->
    (* A protected-handshake step is a RECEIVED handshake message step.  The
       `step_handshake_message` result already satisfies `model_shape` by the
       same enumeration that discharges the `ConnNetworkEvent` arm (the
       pattern helpers cover `next_seq` / `advance_direction_records` /
       `install_keys`).  The extra post-processing can only IMPROVE matters:
       `record_adjusted` either keeps the stepped record state or restores
       `record_read` from the PRE-state `model` (which satisfies `dir_shape`
       by hypothesis), and `set_pending_protected_handshake` touches only
       `model_handshake.hs_buffers`. *)
    ()
  | CS.ConnLocalEvent local -> ()
#pop-options

(* ------------------------------------------------------------------ *)
(* Closure over the reachability relation.                             *)
(* ------------------------------------------------------------------ *)

let lemma_delta_shape (st0 st1:CS.connection_state)
  : Lemma (requires conn_shape st0 /\ SMR.connection_state_single_step st0 st1)
          (ensures conn_shape st1)
=
  let delta_w = ID.indefinite_description_ghost CS.connection_delta
    (fun delta -> CS.legal_connection_delta st0 delta st1) in
  let delta : CS.connection_delta = delta_w in
  assert (CS.legal_connection_delta st0 delta st1);
  assert (CS.step_model st0.CS.cs_model delta.CS.delta_event == Some st1.CS.cs_model);
  lemma_step_model_shape st0.CS.cs_model delta.CS.delta_event st1.CS.cs_model

let lemma_single_step_shape (_:unit)
  : Lemma (ensures forall (x y:CS.connection_state).
      {:pattern (conn_shape y); (SMR.connection_state_single_step x y)}
      conn_shape x /\ SMR.connection_state_single_step x y ==> conn_shape y)
=
  introduce forall (x y:CS.connection_state).
    conn_shape x /\ SMR.connection_state_single_step x y ==> conn_shape y
  with introduce _ ==> _ with _. lemma_delta_shape x y

let lemma_initial_shape (cfg:CS.connection_config)
  : Lemma (ensures conn_shape (CS.initial cfg))
= ()

let lemma_reachable_shape (st:CS.connection_state)
  : Lemma (requires SMR.connection_state_consistent st)
          (ensures conn_shape st)
=
  lemma_initial_shape st.CS.cs_model.CS.model_config;
  lemma_single_step_shape ();
  let p = conn_shape in
  let stable : squash (forall (x y:CS.connection_state).
      {:pattern (p y); (SMR.connection_state_single_step x y)}
      p x /\ SMR.connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure SMR.connection_state_single_step p stable;
  assert (SMR.connection_state_evolves (CS.initial st.CS.cs_model.CS.model_config) st);
  assert (p st)

(* ------------------------------------------------------------------ *)
(* Exported consumers.                                                 *)
(* ------------------------------------------------------------------ *)

let lemma_connection_consistent_read_key_present_not_initial
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        Some? st.CS.cs_model.CS.model_record.CS.record_read.R.key)
      (ensures
        ~(R.Initial? st.CS.cs_model.CS.model_record.CS.record_read.R.epoch))
= lemma_reachable_shape st

let lemma_connection_consistent_write_key_present_not_initial
  (st:CS.connection_state)
  : Lemma
      (requires
        SMR.connection_state_consistent st /\
        Some? st.CS.cs_model.CS.model_record.CS.record_write.R.key)
      (ensures
        ~(R.Initial? st.CS.cs_model.CS.model_record.CS.record_write.R.epoch))
= lemma_reachable_shape st

module TLS13.Impl.Client.DrainProgress

module CP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.StateMachine
module CTypes = TLS13.Impl.CanonicalTypes
module D = TLS13.Impl.Client.Drain
module ID = FStar.IndefiniteDescription
module RTC = FStar.ReflexiveTransitiveClosure

open TLS13.Spec.Endpoint.Client

(**
  Draining makes canonical progress.

  The buffered driver stores its connection behind a monotonic ghost reference
  ordered by [client_progress_preorder], so it can only advance the state along
  that preorder.  A drain step qualifies: by decision S1 the internal event is
  an ordinary local event, so [CP.lemma_internal_step_is_client_step] turns the
  step into a [client_step] at [CP.client_internal_event], which is exactly a
  [client_canonical_step_rel] edge.  The preorder is then the reflexive
  transitive closure of that relation, so a whole chain lifts by induction.
**)

let lemma_drain_step_canonical (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drain_step st0 st1)
      (ensures client_canonical_step_rel #CTypes.client_local_event st0 st1)
=
  let w = D.drain_step_witness st0 st1 in
  CP.lemma_internal_step_is_client_step st0 st1 (fst w) (snd w)

#push-options "--fuel 2 --ifuel 2"
let rec lemma_drain_chain_progress (n:nat) (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drain_chain n st0 st1)
      (ensures client_progress_preorder #CTypes.client_local_event st0 st1)
      (decreases n)
=
  if n = 0
  then ()
  else
  let m : nat = n - 1 in
    eliminate
      (st1 == st0) \/
      (exists st'. D.drain_step st0 st' /\ D.drain_chain m st' st1)
    with ()
    and
      (let st' =
         ID.indefinite_description_ghost
           CS.connection_state
           (fun st' -> D.drain_step st0 st' /\ D.drain_chain m st' st1) in
       lemma_drain_step_canonical st0 st';
       RTC.closure_step
         (client_canonical_step_rel #CTypes.client_local_event)
         st0
         st';
       lemma_drain_chain_progress m st' st1)
#pop-options

let lemma_drained_progress (st0 st1:CS.connection_state)
  : Lemma
      (requires D.drained st0 st1)
      (ensures client_progress_preorder #CTypes.client_local_event st0 st1)
=
  let n =
    ID.indefinite_description_ghost nat (fun n -> D.drain_chain n st0 st1) in
  lemma_drain_chain_progress n st0 st1

/// The drain loop's local notion of "internal work pending" is the canonical
/// one; both are the same inequality on the pending protected-handshake
/// buffer.  Stated so that a driver holding [D.internal_pending] can feed the
/// scheduling obligations phrased over [CP.client_internal_pending].
let lemma_internal_pending_agrees (st:CS.connection_state)
  : Lemma (D.internal_pending st <==> CP.client_internal_pending st)
= ()

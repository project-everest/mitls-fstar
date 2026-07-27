module DH.Sample.StateMachine

(**
  DH.Sample.StateMachine — the semantic transition relation of the DH sample,
  one state machine per role, composed with the wire format into
  `Common.WireFormatStateMachine.wire_format_state_machine`.

  The informal protocol (ISO-DH, three messages) is:

      A -> B :  A, g^x
      B -> A :  B, g^y, Sign_B(A, g^x, g^y)
      A -> B :  Sign_A(B, g^x, g^y)

  with completion:
      * the INITIATOR (A) completes after receiving and verifying message 2
        (learning g^y, deriving the key, and emitting message 3);
      * the RESPONDER (B) completes after receiving and verifying message 3.

  Each endpoint is a `Common.StateMachine.state_machine` whose `sm_step`
  relation is given below.  Steps are driven by:
      * a LOCAL event `StartInitiator x` that kicks off the initiator with a
        freshly generated scalar x (key generation modelled as external input);
      * WIRE events carrying the parsed `DH.Sample.Wire.dh_message`s.

  Cryptographic reasoning is entirely delegated to the abstract, trusted
  `DH.Sample.Crypto` interface — signature checks are the `verify` predicate and
  key agreement is `dh_agree`.  The interface exposes correctness laws but no
  concrete or invertible crypto construction.  There is NO dependence on any
  Dolev–Yao/DY* machinery.

  Apart from the responder's intentionally nondeterministic choice of a fresh
  scalar, every relation clause pins down the next state and produced outputs.
  The fresh scalar is "reflected" out of the next state; see the Msg1 clause.
*)

module SM   = Common.StateMachine
module WF   = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
open DH.Sample.Types
open DH.Sample.Crypto
open DH.Sample.Wire

(** Convenient abbreviations for the event / output instantiations. *)
type dh_event  = SM.event dh_message local_event
type dh_output = SM.step_output dh_message local_output

(** ── Initiator transition relation ─────────────────────────────────────── *)

(**
  The initiator's step relation.

    * `LocalEvent (StartInitiator x)` from `Init_Start`:  generate g^x, remember
      the scalar and share, emit message 1 `Msg1 A g^x`, advance to `Init_Wait2`.

    * `WireEvent (Msg2 B g^y Sign_B)` from `Init_Wait2`:  the responder identity
      must match the intended peer; the signature `Sign_B` over the transcript
      (A, g^x, g^y) must verify; the initiator then derives the session key
      `dh_agree x g^y`, emits message 3 `Sign_A(B, g^x, g^y)`, reports
      `SessionEstablished`, and advances to `Init_Done`.

  All other (event, state) combinations have no transition (`False`).
*)
let initiator_step
  (st0:endpoint_state)
  (ev:dh_event)
  (st1:endpoint_state)
  (out:dh_output)
  : GTot prop =
  match ev with
  | SM.LocalEvent (StartInitiator x) ->
    st0.ep_role == Initiator /\ st0.ep_phase == Init_Start /\
    (match st0.ep_peer with
     | None -> False
     | Some _peer ->
       let gx = dh_exp x in
       st1 == { st0 with ep_phase = Init_Wait2;
                         ep_scalar = Some x; ep_my_share = Some gx } /\
       out.SM.so_wire_outputs == [ Msg1 st0.ep_me gx ] /\
       out.SM.so_local_outputs == [])
  | SM.WireEvent (Msg2 b gy sigB) ->
    st0.ep_role == Initiator /\ st0.ep_phase == Init_Wait2 /\
    (match st0.ep_peer, st0.ep_scalar, st0.ep_my_share with
     | Some peer, Some x, Some gx ->
       b == peer /\
       verify b (transcript st0.ep_me gx gy) sigB /\
       (let key = dh_agree x gy in
        let sigA = sign st0.ep_me (transcript b gx gy) in
        st1 == { st0 with ep_phase = Init_Done;
                          ep_peer_share = Some gy; ep_key = Some key } /\
        out.SM.so_wire_outputs == [ Msg3 sigA ] /\
        out.SM.so_local_outputs == [ SessionEstablished b key ])
     | _ -> False)
  | _ -> False

(** ── Responder transition relation ─────────────────────────────────────── *)

(**
  The responder's step relation.

    * `WireEvent (Msg1 A g^x)` from `Resp_Start`:  the responder generates a
      fresh scalar y — reflected as `st1.ep_scalar = Some y`, so the relation
      admits ANY choice of y — computes g^y, learns the peer A and its share
      g^x, derives the key `dh_agree y g^x`, emits message 2
      `Msg2 B g^y Sign_B(A, g^x, g^y)`, and advances to `Resp_Wait3`.

    * `WireEvent (Msg3 Sign_A)` from `Resp_Wait3`:  the signature `Sign_A` over
      the transcript (B, g^x, g^y) must verify; the responder then reports
      `SessionEstablished` and advances to `Resp_Done`.

  All other (event, state) combinations have no transition (`False`).
*)
let responder_step
  (st0:endpoint_state)
  (ev:dh_event)
  (st1:endpoint_state)
  (out:dh_output)
  : GTot prop =
  match ev with
  | SM.WireEvent (Msg1 a gx) ->
    st0.ep_role == Responder /\ st0.ep_phase == Resp_Start /\
    (match st1.ep_scalar with
     | None -> False
     | Some y ->
       let gy = dh_exp y in
       let me = st0.ep_me in
       let key = dh_agree y gx in
       let sigB = sign me (transcript a gx gy) in
       st1 == { st0 with ep_phase = Resp_Wait3; ep_peer = Some a;
                         ep_scalar = Some y; ep_my_share = Some gy;
                         ep_peer_share = Some gx; ep_key = Some key } /\
       out.SM.so_wire_outputs == [ Msg2 me gy sigB ] /\
       out.SM.so_local_outputs == [])
  | SM.WireEvent (Msg3 sigA) ->
    st0.ep_role == Responder /\ st0.ep_phase == Resp_Wait3 /\
    (match st0.ep_peer, st0.ep_my_share, st0.ep_peer_share, st0.ep_key with
     | Some a, Some gy, Some gx, Some key ->
       verify a (transcript st0.ep_me gx gy) sigA /\
       st1 == { st0 with ep_phase = Resp_Done } /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == [ SessionEstablished a key ]
     | _ -> False)
  | _ -> False

(** ── State-machine and wire-format-state-machine instances ──────────────── *)

(**
  The initiator endpoint as a `Common.StateMachine.state_machine`, parameterized
  by its own identity [me] and the intended peer [peer].
*)
noextract
let initiator_state_machine (me peer:principal)
  : SM.state_machine endpoint_state dh_message local_event local_output = {
  SM.sm_initial_state = initial_initiator me peer;
  SM.sm_step          = initiator_step;
}

(**
  The responder endpoint as a `Common.StateMachine.state_machine`, parameterized
  by its own identity [me].
*)
noextract
let responder_state_machine (me:principal)
  : SM.state_machine endpoint_state dh_message local_event local_output = {
  SM.sm_initial_state = initial_responder me;
  SM.sm_step          = responder_step;
}

(**
  Composition (requirement #4): the initiator endpoint as a full
  `Common.WireFormatStateMachine.wire_format_state_machine`, pairing the
  transition system with the DH wire format.
*)
noextract
let initiator_system (me peer:principal)
  : WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output = {
  WFSM.wfsm_state_machine = initiator_state_machine me peer;
  WFSM.wfsm_wire_format   = dh_wire_format;
}

(** Composition: the responder endpoint as a `wire_format_state_machine`. *)
noextract
let responder_system (me:principal)
  : WFSM.wire_format_state_machine endpoint_state dh_message local_event local_output = {
  WFSM.wfsm_state_machine = responder_state_machine me;
  WFSM.wfsm_wire_format   = dh_wire_format;
}

(** ── Adequacy / satisfiability theorems ────────────────────────────────── *)

(*
  These small theorems demonstrate that the transition relations are not
  vacuously false and that the protocol's core security-relevant equations hold
  end-to-end: an honest run's signatures verify, and both endpoints derive the
  SAME session key.  They connect the state machine to the abstract crypto
  interface.
*)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(** The initial states are valid (reachable) states of their machines. *)
let lemma_initiator_initial_valid (me peer:principal)
  : Lemma (ensures SM.valid_state (initiator_state_machine me peer)
                     (initiator_state_machine me peer).SM.sm_initial_state)
= SM.lemma_initial_state_valid (initiator_state_machine me peer)

let lemma_responder_initial_valid (me:principal)
  : Lemma (ensures SM.valid_state (responder_state_machine me)
                     (responder_state_machine me).SM.sm_initial_state)
= SM.lemma_initial_state_valid (responder_state_machine me)

(**
  The initiator's start transition is realizable: from the fresh initiator
  state there really is a step producing message 1.
*)
let lemma_initiator_start_step (me peer:principal) (x:dh_scalar)
  : Lemma
      (ensures
        (let st0 = initial_initiator me peer in
         let gx  = dh_exp x in
         let st1 = { st0 with ep_phase = Init_Wait2;
                              ep_scalar = Some x; ep_my_share = Some gx } in
         let out : dh_output = { SM.so_wire_outputs = [ Msg1 me gx ];
                                 SM.so_local_outputs = [] } in
         initiator_step st0 (SM.LocalEvent (StartInitiator x)) st1 out))
= ()

(**
  The responder's message-1 transition is realizable for any freshly chosen
  scalar y: it produces message 2 with an honestly generated signature.
*)
let lemma_responder_msg1_step (me a:principal) (gx:dh_share) (y:dh_scalar)
  : Lemma
      (ensures
        (let st0  = initial_responder me in
         let gy   = dh_exp y in
         let key  = dh_agree y gx in
         let sigB = sign me (transcript a gx gy) in
         let st1  = { st0 with ep_phase = Resp_Wait3; ep_peer = Some a;
                               ep_scalar = Some y; ep_my_share = Some gy;
                               ep_peer_share = Some gx; ep_key = Some key } in
         let out : dh_output = { SM.so_wire_outputs = [ Msg2 me gy sigB ];
                                 SM.so_local_outputs = [] } in
         responder_step st0 (SM.WireEvent (Msg1 a gx)) st1 out))
= ()

(**
  End-to-end adequacy of an HONEST run with initiator A=[a], responder B=[b],
  and ephemeral scalars x, y:

    1. the responder's signature Sign_B(A, g^x, g^y) is accepted by the
       initiator's `verify` check;
    2. the initiator's signature Sign_A(B, g^x, g^y) is accepted by the
       responder's `verify` check;
    3. both endpoints derive the SAME session key (DH agreement).

  This is the specification-level correctness statement tying the wire messages,
  the signature-checking predicate, and the DH agreement equation together.
*)
let lemma_honest_run (a b:principal) (x y:dh_scalar)
  : Lemma
      (ensures
        (let gx = dh_exp x in
         let gy = dh_exp y in
         verify b (transcript a gx gy) (sign b (transcript a gx gy)) /\
         verify a (transcript b gx gy) (sign a (transcript b gx gy)) /\
         dh_agree x gy == dh_agree y gx))
=
  let gx = dh_exp x in
  let gy = dh_exp y in
  lemma_sign_verify b (transcript a gx gy);
  lemma_sign_verify a (transcript b gx gy);
  lemma_dh_agree x y

#pop-options

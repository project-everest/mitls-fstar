module DH.Sample.System

(**
  The DY-free composed system for the fixed two-party DH sample.

  The state contains both unchanged local role machines, an explicit network,
  and an explicit IDEAL RNG boundary.  `ActRng owner x` is an honest/internal
  draw (the scalar argument is a semantic frame value, not a network input).
  It records `x` in the private, monotonically growing generation registry and reserves it
  for `owner`.  `ActStart` and the responder's first delivery may consume only a
  reserved draw.  Thus a scalar used by either local machine has honest RNG
  provenance, and a legal run cannot reuse a concrete scalar.

  The only attacker actions are routing/replay (`ActDeliver`) and public-message
  injection (`ActInject`).  No action reveals an RNG draw as a wire message.
  The symbolic product maps each `ActRng`—rather than a later protocol step—to a
  secret-labelled DY `RandGen`.

  ── Active attacker.  Msg1 delivery is DELIBERATELY unrestricted: the attacker
  may inject a Msg1 (`ActInject`) and route it to the responder, driving it from
  `Resp_Start` to `Resp_Wait3` and eliciting an honest Msg2 over the
  attacker-chosen share.  No secrecy or honest-peer agreement is claimed for that
  attacker-selected intermediate responder key; the model is candid that the
  responder can be started (and DoS'd) by the network, and only a genuine peer
  signature + a matching run link yield completion (see below).

  ── Run/session link.  Two auditable identifiers thread through the state:
  `sys_init_msg1_idx` records the network index of the initiator's own Msg1
  packet (fixed at `ActStart`), and `sys_resp_msg1_idx` records the index of the
  Msg1 the responder actually consumed (fixed at its Msg1 delivery).  A completion
  delivery is admitted only when these two indices coincide — i.e. the two
  flights are provably part of the SAME run.  Because the network is append-only
  and packets are immutable, that index equality makes the initiator's exact
  honest Msg1 packet (`Sent Init`) the one the responder consumed; the concrete
  identity/share agreement of a completed session is DERIVED from that link and
  from the local transition semantics — it is never restated by the guard.

  ── Dynamic compromise.  `ActCorrupt who` is a REAL attacker action: it sets the
  persistent per-role compromise flag `sys_init_corrupt` / `sys_resp_corrupt`
  (monotone: once set, never cleared) and changes NOTHING else — no endpoint
  state, no packet, no RNG registry entry, no run-link index, no output (see
  `lemma_corrupt_step_changes_only_compromise_metadata`).  Compromise is therefore
  purely environment/compromise METADATA at the concrete level; its effect is felt
  only through the two completion boundaries below (and, symbolically, through the
  DY* `Corrupt` entry the product records — see DH.Sample.Symbolic.Product).

  ── Signature / session-binding completion boundary MODULO COMPROMISE.
  `deliver_origin_ok` reserves the two completion messages to an honest sender (a
  `Sent Resp` Msg2, a `Sent Init` Msg3) UNLESS the role that signs that message is
  already compromised: a compromised signer's key is the attacker's, so an
  INJECTED Msg2 may complete the initiator once the responder is corrupt, and an
  INJECTED Msg3 may complete the responder once the initiator is corrupt.
  `ideal_completion_link_ok` ADDS the run-link (same Msg1 index) plus the minimum
  genuine phase facts — but, again, ONLY while the relevant signer role is
  uncompromised; after that compromise it imposes nothing, so a forged or replayed
  completion is accepted.  Neither guard states any identity or share the
  completion later concludes; those are consequences of the run link, not
  premises.  This is the signature binding to the run/session identifier,
  documented as such (see dh-sample/SYMBOLIC_SECURITY.md); the local endpoint
  state machines the Pulse implementation refines never observe it.  This is a
  FIXED, one-session, NON-injective model: there is no per-session index inside
  the signed content.
*)

module SM  = Common.StateMachine
module SMc = DH.Sample.StateMachine
module L   = FStar.List.Tot
open DH.Sample.Types
open DH.Sample.Crypto
open DH.Sample.Wire

(** ── Endpoints, packets, and the private RNG registry ────────────────────── *)

type endpoint_id =
  | Init
  | Resp

type pkt_origin =
  | Sent     : who:endpoint_id -> pkt_origin
  | Injected : pkt_origin

noeq
type packet = {
  pk_msg    : dh_message;
  pk_origin : pkt_origin;
}

(** The only constructor denotes an honest/internal ideal-RNG draw.  There is
    deliberately no attacker-origin constructor. *)
noeq
type rng_draw = {
  rd_owner  : endpoint_id;
  rd_scalar : dh_scalar;
}

(** Propositional list operations avoid assuming decidable equality for
    length-indexed byte sequences. *)
let rec rng_has (owner:endpoint_id) (x:dh_scalar) (draws:list rng_draw)
  : Tot prop (decreases draws) =
  match draws with
  | [] -> False
  | d :: tl ->
    (d.rd_owner == owner /\ d.rd_scalar == x) \/ rng_has owner x tl

let rec rng_scalar_fresh (x:dh_scalar) (draws:list rng_draw)
  : Tot prop (decreases draws) =
  match draws with
  | [] -> True
  | d :: tl -> x =!= d.rd_scalar /\ rng_scalar_fresh x tl

let rec rng_no_reuse (draws:list rng_draw)
  : Tot prop (decreases draws) =
  match draws with
  | [] -> True
  | d :: tl -> rng_scalar_fresh d.rd_scalar tl /\ rng_no_reuse tl

(** ── Composed state ─────────────────────────────────────────────────────── *)

noeq
type system_state = {
  sys_init          : endpoint_state;
  sys_resp          : endpoint_state;
  sys_net           : list packet;
  sys_rng           : list rng_draw;
  sys_init_pending  : option dh_scalar;
  sys_resp_pending  : option dh_scalar;
  (* Auditable run/session-link provenance.  `sys_init_msg1_idx` is the network
     index of the initiator's own Msg1 packet (set once at `ActStart`).
     `sys_resp_msg1_idx` is the index of the Msg1 the responder consumed (set once
     at its Msg1 delivery, from ANY origin — including an injected packet). *)
  sys_init_msg1_idx : option nat;
  sys_resp_msg1_idx : option nat;
  (* PERSISTENT per-role dynamic-compromise flags.  Set (and never cleared) by
     `ActCorrupt`; they are pure compromise metadata — no endpoint transition, no
     packet and no output ever reads them, only the two completion boundaries
     `deliver_origin_ok` / `ideal_completion_link_ok` do. *)
  sys_init_corrupt  : bool;
  sys_resp_corrupt  : bool;
}

(** The compromise flag of a role. *)
let corrupt_flag (st:system_state) (who:endpoint_id) : bool =
  match who with
  | Init -> st.sys_init_corrupt
  | Resp -> st.sys_resp_corrupt

(** The role whose long-term signing key authenticates a completion message:
    the responder signs Msg2 (which completes the initiator), the initiator signs
    Msg3 (which completes the responder).  Any other (destination, message) pair
    carries no completion signature. *)
let completion_signer (dst:endpoint_id) (m:dh_message) : option endpoint_id =
  match dst, m with
  | Init, Msg2 _ _ _ -> Some Resp
  | Resp, Msg3 _     -> Some Init
  | _, _             -> None

(** Every reserved or consumed local scalar occurs in the honest registry, and
    the registry contains no repeated concrete scalar. *)
let system_rng_wf (st:system_state) : prop =
  rng_no_reuse st.sys_rng /\
  (match st.sys_init_pending with
   | None -> True
   | Some x -> rng_has Init x st.sys_rng) /\
  (match st.sys_resp_pending with
   | None -> True
   | Some y -> rng_has Resp y st.sys_rng) /\
  (match st.sys_init.ep_scalar with
   | None -> True
   | Some x -> rng_has Init x st.sys_rng) /\
  (match st.sys_resp.ep_scalar with
   | None -> True
   | Some y -> rng_has Resp y st.sys_rng)

let system_initial (a b:principal) : system_state = {
  sys_init          = initial_initiator a b;
  sys_resp          = initial_responder b;
  sys_net           = [];
  sys_rng           = [];
  sys_init_pending  = None;
  sys_resp_pending  = None;
  sys_init_msg1_idx = None;
  sys_resp_msg1_idx = None;
  sys_init_corrupt  = false;
  sys_resp_corrupt  = false;
}

(** ── Actions ───────────────────────────────────────────────────────────────

    `ActRng` is an honest/internal environment transition.  Its scalar argument
    lets the concrete relational model choose bytes, but the freshness check and
    registry make that choice neither attacker-originated nor reusable.
    `ActStart` contains no arbitrary scalar: it consumes the initiator's pending
    honest draw.  `ActCorrupt who` is the attacker's DYNAMIC COMPROMISE of one
    role: it only sets that role's persistent compromise flag. *)
noeq
type sys_action =
  | ActRng     : owner:endpoint_id -> scalar:dh_scalar -> sys_action
  | ActStart   : sys_action
  | ActDeliver : idx:nat -> dst:endpoint_id -> sys_action
  | ActInject  : m:dh_message -> sys_action
  | ActCorrupt : who:endpoint_id -> sys_action

type sys_event  = SM.event dh_message sys_action
type sys_output = SM.step_output dh_message local_output

let empty_output : sys_output = {
  SM.so_wire_outputs = [];
  SM.so_local_outputs = [];
}

(** ── Network helpers and ideal attacker boundary ────────────────────────── *)

let sent_packets (who:endpoint_id) (msgs:list dh_message) : list packet =
  L.map (fun m -> { pk_msg = m; pk_origin = Sent who }) msgs

let append_honest (net:list packet) (who:endpoint_id) (msgs:list dh_message) : list packet =
  L.append net (sent_packets who msgs)

let wire_public (m:dh_message) : prop = True
let attacker_can_inject (net:list packet) (m:dh_message) : prop = wire_public m

(** A completion message must come from its honest signer UNLESS that signer role
    is already compromised — a compromised role's long-term signing key is the
    attacker's, so it can forge (or replay) that role's completion message. *)
let deliver_origin_ok
  (st0:system_state) (dst:endpoint_id) (m:dh_message) (o:pkt_origin) : prop =
  match dst, m with
  | Init, Msg2 _ _ _ -> o == Sent Resp \/ st0.sys_resp_corrupt
  | Resp, Msg3 _     -> o == Sent Init \/ st0.sys_init_corrupt
  | _, _             -> True

(** ── The signature / session-binding completion boundary, modulo compromise ──

    `deliver_origin_ok` (above) reserves the two COMPLETION messages to an honest
    sender — a `Sent Resp` Msg2, a `Sent Init` Msg3 — while the SIGNING role is
    uncompromised.  That is the unforgeability boundary: as long as the signer is
    honest, an ATTACKER-injected Msg2/Msg3 (origin `Injected`) can never complete a
    peer.  Msg1 delivery is deliberately NOT restricted, so an injected Msg1 CAN
    drive responder progress, corrupt or not.

    `ideal_completion_link_ok` ADDS, on top of that honest-origin restriction, the
    RUN/SESSION LINK plus the minimum genuine phase facts — and NOTHING that names
    an identity or a share the completion later concludes:

      * an initiator accepting the responder's Msg2:  the responder must have
        responded (`Resp_Wait3`/`Resp_Done` — a phase fact), and the responder's
        recorded consumed-Msg1 index must equal the initiator's own-Msg1 index
        (`sys_resp_msg1_idx == sys_init_msg1_idx`, both set) — i.e. the two flights
        belong to the SAME run;

      * a responder accepting the initiator's Msg3:  the initiator must have
        finished (`Init_Done` — a phase fact), and the same run-link index equality
        must hold.

    Both requirements are imposed ONLY BEFORE the relevant SIGNER role is
    compromised.  Once `sys_resp_corrupt` (resp. `sys_init_corrupt`) is set, the
    guard for an initiator (resp. responder) completion is vacuously satisfied: a
    FORGED or REPLAYED completion signed with the compromised role's key is
    accepted with no run link at all, exactly as a Dolev-Yao attacker holding that
    key could produce.  This is where dynamic compromise really bites, and it is
    why every authentication/agreement statement below is stated MODULO the
    corresponding role compromise.

    The concrete identity/share agreement of an UNCOMPROMISED completed session is
    still DERIVED from this index equality (via the append-only, immutable network
    provenance and the local transition semantics — see
    DH.Sample.Symbolic.Security), never restated here.  This is an explicit
    IDEAL-ENVIRONMENT boundary over the composed system, documented as such (see
    dh-sample/SYMBOLIC_SECURITY.md); the local endpoint machines the Pulse
    implementation refines never observe it.  It is a FIXED one-session,
    NON-injective signature model.  It is marked `opaque_to_smt` so it does not
    bloat the many lift/coherence/invariant queries that carry a `system_step`
    hypothesis but never inspect this guard; the few lemmas that DO need its
    content `reveal` it locally. *)
[@@"opaque_to_smt"]
let ideal_completion_link_ok (st0:system_state) (dst:endpoint_id) (m:dh_message) : prop =
  match dst, m with
  | Init, Msg2 _ _ _ ->
    st0.sys_resp_corrupt \/
    ((st0.sys_resp.ep_phase == Resp_Wait3 \/ st0.sys_resp.ep_phase == Resp_Done) /\
     Some? st0.sys_resp_msg1_idx /\
     st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx)
  | Resp, Msg3 _ ->
    st0.sys_init_corrupt \/
    (st0.sys_init.ep_phase == Init_Done /\
     Some? st0.sys_resp_msg1_idx /\
     st0.sys_resp_msg1_idx == st0.sys_init_msg1_idx)
  | _, _ -> True

(** ── Composed step relation ──────────────────────────────────────────────── *)

let system_step
  (st0:system_state)
  (ev:sys_event)
  (st1:system_state)
  (out:sys_output)
  : GTot prop =
  system_rng_wf st0 /\
  system_rng_wf st1 /\
  (match ev with
  | SM.LocalEvent (ActRng owner x) ->
    rng_scalar_fresh x st0.sys_rng /\
    out == empty_output /\
    (match owner with
     | Init ->
       st0.sys_init.ep_phase == Init_Start /\
       st0.sys_init.ep_scalar == None /\
       st0.sys_init_pending == None /\
       st1 == { st0 with
         sys_rng = { rd_owner = Init; rd_scalar = x } :: st0.sys_rng;
         sys_init_pending = Some x }
     | Resp ->
       st0.sys_resp.ep_phase == Resp_Start /\
       st0.sys_resp.ep_scalar == None /\
       st0.sys_resp_pending == None /\
       st1 == { st0 with
         sys_rng = { rd_owner = Resp; rd_scalar = x } :: st0.sys_rng;
         sys_resp_pending = Some x })

  | SM.LocalEvent ActStart ->
    (match st0.sys_init_pending with
     | None -> False
     | Some x ->
       SMc.initiator_step st0.sys_init
         (SM.LocalEvent (StartInitiator x)) st1.sys_init out /\
       st1.sys_resp == st0.sys_resp /\
       st1.sys_net  == append_honest st0.sys_net Init out.SM.so_wire_outputs /\
       st1.sys_rng == st0.sys_rng /\
       st1.sys_init_pending == None /\
       st1.sys_resp_pending == st0.sys_resp_pending /\
       (* record the network index of the initiator's own Msg1 (appended at the end) *)
       st1.sys_init_msg1_idx == Some (L.length st0.sys_net) /\
       st1.sys_resp_msg1_idx == st0.sys_resp_msg1_idx /\
       st1.sys_init_corrupt == st0.sys_init_corrupt /\
       st1.sys_resp_corrupt == st0.sys_resp_corrupt)

  | SM.LocalEvent (ActDeliver idx dst) ->
    idx < L.length st0.sys_net /\
    (let pkt = L.index st0.sys_net idx in
     deliver_origin_ok st0 dst pkt.pk_msg pkt.pk_origin /\
     ideal_completion_link_ok st0 dst pkt.pk_msg /\
     (match dst with
     | Init ->
       SMc.initiator_step st0.sys_init (SM.WireEvent pkt.pk_msg) st1.sys_init out /\
       st1.sys_resp == st0.sys_resp /\
       st1.sys_net  == append_honest st0.sys_net Init out.SM.so_wire_outputs /\
       st1.sys_rng == st0.sys_rng /\
       st1.sys_init_pending == st0.sys_init_pending /\
       st1.sys_resp_pending == st0.sys_resp_pending /\
       st1.sys_init_msg1_idx == st0.sys_init_msg1_idx /\
       st1.sys_resp_msg1_idx == st0.sys_resp_msg1_idx /\
       st1.sys_init_corrupt == st0.sys_init_corrupt /\
       st1.sys_resp_corrupt == st0.sys_resp_corrupt
     | Resp ->
       (match pkt.pk_msg with
        | Msg1 _ _ ->
          (match st0.sys_resp_pending with
           | None -> False
           | Some y ->
             SMc.responder_step st0.sys_resp (SM.WireEvent pkt.pk_msg) st1.sys_resp out /\
             st1.sys_resp.ep_scalar == Some y /\
             st1.sys_init == st0.sys_init /\
             st1.sys_net == append_honest st0.sys_net Resp out.SM.so_wire_outputs /\
             st1.sys_rng == st0.sys_rng /\
             st1.sys_init_pending == st0.sys_init_pending /\
             st1.sys_resp_pending == None /\
             st1.sys_init_msg1_idx == st0.sys_init_msg1_idx /\
             (* record the index of the Msg1 the responder consumed (any origin) *)
             st1.sys_resp_msg1_idx == Some idx /\
             st1.sys_init_corrupt == st0.sys_init_corrupt /\
             st1.sys_resp_corrupt == st0.sys_resp_corrupt)
        | _ ->
          SMc.responder_step st0.sys_resp (SM.WireEvent pkt.pk_msg) st1.sys_resp out /\
          st1.sys_init == st0.sys_init /\
          st1.sys_net == append_honest st0.sys_net Resp out.SM.so_wire_outputs /\
          st1.sys_rng == st0.sys_rng /\
          st1.sys_init_pending == st0.sys_init_pending /\
          st1.sys_resp_pending == st0.sys_resp_pending /\
          st1.sys_init_msg1_idx == st0.sys_init_msg1_idx /\
          st1.sys_resp_msg1_idx == st0.sys_resp_msg1_idx /\
          st1.sys_init_corrupt == st0.sys_init_corrupt /\
          st1.sys_resp_corrupt == st0.sys_resp_corrupt)))

  | SM.LocalEvent (ActInject m) ->
    attacker_can_inject st0.sys_net m /\
    st1.sys_init == st0.sys_init /\
    st1.sys_resp == st0.sys_resp /\
    st1.sys_net == L.append st0.sys_net
      [ { pk_msg = m; pk_origin = Injected } ] /\
    st1.sys_rng == st0.sys_rng /\
    st1.sys_init_pending == st0.sys_init_pending /\
    st1.sys_resp_pending == st0.sys_resp_pending /\
    st1.sys_init_msg1_idx == st0.sys_init_msg1_idx /\
    st1.sys_resp_msg1_idx == st0.sys_resp_msg1_idx /\
    st1.sys_init_corrupt == st0.sys_init_corrupt /\
    st1.sys_resp_corrupt == st0.sys_resp_corrupt /\
    out == empty_output

  (* DYNAMIC COMPROMISE.  The attacker compromises one role: the ONLY change is
     that role's persistent compromise flag.  Both endpoint states, the network,
     the RNG registry, both pending draws, both run-link indices and the output
     are literally unchanged (`st1 == { st0 with sys_*_corrupt = true }` pins
     every other field), so corruption can never be a disguised protocol step. *)
  | SM.LocalEvent (ActCorrupt who) ->
    out == empty_output /\
    (match who with
     | Init -> st1 == { st0 with sys_init_corrupt = true }
     | Resp -> st1 == { st0 with sys_resp_corrupt = true })

  | _ -> False)

noextract
let system_state_machine (a b:principal)
  : SM.state_machine system_state dh_message sys_action local_output = {
  SM.sm_initial_state = system_initial a b;
  SM.sm_step          = system_step;
}

type system_transition = SM.transition system_state dh_message sys_action local_output

(** ── Explicit local-machine projections ───────────────────────────────────

    These facts make the composition boundary precise.  Every composed start
    and delivery step literally contains the corresponding unchanged local
    `initiator_step` / `responder_step`; the system adds only RNG, network, and
    ideal-origin conditions around that local transition. *)

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"

let lemma_start_projects_local
  (st0 st1:system_state) (out:sys_output)
  : Lemma
    (requires system_step st0 (SM.LocalEvent ActStart) st1 out)
    (ensures
      exists (x:dh_scalar).
        st0.sys_init_pending == Some x /\
        SMc.initiator_step st0.sys_init
          (SM.LocalEvent (StartInitiator x)) st1.sys_init out)
= match st0.sys_init_pending with
  | None -> ()
  | Some x ->
    introduce exists (x':dh_scalar).
      st0.sys_init_pending == Some x' /\
      SMc.initiator_step st0.sys_init
        (SM.LocalEvent (StartInitiator x')) st1.sys_init out
    with x and ()

let lemma_delivery_projects_local
  (st0 st1:system_state) (idx:nat) (dst:endpoint_id) (out:sys_output)
  : Lemma
    (requires system_step st0 (SM.LocalEvent (ActDeliver idx dst)) st1 out)
    (ensures
      idx < L.length st0.sys_net /\
      (let pkt = L.index st0.sys_net idx in
       match dst with
       | Init ->
         SMc.initiator_step st0.sys_init (SM.WireEvent pkt.pk_msg) st1.sys_init out
       | Resp ->
         SMc.responder_step st0.sys_resp (SM.WireEvent pkt.pk_msg) st1.sys_resp out))
= ()

let lemma_rng_step_records_fresh
  (st0 st1:system_state) (owner:endpoint_id) (x:dh_scalar) (out:sys_output)
  : Lemma
    (requires system_step st0 (SM.LocalEvent (ActRng owner x)) st1 out)
    (ensures
      rng_scalar_fresh x st0.sys_rng /\
      rng_has owner x st1.sys_rng /\
      rng_no_reuse st1.sys_rng /\
      out == empty_output)
= match owner with Init -> () | Resp -> ()

let lemma_system_initial_valid (a b:principal)
  : Lemma (ensures SM.valid_state (system_state_machine a b)
                     (system_state_machine a b).SM.sm_initial_state)
= SM.lemma_initial_state_valid (system_state_machine a b)

(** ── Dynamic compromise is pure compromise metadata ──────────────────────────

    A legal `ActCorrupt` step changes NOTHING except the target role's persistent
    compromise flag: both endpoint states, the network, the RNG registry, both
    pending draws, both run-link indices and the step output are identical before
    and after.  So compromise can never smuggle in a protocol step, a packet, or
    an output — it only records that the attacker now holds that role's state. *)
let lemma_corrupt_step_changes_only_compromise_metadata
  (st0 st1:system_state) (who:endpoint_id) (out:sys_output)
  : Lemma
    (requires system_step st0 (SM.LocalEvent (ActCorrupt who)) st1 out)
    (ensures
      st1.sys_init == st0.sys_init /\
      st1.sys_resp == st0.sys_resp /\
      st1.sys_net == st0.sys_net /\
      st1.sys_rng == st0.sys_rng /\
      st1.sys_init_pending == st0.sys_init_pending /\
      st1.sys_resp_pending == st0.sys_resp_pending /\
      st1.sys_init_msg1_idx == st0.sys_init_msg1_idx /\
      st1.sys_resp_msg1_idx == st0.sys_resp_msg1_idx /\
      corrupt_flag st1 who == true /\
      (* the OTHER role's compromise flag is untouched *)
      (who == Init ==> st1.sys_resp_corrupt == st0.sys_resp_corrupt) /\
      (who == Resp ==> st1.sys_init_corrupt == st0.sys_init_corrupt) /\
      out == empty_output)
= match who with Init -> () | Resp -> ()

(** Compromise flags are PERSISTENT: no step of the composed system ever clears
    one.  (Read off every branch of `system_step`: the four protocol/environment
    actions copy both flags verbatim, and `ActCorrupt` only ever sets one.) *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 10 --split_queries always"
let lemma_corruption_monotone
  (st0 st1:system_state) (ev:sys_event) (out:sys_output)
  : Lemma
    (requires system_step st0 ev st1 out)
    (ensures
      (st0.sys_init_corrupt ==> st1.sys_init_corrupt) /\
      (st0.sys_resp_corrupt ==> st1.sys_resp_corrupt))
= match ev with
  | SM.LocalEvent (ActRng owner x) -> (match owner with Init -> () | Resp -> ())
  | SM.LocalEvent (ActCorrupt who) -> (match who with Init -> () | Resp -> ())
  | SM.LocalEvent ActStart -> ()
  | SM.LocalEvent (ActInject m) -> ()
  | SM.LocalEvent (ActDeliver idx dst) ->
    assert (idx < L.length st0.sys_net);
    let pkt = L.index st0.sys_net idx in
    (match dst, pkt.pk_msg with
     | Init, _ -> ()
     | Resp, Msg1 _ _ ->
       (match st0.sys_resp_pending with None -> () | Some _ -> ())
     | Resp, Msg2 _ _ _ -> ()
     | Resp, Msg3 _ -> ())
  | _ -> ()
#pop-options

#pop-options

(** ── Full honest run ───────────────────────────────────────────────────────

    Six transitions: draw x; start/send Msg1; draw y; deliver Msg1/send Msg2;
    deliver Msg2/send Msg3; deliver Msg3.  The freshness premise is exactly the
    concrete no-reuse obligation for the two honest draws. *)

let hgx (x:dh_scalar) : dh_share = dh_exp x
let hgy (y:dh_scalar) : dh_share = dh_exp y

let hsigB (a b:principal) (x y:dh_scalar) : signature =
  sign b (transcript a (hgx x) (hgy y))
let hsigA (a b:principal) (x y:dh_scalar) : signature =
  sign a (transcript b (hgx x) (hgy y))

let hikey (x y:dh_scalar) : shared_secret = dh_agree x (hgy y)
let hrkey (x y:dh_scalar) : shared_secret = dh_agree y (hgx x)

let h_ist1 (a b:principal) (x:dh_scalar) : endpoint_state =
  { initial_initiator a b with
    ep_phase = Init_Wait2; ep_scalar = Some x; ep_my_share = Some (hgx x) }

let h_ist2 (a b:principal) (x y:dh_scalar) : endpoint_state =
  { h_ist1 a b x with
    ep_phase = Init_Done; ep_peer_share = Some (hgy y); ep_key = Some (hikey x y) }

let h_rst1 (a b:principal) (x y:dh_scalar) : endpoint_state =
  { initial_responder b with
    ep_phase = Resp_Wait3; ep_peer = Some a; ep_scalar = Some y;
    ep_my_share = Some (hgy y); ep_peer_share = Some (hgx x);
    ep_key = Some (hrkey x y) }

let h_rst2 (a b:principal) (x y:dh_scalar) : endpoint_state =
  { h_rst1 a b x y with ep_phase = Resp_Done }

let h_p1 (a:principal) (x:dh_scalar) : packet =
  { pk_msg = Msg1 a (hgx x); pk_origin = Sent Init }
let h_p2 (a b:principal) (x y:dh_scalar) : packet =
  { pk_msg = Msg2 b (hgy y) (hsigB a b x y); pk_origin = Sent Resp }
let h_p3 (a b:principal) (x y:dh_scalar) : packet =
  { pk_msg = Msg3 (hsigA a b x y); pk_origin = Sent Init }

let h_dx (x:dh_scalar) : rng_draw = { rd_owner = Init; rd_scalar = x }
let h_dy (y:dh_scalar) : rng_draw = { rd_owner = Resp; rd_scalar = y }

let h_s0 (a b:principal) : system_state = system_initial a b
let h_s0x (a b:principal) (x:dh_scalar) : system_state =
  { h_s0 a b with sys_rng = [ h_dx x ]; sys_init_pending = Some x }
let h_s1 (a b:principal) (x:dh_scalar) : system_state =
  { h_s0x a b x with
    sys_init = h_ist1 a b x; sys_net = [ h_p1 a x ]; sys_init_pending = None;
    sys_init_msg1_idx = Some 0 }
let h_s1y (a b:principal) (x y:dh_scalar) : system_state =
  { h_s1 a b x with
    sys_rng = [ h_dy y; h_dx x ]; sys_resp_pending = Some y }
let h_s2 (a b:principal) (x y:dh_scalar) : system_state =
  { h_s1y a b x y with
    sys_resp = h_rst1 a b x y;
    sys_net = [ h_p1 a x; h_p2 a b x y ];
    sys_resp_pending = None;
    sys_resp_msg1_idx = Some 0 }
let h_s3 (a b:principal) (x y:dh_scalar) : system_state =
  { h_s2 a b x y with
    sys_init = h_ist2 a b x y;
    sys_net = [ h_p1 a x; h_p2 a b x y; h_p3 a b x y ] }
let h_s4 (a b:principal) (x y:dh_scalar) : system_state =
  { h_s3 a b x y with sys_resp = h_rst2 a b x y }

let h_t_rng_i (a b:principal) (x:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActRng Init x);
  SM.tr_next_state = h_s0x a b x;
  SM.tr_output     = empty_output;
}

let h_t1 (a b:principal) (x:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent ActStart;
  SM.tr_next_state = h_s1 a b x;
  SM.tr_output     = { SM.so_wire_outputs = [ Msg1 a (hgx x) ];
                       SM.so_local_outputs = [] };
}

let h_t_rng_r (a b:principal) (x y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActRng Resp y);
  SM.tr_next_state = h_s1y a b x y;
  SM.tr_output     = empty_output;
}

let h_t2 (a b:principal) (x y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActDeliver 0 Resp);
  SM.tr_next_state = h_s2 a b x y;
  SM.tr_output     = { SM.so_wire_outputs = [ Msg2 b (hgy y) (hsigB a b x y) ];
                       SM.so_local_outputs = [] };
}

let h_t3 (a b:principal) (x y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActDeliver 1 Init);
  SM.tr_next_state = h_s3 a b x y;
  SM.tr_output     = { SM.so_wire_outputs  = [ Msg3 (hsigA a b x y) ];
                       SM.so_local_outputs = [ SessionEstablished b (hikey x y) ] };
}

let h_t4 (a b:principal) (x y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActDeliver 2 Resp);
  SM.tr_next_state = h_s4 a b x y;
  SM.tr_output     = { SM.so_wire_outputs  = [];
                       SM.so_local_outputs = [ SessionEstablished a (hrkey x y) ] };
}

let honest_run (a b:principal) (x y:dh_scalar) : list system_transition =
  [ h_t_rng_i a b x; h_t1 a b x; h_t_rng_r a b x y;
    h_t2 a b x y; h_t3 a b x y; h_t4 a b x y ]

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10"

let lemma_honest_run_reaches (a b:principal) (x y:dh_scalar)
  : Lemma
      (requires x =!= y)
      (ensures (
        SM.trace_reaches (system_state_machine a b) (system_initial a b)
          (honest_run a b x y) (h_s4 a b x y) /\
        (h_s4 a b x y).sys_init.ep_phase == Init_Done /\
        (h_s4 a b x y).sys_resp.ep_phase == Resp_Done /\
        system_rng_wf (h_s4 a b x y) /\
        rng_has Init x (h_s4 a b x y).sys_rng /\
        rng_has Resp y (h_s4 a b x y).sys_rng /\
        hikey x y == hrkey x y))
= let gx = hgx x in
  let gy = hgy y in
  reveal_opaque (`%ideal_completion_link_ok) ideal_completion_link_ok;
  lemma_sign_verify b (transcript a gx gy);
  lemma_sign_verify a (transcript b gx gy);
  lemma_dh_agree x y;
  assert (system_step (h_s0 a b) (SM.LocalEvent (ActRng Init x)) (h_s0x a b x)
            (h_t_rng_i a b x).SM.tr_output);
  assert (append_honest [] Init [ Msg1 a gx ] == [ h_p1 a x ]);
  assert (system_step (h_s0x a b x) (SM.LocalEvent ActStart) (h_s1 a b x)
            (h_t1 a b x).SM.tr_output);
  assert (system_step (h_s1 a b x) (SM.LocalEvent (ActRng Resp y)) (h_s1y a b x y)
            (h_t_rng_r a b x y).SM.tr_output);
  assert (L.index (h_s1y a b x y).sys_net 0 == h_p1 a x);
  assert (append_honest [ h_p1 a x ] Resp [ Msg2 b gy (hsigB a b x y) ]
            == [ h_p1 a x; h_p2 a b x y ]);
  assert (system_step (h_s1y a b x y) (SM.LocalEvent (ActDeliver 0 Resp)) (h_s2 a b x y)
            (h_t2 a b x y).SM.tr_output);
  assert (L.index (h_s2 a b x y).sys_net 1 == h_p2 a b x y);
  assert (append_honest [ h_p1 a x; h_p2 a b x y ] Init [ Msg3 (hsigA a b x y) ]
            == [ h_p1 a x; h_p2 a b x y; h_p3 a b x y ]);
  assert (system_step (h_s2 a b x y) (SM.LocalEvent (ActDeliver 1 Init)) (h_s3 a b x y)
            (h_t3 a b x y).SM.tr_output);
  assert (L.index (h_s3 a b x y).sys_net 2 == h_p3 a b x y);
  assert (system_step (h_s3 a b x y) (SM.LocalEvent (ActDeliver 2 Resp)) (h_s4 a b x y)
            (h_t4 a b x y).SM.tr_output)

#pop-options

(** ── Active-attacker witness (non-vacuity of the injected-Msg1 attack) ────────

    `ActInject` is load-bearing, not decorative.  After a responder scalar draw,
    the attacker injects a Msg1 with ARBITRARY identity/share and routes it to the
    responder, which leaves `Resp_Start` for `Resp_Wait3` and emits an honest Msg2
    over the ATTACKER-chosen share.  The consumed packet has `Injected` origin (no
    honest initiator ever sent it) and the run link is BROKEN — the responder's
    recorded `sys_resp_msg1_idx = Some 0` while `sys_init_msg1_idx = None` — so no
    Msg3 completion is admissible and no honest-peer agreement or key secrecy is
    claimed for this attacker-selected intermediate responder key.  This is the
    candid "attacker can start / DoS the responder but cannot complete
    authentication" story. *)
let a_pkt_inj (am:principal) (ash:dh_share) : packet =
  { pk_msg = Msg1 am ash; pk_origin = Injected }

let a_rst_wait3 (b am:principal) (ash:dh_share) (y:dh_scalar) : endpoint_state =
  { initial_responder b with
    ep_phase = Resp_Wait3; ep_peer = Some am; ep_scalar = Some y;
    ep_my_share = Some (dh_exp y); ep_peer_share = Some ash;
    ep_key = Some (dh_agree y ash) }

let a_msg2 (b am:principal) (ash:dh_share) (y:dh_scalar) : dh_message =
  Msg2 b (dh_exp y) (sign b (transcript am ash (dh_exp y)))
let a_pkt_msg2 (b am:principal) (ash:dh_share) (y:dh_scalar) : packet =
  { pk_msg = a_msg2 b am ash y; pk_origin = Sent Resp }

let a_s0 (a b:principal) : system_state = system_initial a b
let a_s0y (a b:principal) (y:dh_scalar) : system_state =
  { a_s0 a b with sys_rng = [ h_dy y ]; sys_resp_pending = Some y }
let a_s1 (a b am:principal) (ash:dh_share) (y:dh_scalar) : system_state =
  { a_s0y a b y with sys_net = [ a_pkt_inj am ash ] }
let a_s2 (a b am:principal) (ash:dh_share) (y:dh_scalar) : system_state =
  { a_s1 a b am ash y with
    sys_resp = a_rst_wait3 b am ash y;
    sys_net = [ a_pkt_inj am ash; a_pkt_msg2 b am ash y ];
    sys_resp_pending = None;
    sys_resp_msg1_idx = Some 0 }

let a_t_rng (a b:principal) (y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActRng Resp y);
  SM.tr_next_state = a_s0y a b y;
  SM.tr_output     = empty_output;
}
let a_t_inject (a b am:principal) (ash:dh_share) (y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActInject (Msg1 am ash));
  SM.tr_next_state = a_s1 a b am ash y;
  SM.tr_output     = empty_output;
}
let a_t_deliver (a b am:principal) (ash:dh_share) (y:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActDeliver 0 Resp);
  SM.tr_next_state = a_s2 a b am ash y;
  SM.tr_output     = { SM.so_wire_outputs = [ a_msg2 b am ash y ]; SM.so_local_outputs = [] };
}

let attacker_run (a b am:principal) (ash:dh_share) (y:dh_scalar) : list system_transition =
  [ a_t_rng a b y; a_t_inject a b am ash y; a_t_deliver a b am ash y ]

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10"
let lemma_attacker_run_reaches (a b am:principal) (ash:dh_share) (y:dh_scalar)
  : Lemma
      (ensures (
        SM.trace_reaches (system_state_machine a b) (system_initial a b)
          (attacker_run a b am ash y) (a_s2 a b am ash y) /\
        (a_s2 a b am ash y).sys_resp.ep_phase == Resp_Wait3 /\
        (a_s2 a b am ash y).sys_init.ep_phase == Init_Start /\
        (a_s2 a b am ash y).sys_resp_msg1_idx == Some 0 /\
        (a_s2 a b am ash y).sys_init_msg1_idx == None /\
        (* the consumed Msg1 was injected, never honestly sent *)
        (L.index (a_s2 a b am ash y).sys_net 0).pk_origin == Injected /\
        (* the responder's peer share is the attacker's chosen share *)
        (a_s2 a b am ash y).sys_resp.ep_peer_share == Some ash))
= assert (system_step (a_s0 a b) (SM.LocalEvent (ActRng Resp y)) (a_s0y a b y)
            (a_t_rng a b y).SM.tr_output);
  reveal_opaque (`%ideal_completion_link_ok) ideal_completion_link_ok;
  assert (L.append [] [ a_pkt_inj am ash ] == [ a_pkt_inj am ash ]);
  assert (system_step (a_s0y a b y) (SM.LocalEvent (ActInject (Msg1 am ash)))
            (a_s1 a b am ash y) (a_t_inject a b am ash y).SM.tr_output);
  assert (L.index (a_s1 a b am ash y).sys_net 0 == a_pkt_inj am ash);
  assert (append_honest [ a_pkt_inj am ash ] Resp [ a_msg2 b am ash y ]
            == [ a_pkt_inj am ash; a_pkt_msg2 b am ash y ]);
  assert (system_step (a_s1 a b am ash y) (SM.LocalEvent (ActDeliver 0 Resp))
            (a_s2 a b am ash y) (a_t_deliver a b am ash y).SM.tr_output)
#pop-options

(** ── Compromised-completion witness (non-vacuity of dynamic compromise) ───────

    `ActCorrupt` is load-bearing, not decorative, and the compromised branch of
    every completion boundary is genuinely REACHABLE.  The run below is:

      draw x; ActStart (the initiator publishes its own honest Msg1 at index 0);
      ActCorrupt Resp (the responder's long-term signing state is compromised);
      ActInject of a FORGED Msg2 that carries an ARBITRARY attacker share `agy`
      and the responder-key signature the attacker can now produce;
      ActDeliver of that INJECTED packet to the initiator.

    The delivery is admissible ONLY because `sys_resp_corrupt` is set: with an
    honest responder, `deliver_origin_ok` would reject the `Injected` origin AND
    `ideal_completion_link_ok` would demand a run link the responder never
    established.  The initiator nevertheless reaches `Init_Done`, with the
    attacker's share as its peer share, while the responder NEVER left
    `Resp_Start`.  So after compromise a completion is genuinely FORGED: no
    honest-peer authorization, no matching session, no key secrecy — exactly what
    the "modulo compromise" security statements allow, and nothing less. *)
let c_sigB (a b:principal) (x:dh_scalar) (agy:dh_share) : signature =
  sign b (transcript a (hgx x) agy)
let c_msg2 (a b:principal) (x:dh_scalar) (agy:dh_share) : dh_message =
  Msg2 b agy (c_sigB a b x agy)
let c_pkt2 (a b:principal) (x:dh_scalar) (agy:dh_share) : packet =
  { pk_msg = c_msg2 a b x agy; pk_origin = Injected }

let c_sigA (a b:principal) (x:dh_scalar) (agy:dh_share) : signature =
  sign a (transcript b (hgx x) agy)
let c_msg3 (a b:principal) (x:dh_scalar) (agy:dh_share) : dh_message =
  Msg3 (c_sigA a b x agy)
let c_pkt3 (a b:principal) (x:dh_scalar) (agy:dh_share) : packet =
  { pk_msg = c_msg3 a b x agy; pk_origin = Sent Init }

let c_ist2 (a b:principal) (x:dh_scalar) (agy:dh_share) : endpoint_state =
  { h_ist1 a b x with
    ep_phase = Init_Done; ep_peer_share = Some agy;
    ep_key = Some (dh_agree x agy) }

let c_s0 (a b:principal) : system_state = system_initial a b
let c_s0x (a b:principal) (x:dh_scalar) : system_state =
  { c_s0 a b with sys_rng = [ h_dx x ]; sys_init_pending = Some x }
let c_s1 (a b:principal) (x:dh_scalar) : system_state =
  { c_s0x a b x with
    sys_init = h_ist1 a b x; sys_net = [ h_p1 a x ]; sys_init_pending = None;
    sys_init_msg1_idx = Some 0 }
let c_s2 (a b:principal) (x:dh_scalar) : system_state =
  { c_s1 a b x with sys_resp_corrupt = true }
let c_s3 (a b:principal) (x:dh_scalar) (agy:dh_share) : system_state =
  { c_s2 a b x with sys_net = [ h_p1 a x; c_pkt2 a b x agy ] }
let c_s4 (a b:principal) (x:dh_scalar) (agy:dh_share) : system_state =
  { c_s3 a b x agy with
    sys_init = c_ist2 a b x agy;
    sys_net = [ h_p1 a x; c_pkt2 a b x agy; c_pkt3 a b x agy ] }

let c_t_rng (a b:principal) (x:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActRng Init x);
  SM.tr_next_state = c_s0x a b x;
  SM.tr_output     = empty_output;
}
let c_t_start (a b:principal) (x:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent ActStart;
  SM.tr_next_state = c_s1 a b x;
  SM.tr_output     = { SM.so_wire_outputs = [ Msg1 a (hgx x) ];
                       SM.so_local_outputs = [] };
}
let c_t_corrupt (a b:principal) (x:dh_scalar) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActCorrupt Resp);
  SM.tr_next_state = c_s2 a b x;
  SM.tr_output     = empty_output;
}
let c_t_inject (a b:principal) (x:dh_scalar) (agy:dh_share) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActInject (c_msg2 a b x agy));
  SM.tr_next_state = c_s3 a b x agy;
  SM.tr_output     = empty_output;
}
let c_t_deliver (a b:principal) (x:dh_scalar) (agy:dh_share) : system_transition = {
  SM.tr_event      = SM.LocalEvent (ActDeliver 1 Init);
  SM.tr_next_state = c_s4 a b x agy;
  SM.tr_output     = { SM.so_wire_outputs  = [ c_msg3 a b x agy ];
                       SM.so_local_outputs = [ SessionEstablished b (dh_agree x agy) ] };
}

let corrupt_run (a b:principal) (x:dh_scalar) (agy:dh_share) : list system_transition =
  [ c_t_rng a b x; c_t_start a b x; c_t_corrupt a b x;
    c_t_inject a b x agy; c_t_deliver a b x agy ]

#push-options "--fuel 10 --ifuel 2 --z3rlimit 10"
let lemma_corrupt_run_reaches (a b:principal) (x:dh_scalar) (agy:dh_share)
  : Lemma
      (ensures (
        SM.trace_reaches (system_state_machine a b) (system_initial a b)
          (corrupt_run a b x agy) (c_s4 a b x agy) /\
        (* the responder was compromised, and never ran at all *)
        (c_s4 a b x agy).sys_resp_corrupt == true /\
        (c_s4 a b x agy).sys_init_corrupt == false /\
        (c_s4 a b x agy).sys_resp.ep_phase == Resp_Start /\
        (* yet the initiator COMPLETED, on an INJECTED, forged Msg2 ... *)
        (c_s4 a b x agy).sys_init.ep_phase == Init_Done /\
        (L.index (c_s4 a b x agy).sys_net 1).pk_origin == Injected /\
        (* ... with the ATTACKER's share as its peer share and session key *)
        (c_s4 a b x agy).sys_init.ep_peer_share == Some agy /\
        (c_s4 a b x agy).sys_init.ep_key == Some (dh_agree x agy) /\
        (* and no run link whatsoever *)
        (c_s4 a b x agy).sys_resp_msg1_idx == None))
= let gx = hgx x in
  reveal_opaque (`%ideal_completion_link_ok) ideal_completion_link_ok;
  lemma_sign_verify b (transcript a gx agy);
  assert (system_step (c_s0 a b) (SM.LocalEvent (ActRng Init x)) (c_s0x a b x)
            (c_t_rng a b x).SM.tr_output);
  assert (append_honest [] Init [ Msg1 a gx ] == [ h_p1 a x ]);
  assert (system_step (c_s0x a b x) (SM.LocalEvent ActStart) (c_s1 a b x)
            (c_t_start a b x).SM.tr_output);
  assert (system_step (c_s1 a b x) (SM.LocalEvent (ActCorrupt Resp)) (c_s2 a b x)
            (c_t_corrupt a b x).SM.tr_output);
  assert (L.append [ h_p1 a x ] [ c_pkt2 a b x agy ] == [ h_p1 a x; c_pkt2 a b x agy ]);
  assert (system_step (c_s2 a b x) (SM.LocalEvent (ActInject (c_msg2 a b x agy)))
            (c_s3 a b x agy) (c_t_inject a b x agy).SM.tr_output);
  assert (L.index (c_s3 a b x agy).sys_net 1 == c_pkt2 a b x agy);
  assert (append_honest [ h_p1 a x; c_pkt2 a b x agy ] Init [ c_msg3 a b x agy ]
            == [ h_p1 a x; c_pkt2 a b x agy; c_pkt3 a b x agy ]);
  assert (system_step (c_s3 a b x agy) (SM.LocalEvent (ActDeliver 1 Init))
            (c_s4 a b x agy) (c_t_deliver a b x agy).SM.tr_output)
#pop-options

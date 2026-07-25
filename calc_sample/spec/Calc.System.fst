module Calc.System

(**
  The combined calculator client–server system.

  This composes the verified client (`Calc.Client.Log`) and server
  (`Calc.Log`) abstract state machines into a single transition system with an
  explicit message channel, so that temporal properties of their *interaction*
  can be stated and proved (see `Calc.System.Temporal`).

  The protocol is strict request/response lockstep, so at most one message is
  ever in flight; the channel is:

    - `Quiet`      : nothing in flight (the system is quiescent);
    - `InReq b`    : the client has sent request frame `b`, the server has not
                     yet processed it;
    - `InResp r`   : the server has produced response frame `r`, the client has
                     not yet received it.

  The three transitions are `issue` (client sends a request), `serve` (server
  processes the in-flight request) and `recv` (client receives the response).

  The key structural invariant (`system_inv`, proved inductive below) pins down
  exactly how the two endpoints lag during delivery:

    - `Quiet`/`InReq`: the server log equals the client's completed log
      (so the stacks agree);
    - `InResp`: the server has advanced one request ahead of the client's
      completed log.
**)

module R = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module CalcP = Calc.Protocol
module SP = Common.SystemProduct

open Calc.Spec
open Calc.Wire
open Calc.Log
open Calc.Client.Log
open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight message channel (at most one message). **)
noeq
type channel_state =
  | Quiet  : channel_state
  | InReq  : CalcP.calc_frame -> channel_state
  | InResp : CalcP.calc_frame -> channel_state

(** The combined system state: client, server, and the channel between them. **)
noeq
type system_state = {
  client:  client_state_abs;
  server:  calc_log;
  channel: channel_state;
}

(** The stacks we ultimately want to compare. **)
let client_stack (s:system_state) : calc_stack = s.client.completed.current_state
let server_stack (s:system_state) : calc_stack = s.server.current_state

(** The system is quiescent when nothing is in flight. **)
let quiescent (s:system_state) : prop = Quiet? s.channel

(** Initial state: fresh client, fresh server, empty channel. **)
let initial_system : system_state = {
  client  = initial_client;
  server  = initial_log;
  channel = Quiet;
}

(** ─────────────────────────────────────────────────────────────────────────
    The server processing a single request frame (mirrors recv_completed).
    ───────────────────────────────────────────────────────────────────────── **)

(** The server log after processing request frame `b`. **)
let server_process (srv:calc_log) (b:CalcP.calc_frame) : calc_log =
  let req = CalcP.calc_frame_request b in
  let (new_state, resp) = step srv.current_state req in
  {
    input_bytes   = Seq.append srv.input_bytes b;
    output_bytes  = Seq.append srv.output_bytes (serialize_response resp);
    requests      = srv.requests @ [req];
    responses     = srv.responses @ [resp];
    current_state = new_state;
  }

(**
  `server_process` on a client's completed log is exactly the client's own
  `recv_completed`: they are the same computation. This equality is what makes
  the `recv` transition re-establish `server == client.completed`.
**)
val lemma_recv_completed_eq (st:client_state_abs{Some? st.pending})
  : Lemma (recv_completed st == server_process st.completed (Some?.v st.pending))
let lemma_recv_completed_eq st = ()

(** ─────────────────────────────────────────────────────────────────────────
    Transitions (as total functions; guarded by the step relation below)
    ───────────────────────────────────────────────────────────────────────── **)

(** Client issues request frame `b` (only meaningful when Quiet & Idle). **)
let do_issue (b:CalcP.calc_frame) (s:system_state) : system_state =
  if Quiet? s.channel && None? s.client.pending
  then { s with client = client_issue b s.client; channel = InReq b }
  else s

(** Server processes the in-flight request. **)
let do_serve (s:system_state) : system_state =
  match s.channel with
  | InReq b ->
    { s with
      server  = server_process s.server b;
      channel = InResp (CalcP.calc_frame_response_for s.server b) }
  | _ -> s

(** Client receives the in-flight response (only meaningful when awaiting). **)
let do_recv (s:system_state) : system_state =
  if InResp? s.channel && Some? s.client.pending
  then { s with client = client_recv s.client; channel = Quiet }
  else s

(** ─────────────────────────────────────────────────────────────────────────
    The system step relation
    ───────────────────────────────────────────────────────────────────────── **)

(** The calculator system as an instance of the generic single-slot
    directed-channel product (`Common.SystemProduct`).  The channel observations
    read off `channel_state`.  The calculator is a strict request/response
    protocol: the client `issue`s (an OUTPUT to the server), the server `serve`s
    (a FUSED receive-and-respond, the product's `server_serve`), and the client
    `recv`s the response (a DELIVER to the client).  There is no plain server
    output, no server-directed delivery, and no purely internal move, so those
    four families are the empty relation.  `product_step SP` supplies the channel
    discipline (issue needs Quiet, serve needs a request in flight, recv needs a
    response in flight). **)
let calc_iface : SP.prod_iface system_state = {
  is_quiet     = (fun s -> Quiet? s.channel);
  in_to_server = (fun s -> InReq? s.channel);
  in_to_client = (fun s -> InResp? s.channel);
  // issue: client OUTPUT (Quiet gate supplied by product_step)
  client_send       = (fun s s' -> None? s.client.pending /\ (exists (b:CalcP.calc_frame). s' == do_issue b s));
  server_send       = SP.no_move;
  // recv: client DELIVER (InResp gate supplied by product_step)
  deliver_to_client = (fun s s' -> Some? s.client.pending /\ s' == do_recv s);
  deliver_to_server = SP.no_move;
  client_local      = SP.no_move;
  server_local      = SP.no_move;
  // serve: server FUSED receive-and-respond (InReq gate supplied by product_step)
  server_serve      = (fun s s' -> InReq? s.channel /\
                                    Some? s.client.pending /\
                                    Some?.v s.client.pending == InReq?._0 s.channel /\
                                    s' == do_serve s);
}

let sys_step : R.binrel system_state =
  fun s s' -> SP.product_step calc_iface s s'

(** Stutter-tolerant step: a real step or "no delivery yet". Used for runs where
    the environment may delay delivery (needed for the liveness statement). **)
let sys_step_stutter : R.binrel system_state =
  fun s s' -> sys_step s s' \/ s' == s

let reachable (s s':system_state) : prop = R.closure sys_step s s'

(** ─────────────────────────────────────────────────────────────────────────
    The structural invariant and its inductiveness
    ───────────────────────────────────────────────────────────────────────── **)

(**
  The invariant precisely describes the lag between client and server:
    - Quiet / InReq: the server log equals the client's completed log;
    - InResp r: the server is one processed request ahead, and `r` is that
      request's response.
**)
let system_inv (s:system_state) : prop =
  match s.channel with
  | Quiet ->
    None? s.client.pending /\
    s.server == s.client.completed
  | InReq b ->
    s.client.pending == Some b /\
    s.server == s.client.completed
  | InResp r ->
    Some? s.client.pending /\
    (let b = Some?.v s.client.pending in
     s.server == server_process s.client.completed b /\
     r == CalcP.calc_frame_response_for s.client.completed b)

val lemma_initial_inv : unit -> Lemma (system_inv initial_system)
let lemma_initial_inv () = ()

#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
val lemma_inv_preserved (s s':system_state)
  : Lemma (requires system_inv s /\ sys_step s s')
          (ensures system_inv s')
let lemma_inv_preserved s s' =
  match s.channel with
  | Quiet ->
    // Only the issue step is enabled.
    eliminate exists (b:CalcP.calc_frame). s' == do_issue b s
    returns system_inv s'
    with _pf. ()
  | InReq b ->
    // Only the serve step is enabled; server advances by server_process.
    ()
  | InResp r ->
    // Only the recv step is enabled; client catches up to the server.
    let b = Some?.v s.client.pending in
    lemma_recv_completed_eq s.client;
    ()
#pop-options

(** The invariant holds on every reachable state. **)
val lemma_reachable_inv (s:system_state)
  : Lemma (requires reachable initial_system s)
          (ensures system_inv s)
let lemma_reachable_inv s =
  lemma_initial_inv ();
  Classical.forall_intro_2
    (Classical.move_requires_2 lemma_inv_preserved);
  R.stable_on_closure sys_step system_inv ()

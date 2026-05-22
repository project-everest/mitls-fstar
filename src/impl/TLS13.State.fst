module TLS13.State

#lang-pulse

open Pulse.Lib.Pervasives

module MR = Pulse.Lib.MonotonicGhostRef
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine

let state_ref : Type0 = MR.mref S.conn_evolves

let current ([@@@mkey] r:state_ref) (s:S.conn_state) : slprop =
  MR.pts_to r #1.0R s

let snapshot ([@@@mkey] r:state_ref) (s:S.conn_state) : slprop =
  MR.snapshot r s

ghost
fn alloc_initial ()
  returns r: state_ref
  ensures current r S.initial
{
  let r = MR.alloc #S.conn_state #S.conn_evolves S.initial;
  fold (current r S.initial);
  r
}

ghost
fn take_snapshot (r:state_ref) (#s:S.conn_state)
  preserves current r s
  ensures snapshot r s
{
  unfold current;
  MR.take_snapshot #S.conn_state #S.conn_evolves r s;
  fold (snapshot r s);
  fold current;
}

ghost
fn recall_snapshot (r:state_ref) (#s0 #s1:S.conn_state)
  preserves current r s1
  preserves snapshot r s0
  ensures pure (S.conn_evolves s0 s1)
{
  unfold current;
  unfold snapshot;
  MR.recall_snapshot #S.conn_state #S.conn_evolves r;
  fold (snapshot r s0);
  fold current;
}

ghost
fn advance (r:state_ref) (#s0:S.conn_state) (e:S.event) (s1:S.conn_state)
  requires current r s0
  requires pure (S.step s0 e == Some s1)
  ensures current r s1
{
  assert (pure (S.step s0 e == Some s1));
  assert (pure (S.state_single_step s0 s1));
  unfold current;
  RTC.closure_step S.state_single_step s0 s1;
  MR.update #S.conn_state #S.conn_evolves r s1;
  fold (current r s1);
}

ghost
fn advance_fail (r:state_ref) (#s0:S.conn_state) (err:TLS13.Types.tls_error)
  requires current r s0
  ensures current r (S.fail s0 err)
{
  advance r (S.Fail err) (S.fail s0 err);
}

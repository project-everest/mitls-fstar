module TLS13.Connection.StateDriver

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module S = TLS13.StateMachine
module ST = TLS13.State

ghost
fn application_echo_roundtrip
  (st:ST.state_ref)
  (#s:S.conn_state)
  (sent:B.bytes)
  (received:B.bytes)
  requires ST.current st s
  requires pure (s.S.phase == S.ApplicationData)
  ensures ST.current st s **
          ST.snapshot st s **
          pure (S.conn_evolves s s)
{
  ST.take_snapshot st;
  ST.advance st (S.SendApplicationData sent) s;
  ST.advance st (S.RecvApplicationData received) s;
  ST.recall_snapshot st;
}

ghost
fn close_after_application_data
  (st:ST.state_ref)
  (#s:S.conn_state)
  requires ST.current st s
  requires pure (s.S.phase == S.ApplicationData)
  ensures exists* closed.
          ST.current st closed **
          ST.snapshot st s **
          pure (S.conn_evolves s closed /\ closed.S.phase == S.Closed)
{
  ST.take_snapshot st;

  let closing = S.with_phase s S.Closing;
  ST.advance st S.SendCloseNotify closing;

  let closed = S.with_phase closing S.Closed;
  ST.advance st S.RecvCloseNotify closed;

  ST.recall_snapshot st;
}

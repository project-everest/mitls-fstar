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
  ensures exists* s'.
          ST.current st s' **
          ST.snapshot st s **
          pure (S.conn_evolves s s' /\ s'.S.phase == S.ApplicationData)
{
  ST.take_snapshot st;
  let sent_s = S.advance_write_records s (S.application_data_record_count sent);
  ST.advance st (S.SendApplicationData sent) sent_s;

  S.lemma_advance_write_records_preserves_phase s (S.application_data_record_count sent);
  assert (pure (sent_s.S.phase == S.ApplicationData));
  let received_s = S.advance_read_record sent_s;
  ST.advance st (S.RecvApplicationData received) received_s;

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

  let closing = S.send_close_state s;
  ST.advance st S.SendCloseNotify closing;

  let closed = S.recv_close_state closing;
  ST.advance st S.RecvCloseNotify closed;

  ST.recall_snapshot st;
}

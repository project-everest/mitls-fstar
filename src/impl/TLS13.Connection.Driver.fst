module TLS13.Connection.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Connection
module IO = TLS13.IO
module S = TLS13.StateMachine
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn connect_write_read_exact
  (c: C.connection)
  (ch: IO.channel)
  (outbound: array U8.t)
  (outbound_len: SZ.t)
  (inbound: array U8.t)
  (inbound_len: SZ.t)
  requires C.is_connection c 'st 's **
           IO.is_channel ch **
           pts_to outbound 'outbound_bytes **
           pts_to inbound 'old_inbound_bytes **
           pure ('s.S.phase == S.Start /\
                 B.length 'outbound_bytes == SZ.v outbound_len /\
                 B.length 'old_inbound_bytes == SZ.v inbound_len)
  returns ok: bool
  ensures exists* s' inbound_bytes.
          C.is_connection c 'st s' **
          IO.is_channel ch **
          pts_to outbound 'outbound_bytes **
          pts_to inbound inbound_bytes **
          pure (B.length inbound_bytes == SZ.v inbound_len /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))
{
  let ok_connect = C.client_connect c ch;
  if ok_connect {
    let ok_write = C.client_write_all c ch outbound outbound_len;
    if ok_write {
      C.client_read_exact c ch inbound inbound_len
    } else {
      false
    }
  } else {
    false
  }
}

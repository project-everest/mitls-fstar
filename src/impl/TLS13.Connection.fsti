module TLS13.Connection

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

val connection : Type0

val is_connection: connection -> ST.state_ref -> S.conn_state -> slprop

fn client_new
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (trust_store: X.trust_store)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns c: connection
  ensures exists* st.
          pts_to hostname 'hostname_bytes **
          is_connection c st S.initial

fn client_free (c: connection)
  requires is_connection c 'st 's
  ensures emp

fn client_connect (c: connection) (ch: IO.channel)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))

fn client_write (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns written: SZ.t
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (SZ.v written <= SZ.v len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Failed))

fn client_write_all (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to buf 'bytes **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns ok: bool
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))

fn client_read (c: connection) (ch: IO.channel) (out: array U8.t) (max_len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to out 'old **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* s' bytes. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Closing \/
                 s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))

fn client_read_exact (c: connection) (ch: IO.channel) (out: array U8.t) (len: SZ.t)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pts_to out 'old **
           pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v len)
  returns ok: bool
  ensures exists* s' bytes. is_connection c 'st s' **
          IO.is_channel ch **
          pts_to out bytes **
          pure (B.length bytes == SZ.v len /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))

fn client_close (c: connection) (ch: IO.channel)
  requires is_connection c 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.ApplicationData \/ 's.S.phase == S.Closing)
  ensures exists* s'. is_connection c 'st s' **
          IO.is_channel ch **
          pure (s'.S.phase == S.Closing \/ s'.S.phase == S.Closed \/ s'.S.phase == S.Failed)

module TLS13.Connection

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

val connection : Type0

val connection_exactly: connection -> ST.state_ref -> S.conn_state -> CL.connection_view -> slprop

val is_connection: connection -> ST.state_ref -> S.conn_state -> slprop

ghost
fn reveal_connection_view (c: connection)
  requires is_connection c 'st 's
  ensures exists* view. connection_exactly c 'st 's view

ghost
fn hide_connection_view (c: connection)
  requires connection_exactly c 'st 's 'view
  ensures is_connection c 'st 's

fn client_new
  (hostname: array U8.t)
  (hostname_len: SZ.t)
  (#trust_store: X.trust_store)
  requires pts_to hostname 'hostname_bytes **
           pure (B.length 'hostname_bytes == SZ.v hostname_len)
  returns c: connection
  ensures exists* st.
          pts_to hostname 'hostname_bytes **
          connection_exactly c st S.initial CL.empty_connection_view

fn client_free (c: connection)
  requires connection_exactly c 'st 's 'view
  ensures emp

fn client_connect (c: connection) (ch: IO.channel)
  requires connection_exactly c 'st 's 'view0 **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))

fn client_write (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns written: SZ.t
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in (CL.OpSendApplicationData 'bytes)) view1 resp) /\
                SZ.v written <= SZ.v len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Failed))

fn client_write_all (c: connection) (ch: IO.channel) (buf: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'bytes == SZ.v len)
  returns ok: bool
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to buf 'bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in (CL.OpSendApplicationData 'bytes)) view1 resp) /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))

fn client_read (c: connection) (ch: IO.channel) (out: array U8.t) (max_len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to out 'old **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v max_len)
  returns n: SZ.t
  ensures exists* s' view1 bytes. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to out bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0
                  (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v max_len)) 'view0.CL.raw_log view1.CL.raw_log)
                  view1 resp) /\
                B.length bytes == SZ.v max_len /\
                SZ.v n <= SZ.v max_len /\
                (s'.S.phase == S.ApplicationData \/ s'.S.phase == S.Closing \/
                 s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))

fn client_read_exact (c: connection) (ch: IO.channel) (out: array U8.t) (len: SZ.t)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pts_to out 'old **
          pure ('s.S.phase == S.ApplicationData /\ B.length 'old == SZ.v len)
  returns ok: bool
  ensures exists* s' view1 bytes. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pts_to out bytes **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0
                  (CL.request_with_received_raw_delta (CL.OpReadApplicationData (SZ.v len)) 'view0.CL.raw_log view1.CL.raw_log)
                  view1 resp) /\
                B.length bytes == SZ.v len /\
                (ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Closed \/ s'.S.phase == S.Failed))

fn client_close (c: connection) (ch: IO.channel)
  requires connection_exactly c 'st 's 'view0 **
          IO.is_channel ch **
          pure ('s.S.phase == S.ApplicationData)
  ensures exists* s' view1. connection_exactly c 'st s' view1 **
          IO.is_channel ch **
          pure (CL.connection_view_single_step 'view0 view1 /\
                (exists resp. CL.step 'view0 (CL.request_no_network_in CL.OpClose) view1 resp) /\
                (s'.S.phase == S.Closing \/ s'.S.phase == S.Failed))

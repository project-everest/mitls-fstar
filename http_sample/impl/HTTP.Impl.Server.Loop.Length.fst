module HTTP.Impl.Server.Loop.Length

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** HTTP/1.1 *Content-Length delimited* server-send
  driver — the Length-framing companion of HTTP.Impl.Server.Loop.http_server_run.

  For a Content-Length body there is no on-wire framing around the payload: the
  body is sent verbatim (its length is agreed out of band, exactly as TFTP's
  DATA payload length is).  `http_server_run_length` frames the file body through
  the verified codec leaf `HTTP.Impl.Codec.Length.http_emit_body` into a staging
  buffer, pushes it over the connected `Common.TCP` channel, and closes.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ    = FStar.SizeT
module Seq   = FStar.Seq
module TCP   = Common.TCP
module U8    = FStar.UInt8
module Codec = HTTP.Impl.Codec.Length

open HTTP.Wire.Length
open Pulse.Lib.BoundedIntegers

(* Send a whole file body over `ch` as a Content-Length delimited segment, then
   close the channel.  `scratch` (file_len bytes) stages the body; `body_ok`
   guarantees the segment cannot be confused with a request/response line. *)
fn http_server_run_length
  (ch: TCP.channel)
  (file: array U8.t)
  (file_len: SZ.t)
  (scratch: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to file 'f **
    pts_to scratch 's **
    pure (Seq.length 'f == SZ.v file_len /\
          Seq.length 's == SZ.v file_len /\
          body_ok 'f)
  ensures
    pts_to file 'f **
    (exists* (s':Seq.seq U8.t).
       pts_to scratch s')
{
  Codec.http_emit_body file file_len scratch;
  let n1 = TCP.write ch scratch file_len;
  TCP.close ch;
  ()
}

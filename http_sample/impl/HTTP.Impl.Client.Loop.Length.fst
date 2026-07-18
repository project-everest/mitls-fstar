module HTTP.Impl.Client.Loop.Length

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** HTTP/1.1 *Content-Length delimited* client
  receive driver — the verified counterpart of
  HTTP.Impl.Server.Loop.Length.http_server_run_length.

  `http_client_run_length` reads the agreed-length body segment off a connected
  `Common.TCP` channel (a single `read_full` of `flen` bytes) and hands it to the
  verified receive codec leaf `HTTP.Impl.Codec.Length.http_recv_body`, which
  copies it into `out` and reports `body_ok`.  When it returns `true`, `out` is
  exactly the payload the spec parser `http_parse` decodes to `Msg_body`.

  As with the chunked slice, the body length `flen` is agreed by both peers out
  of band (mirroring how the TFTP vloop harness hands `nblocks`/`flen` to both
  sides); for a real Content-Length exchange this value comes from the response
  head's `Content-Length` field.
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

(* Receive one Content-Length body segment of the agreed length `flen` over `ch`.
   `body` (flen bytes) stages the raw payload and `out` (flen bytes) receives the
   decoded body.  Returns whether the segment is `body_ok`; on success `out`
   corresponds to the spec parse `http_parse out == Some (Msg_body out, empty)`. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_client_run_length
  (ch: TCP.channel)
  (body: array U8.t)
  (out: array U8.t)
  (flen: SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 'b == SZ.v flen /\ Seq.length 'o == SZ.v flen)
  returns ok: bool
  ensures
    (exists* (rcv snt:TCP.bytes) (bb o':Seq.seq U8.t).
       TCP.is_channel ch rcv snt **
       pts_to body bb ** pts_to out o' **
       pure (Seq.length o' == SZ.v flen /\
             (ok == true ==>
                (body_ok o' /\
                 http_parse o' == Some (Msg_body o', Seq.empty #U8.t)))))
{
  let _n1 = TCP.read_full ch body flen;
  let ok = Codec.http_recv_body body out flen;
  ok
}
#pop-options

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
module U16   = FStar.UInt16
module U32   = FStar.UInt32
module R     = Pulse.Lib.Reference
module W     = HTTP.Wire.Common
module Codec = HTTP.Impl.Codec.Length

open HTTP.Wire.Length

open FStar.SizeT { (+), (-), ( * ), (/), (%), (<), (<=), (>), (>=) }
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

(* Full Content-Length *exchange* send driver: emit the 43-byte response head
   (status `code`, Content-Length `file_len`) via the verified codec leaf
   `http_emit_response`, push it, then send the body verbatim and close.  The
   companion `http_client_run_length_full` reads the head to learn the length. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_server_run_length_full
  (ch: TCP.channel)
  (code: U16.t)
  (file: array U8.t)
  (file_len: SZ.t)
  (headbuf: array U8.t)
  (scratch: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to file 'f **
    pts_to headbuf 'hb **
    pts_to scratch 's **
    pure (Seq.length 'f == SZ.v file_len /\
          Seq.length 'hb == 43 /\
          Seq.length 's == SZ.v file_len /\
          body_ok 'f /\
          Prims.op_Less_Equals 100 (U16.v code) /\
          Prims.op_Less (U16.v code) 1000 /\
          Prims.op_Less (SZ.v file_len) W.max_len8)
  ensures
    pts_to file 'f **
    (exists* (hb' s':Seq.seq U8.t).
       pts_to headbuf hb' ** pts_to scratch s')
{
  let flen32 = SZ.sizet_to_uint32 file_len;
  Codec.http_emit_response code flen32 headbuf;
  let nh = TCP.write ch headbuf 43sz;
  Codec.http_emit_body file file_len scratch;
  let nb = TCP.write ch scratch file_len;
  TCP.close ch;
  ()
}
#pop-options

(* Variable-width Content-Length send driver: identical to
   `http_server_run_length_full` but emits the RFC-canonical *minimal-width*
   Content-Length (e.g. "Content-Length: 25" rather than the fixed
   "Content-Length: 00000025").  The head is `35 + dec_width file_len` bytes,
   emitted through the verified leaf `Codec.http_emit_response_var` (proved equal
   to `ser_response_var`), then the body follows verbatim.  This is what a
   real-world origin server sends and what ordinary clients (curl, browsers)
   expect on the wire. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_server_run_length_var
  (ch: TCP.channel)
  (code: U16.t)
  (file: array U8.t)
  (file_len: SZ.t)
  (headbuf: array U8.t)
  (scratch: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to file 'f **
    pts_to headbuf 'hb **
    pts_to scratch 's **
    pure (Seq.length 'f == SZ.v file_len /\
          Seq.length 'hb == Prims.op_Plus 35 (Codec.dec_width (SZ.v file_len)) /\
          Seq.length 's == SZ.v file_len /\
          body_ok 'f /\
          Prims.op_Less_Equals 100 (U16.v code) /\
          Prims.op_Less (U16.v code) 1000 /\
          Prims.op_Less (SZ.v file_len) W.max_len8)
  ensures
    pts_to file 'f **
    (exists* (hb' s':Seq.seq U8.t).
       pts_to headbuf hb' ** pts_to scratch s')
{
  let flen32 = SZ.sizet_to_uint32 file_len;
  Codec.http_emit_response_var code flen32 headbuf;
  Codec.lemma_dec_width_u32_le10 flen32;
  let hlen = SZ.add 35sz (Codec.dec_width_u32 flen32);
  let nh = TCP.write ch headbuf hlen;
  Codec.http_emit_body file file_len scratch;
  let nb = TCP.write ch scratch file_len;
  TCP.close ch;
  ()
}
#pop-options

(* Full Content-Length request/response *round trip* (server side): read the
   `reqlen`-byte request head, parse it via the verified codec leaf
   `http_recv_request` to recover the request target (its length reported in
   `ptlen`), then send the response head+body exactly as
   `http_server_run_length_full` does, closing the channel.  On `okr` the received
   request bytes parse to `Msg_request tk` with `tk` the recovered target slice. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_server_exchange_length
  (ch: TCP.channel)
  (reqbuf: array U8.t)
  (reqlen: SZ.t)
  (ptlen: R.ref SZ.t)
  (code: U16.t)
  (file: array U8.t)
  (file_len: SZ.t)
  (headbuf: array U8.t)
  (scratch: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to reqbuf 'rq ** R.pts_to ptlen 't0 **
    pts_to file 'f ** pts_to headbuf 'hb ** pts_to scratch 's **
    pure (Seq.length 'rq == SZ.v reqlen /\
          Seq.length 'f == SZ.v file_len /\
          Seq.length 'hb == 43 /\
          Seq.length 's == SZ.v file_len /\
          body_ok 'f /\
          Prims.op_Less_Equals 100 (U16.v code) /\
          Prims.op_Less (U16.v code) 1000 /\
          Prims.op_Less (SZ.v file_len) W.max_len8)
  returns okr: bool
  ensures
    pts_to file 'f **
    (exists* (rq' hb' s':Seq.seq U8.t) (tl:SZ.t).
       pts_to reqbuf rq' ** R.pts_to ptlen tl **
       pts_to headbuf hb' ** pts_to scratch s' **
       pure (okr == true ==>
         (exists (tk:W.token).
            Seq.length rq' == SZ.v reqlen /\
            Prims.op_Less_Equals (Prims.op_Plus 4 (SZ.v tl)) (SZ.v reqlen) /\
            (tk <: Seq.seq U8.t) == Seq.slice rq' 4 (Prims.op_Plus 4 (SZ.v tl)) /\
            http_parse rq' == Some (Msg_request tk, Seq.empty #U8.t))))
{
  let _nr = TCP.read_full ch reqbuf reqlen;
  let okr = Codec.http_recv_request reqbuf reqlen ptlen;
  http_server_run_length_full ch code file file_len headbuf scratch;
  okr
}
#pop-options

(* Full Content-Length request/response *round trip* accepting a REAL client's
   request head (curl, browsers): the caller has already drained `reqlen` request
   bytes into `reqbuf` (a header-bearing request line of a-priori-unknown length,
   so it is NOT read here via `read_full`), which the verified headers-tolerant
   codec leaf `http_recv_request_head` parses to recover the request target
   (length in `ptlen`); then the response head+body are sent exactly as
   `http_server_run_length_full` does, closing the channel.  On `okr` the received
   bytes match `parse_request_line` with `tk` the recovered target slice. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_server_exchange_length_head
  (ch: TCP.channel)
  (reqbuf: array U8.t)
  (reqlen: SZ.t)
  (ptlen: R.ref SZ.t)
  (code: U16.t)
  (file: array U8.t)
  (file_len: SZ.t)
  (headbuf: array U8.t)
  (scratch: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to reqbuf 'rq ** R.pts_to ptlen 't0 **
    pts_to file 'f ** pts_to headbuf 'hb ** pts_to scratch 's **
    pure (Seq.length 'rq == SZ.v reqlen /\
          Seq.length 'f == SZ.v file_len /\
          Seq.length 'hb == 43 /\
          Seq.length 's == SZ.v file_len /\
          body_ok 'f /\
          Prims.op_Less_Equals 100 (U16.v code) /\
          Prims.op_Less (U16.v code) 1000 /\
          Prims.op_Less (SZ.v file_len) W.max_len8)
  returns okr: bool
  ensures
    pts_to file 'f **
    (exists* (rq' hb' s':Seq.seq U8.t) (tl:SZ.t).
       pts_to reqbuf rq' ** R.pts_to ptlen tl **
       pts_to headbuf hb' ** pts_to scratch s' **
       pure (okr == true ==>
         (exists (tk:W.token).
            Seq.length rq' == SZ.v reqlen /\
            Prims.op_Less_Equals (Prims.op_Plus 4 (SZ.v tl)) (SZ.v reqlen) /\
            (tk <: Seq.seq U8.t) == Seq.slice rq' 4 (Prims.op_Plus 4 (SZ.v tl)) /\
            parse_request_line rq' == Some tk)))
{
  let okr = Codec.http_recv_request_head reqbuf reqlen ptlen;
  http_server_run_length_full ch code file file_len headbuf scratch;
  okr
}
#pop-options

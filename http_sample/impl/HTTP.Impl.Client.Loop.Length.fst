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
module U16   = FStar.UInt16
module U32   = FStar.UInt32
module R     = Pulse.Lib.Reference
module W     = HTTP.Wire.Common
module Codec = HTTP.Impl.Codec.Length

open HTTP.Wire.Length

let lemma_flen_fits (flen:SZ.t)
  : Lemma (requires SZ.v flen < W.max_len8) (ensures SZ.v flen < pow2 32)
  = assert_norm (W.max_len8 < pow2 32)


open FStar.SizeT { (+), (-), ( * ), (/), (%), (<), (<=), (>), (>=) }
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

(* Full Content-Length *exchange* receive driver: read the 43-byte response head,
   parse it via the verified codec leaf `http_recv_response` to recover the status
   `code` and Content-Length `len`, check that `len` equals the agreed buffer
   length `flen`, then read+decode the body.  On success the head bytes parse to
   `Msg_response code len`, `out` holds the body, and it parses to `Msg_body`. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_client_run_length_full
  (ch: TCP.channel)
  (headbuf: array U8.t)
  (pcode: R.ref U16.t)
  (plen: R.ref U32.t)
  (body: array U8.t)
  (out: array U8.t)
  (flen: SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to headbuf 'hb ** R.pts_to pcode 'c0 ** R.pts_to plen 'l0 **
    pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 'hb == 43 /\
          Seq.length 'b == SZ.v flen /\
          Seq.length 'o == SZ.v flen /\
          Prims.op_Less (SZ.v flen) W.max_len8)
  returns ok: bool
  ensures
    (exists* (rcv snt:TCP.bytes) (hb' bb o':Seq.seq U8.t) (cv:U16.t) (lv:U32.t).
       TCP.is_channel ch rcv snt **
       pts_to headbuf hb' ** R.pts_to pcode cv ** R.pts_to plen lv **
       pts_to body bb ** pts_to out o' **
       pure (Seq.length o' == SZ.v flen /\
             (ok == true ==>
                (Prims.op_Less_Equals 100 (U16.v cv) /\
                 Prims.op_Less (U16.v cv) 1000 /\
                 Prims.op_Less (U32.v lv) W.max_len8 /\
                 Prims.op_Equals #nat (U32.v lv) (SZ.v flen) /\
                 http_parse hb' == Some (Msg_response cv (U32.v lv), Seq.empty #U8.t) /\
                 body_ok o' /\
                 http_parse o' == Some (Msg_body o', Seq.empty #U8.t)))))
{
  let _nh = TCP.read_full ch headbuf 43sz;
  let okh = Codec.http_recv_response headbuf pcode plen;
  if okh {
    let lv = !plen;
    let flen32 = SZ.sizet_to_uint32 flen;
    lemma_flen_fits flen;
    if U32.eq lv flen32 {
      let _nb = TCP.read_full ch body flen;
      let okb = Codec.http_recv_body body out flen;
      (* Pin the postcondition's pure conjuncts one at a time.  Every one of them
         is immediate from `http_recv_response`'s and `http_recv_body`'s
         contracts, but discharging the whole seven-witness existential in a
         single query costs more than rlimit 100 under Z3 4.15.3. *)
      with o'. assert (pts_to out o');
      assert (pure (Seq.length o' == SZ.v flen));
      assert (pure (U32.v lv == SZ.v flen));
      assert (pure (okb == true ==> body_ok o'));
      assert (pure (okb == true ==>
                    http_parse o' == Some (Msg_body o', Seq.empty #U8.t)));
      okb
    } else {
      false
    }
  } else {
    false
  }
}
#pop-options

(* Full Content-Length request/response *round trip* (client side): emit a
   `GET <target> HTTP/1.1...` request head via the verified codec leaf
   `http_emit_request`, send it, then receive the response head+body exactly as
   `http_client_run_length_full` does (parse the head to learn the length, check
   it against `flen`, read+decode the body).  On success `out` holds the response
   body and the head/body parse facts hold, mirroring `http_client_run_length_full`. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_client_exchange_length
  (ch: TCP.channel)
  (target: array U8.t)
  (target_len: SZ.t)
  (reqbuf: array U8.t)
  (headbuf: array U8.t)
  (pcode: R.ref U16.t)
  (plen: R.ref U32.t)
  (body: array U8.t)
  (out: array U8.t)
  (flen: SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to target 't ** pts_to reqbuf 'rq **
    pts_to headbuf 'hb ** R.pts_to pcode 'c0 ** R.pts_to plen 'l0 **
    pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 't == SZ.v target_len /\ W.space_free 't /\
          SZ.v target_len + 17 < pow2 32 /\
          Seq.length 'rq == 4 + SZ.v target_len + 13 /\
          Seq.length 'hb == 43 /\
          Seq.length 'b == SZ.v flen /\
          Seq.length 'o == SZ.v flen /\
          Prims.op_Less (SZ.v flen) W.max_len8)
  returns ok: bool
  ensures
    pts_to target 't **
    (exists* (rcv snt:TCP.bytes) (rq' hb' bb o':Seq.seq U8.t) (cv:U16.t) (lv:U32.t).
       TCP.is_channel ch rcv snt **
       pts_to reqbuf rq' ** pts_to headbuf hb' **
       R.pts_to pcode cv ** R.pts_to plen lv **
       pts_to body bb ** pts_to out o' **
       pure (Seq.length o' == SZ.v flen /\
             (ok == true ==>
                (Prims.op_Less_Equals 100 (U16.v cv) /\
                 Prims.op_Less (U16.v cv) 1000 /\
                 Prims.op_Less (U32.v lv) W.max_len8 /\
                 Prims.op_Equals #nat (U32.v lv) (SZ.v flen) /\
                 http_parse hb' == Some (Msg_response cv (U32.v lv), Seq.empty #U8.t) /\
                 body_ok o' /\
                 http_parse o' == Some (Msg_body o', Seq.empty #U8.t)))))
{
  Codec.http_emit_request target target_len reqbuf;
  Codec.lemma_fits32 (Prims.op_Plus 4 (SZ.v target_len));
  Codec.lemma_fits32 (Prims.op_Plus (Prims.op_Plus 4 (SZ.v target_len)) 13);
  let rlen = SZ.add (SZ.add 4sz target_len) 13sz;
  let _nw = TCP.write ch reqbuf rlen;
  let ok = http_client_run_length_full ch headbuf pcode plen body out flen;
  ok
}
#pop-options

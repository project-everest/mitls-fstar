module HTTP.Impl.Client.Loop.Get

#lang-pulse

(**
  A verified, Low*-extractable HTTP/1.1 client driver for a *real* origin-server
  GET (e.g. GET http://example.com/ over port 80).  It composes three already
  verified leaves over a connected `Common.TCP` channel:

    1. HTTP.Impl.Codec.Request.http_emit_request_host — build+send the request
       "GET <target> HTTP/1.1\r\nHost: <host>\r\nConnection: close\r\n\r\n";
    2. `recv_to_eof` (below) — because we ask the server to close the connection
       (`Connection: close`), read the entire response into `buf` until EOF;
    3. HTTP.Impl.Codec.Response.http_parse_response_head — parse the accumulated
       head to recover the status code and the body framing (Content-Length /
       chunked / read-to-EOF).

  The response-head scanner stops at the CRLF-CRLF terminator, so passing it the
  whole received buffer (head + body) is correct; the body then occupies
  `buf[headlen .. rlen)` (the caller can locate it with the same terminator).

  Everything here is proved memory-safe by the Pulse VC; on success we further
  carry the status-line fact `code == W.dec_dec3` of the three code bytes.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Common.TCP
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module R    = Pulse.Lib.Reference
module W    = HTTP.Wire.Common
module Req  = HTTP.Impl.Codec.Request
module Resp = HTTP.Impl.Codec.Response
module CS   = HTTP.Impl.Codec.Chunked.Stream

(* Read the whole response off `ch` into `buf` (capacity `cap`) until the peer
   closes (read returns 0) or `buf` fills.  `tmp` (capacity `tmpcap > 0`) stages
   each read.  On return `prlen` holds the total number of bytes received
   (<= cap).  Memory-safe. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn recv_to_eof
  (ch: TCP.channel)
  (buf: array U8.t) (cap: SZ.t)
  (tmp: array U8.t) (tmpcap: SZ.t)
  (prlen: R.ref SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to buf 'b ** pts_to tmp 't ** R.pts_to prlen 'l0 **
    pure (Seq.length 'b == SZ.v cap /\ Seq.length 't == SZ.v tmpcap /\ 0 < SZ.v tmpcap)
  ensures
    (exists* (rcv snt:TCP.bytes) (bv tv:Seq.seq U8.t) (rl:SZ.t).
       TCP.is_channel ch rcv snt **
       pts_to buf bv ** pts_to tmp tv ** R.pts_to prlen rl **
       pure (Seq.length bv == SZ.v cap /\ SZ.v rl <= SZ.v cap))
{
  prlen := 0sz;
  let mut go = true;
  while (!go)
  invariant exists* (rcv snt:TCP.bytes) (bv tv:Seq.seq U8.t) (rl:SZ.t) (vg:bool).
    TCP.is_channel ch rcv snt **
    pts_to buf bv ** pts_to tmp tv ** R.pts_to prlen rl ** R.pts_to go vg **
    pure (Seq.length bv == SZ.v cap /\ Seq.length tv == SZ.v tmpcap /\
          0 < SZ.v tmpcap /\ SZ.v rl <= SZ.v cap)
  {
    let rl = !prlen;
    if SZ.lt rl cap {
      let nread = TCP.read ch tmp tmpcap;
      if SZ.eq nread 0sz {
        go := false;
      } else {
        let room : SZ.t = SZ.sub cap rl;
        let ncopy : SZ.t = if SZ.lt room nread { room } else { nread };
        (* copy tmp[0 .. ncopy) into buf[rl .. rl+ncopy) *)
        with bvold. assert (pts_to buf bvold);
        let mut k = 0sz;
        while (SZ.lt !k ncopy)
        invariant exists* (vk:SZ.t) (bv tv:Seq.seq U8.t).
          R.pts_to k vk ** pts_to buf bv ** pts_to tmp tv **
          pure (SZ.v vk <= SZ.v ncopy /\ Seq.length bv == SZ.v cap /\
                Seq.length tv == SZ.v tmpcap /\
                SZ.v ncopy <= SZ.v tmpcap /\
                SZ.v rl + SZ.v ncopy <= SZ.v cap)
        {
          let vk = !k;
          let dv = tmp.(vk);
          buf.(SZ.add rl vk) <- dv;
          k := SZ.add vk 1sz;
        };
        prlen := SZ.add rl ncopy;
        if SZ.lt ncopy nread { go := false }
      }
    } else {
      go := false;
    }
  }
}
#pop-options

(* Perform a full GET over a connected channel `ch`:
     * emit "GET <target> HTTP/1.1\r\nHost: <host>\r\nConnection: close\r\n\r\n"
       into `reqbuf` (which must be exactly 4 + target_len + 17 + host_len + 23
       bytes) and send it;
     * read the whole response into `buf` (capacity `cap`), staging through
       `tmp`, until the server closes the connection;
     * parse the accumulated head, recovering the status code (`pcode`), the
       body framing signals (`pchunked`, `phas_cl`) and Content-Length (`pcl`).
   `prlen` reports how many bytes were received.  Returns `ok` = the response
   head parsed and its CRLF-CRLF terminator was found; on success the status
   code equals `W.dec_dec3` of the head's three code bytes.  Memory-safe. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_get
  (ch: TCP.channel)
  (target: array U8.t) (target_len: SZ.t)
  (host: array U8.t) (host_len: SZ.t)
  (reqbuf: array U8.t)
  (buf: array U8.t) (cap: SZ.t)
  (tmp: array U8.t) (tmpcap: SZ.t)
  (prlen: R.ref SZ.t)
  (pcode: R.ref U16.t) (pchunked: R.ref bool) (phas_cl: R.ref bool) (pcl: R.ref U32.t)
  (phead: R.ref SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to target 't ** pts_to host 'hst ** pts_to reqbuf 'rq **
    pts_to buf 'b ** pts_to tmp 'tm ** R.pts_to prlen 'l0 **
    R.pts_to pcode 'c0 ** R.pts_to pchunked 'ch0 **
    R.pts_to phas_cl 'hc0 ** R.pts_to pcl 'cl0 ** R.pts_to phead 'hd0 **
    pure (Seq.length 't == SZ.v target_len /\ Seq.length 'hst == SZ.v host_len /\
          W.space_free 't /\ W.space_free 'hst /\
          SZ.v target_len + SZ.v host_len + 44 < pow2 32 /\
          Seq.length 'rq == 4 + SZ.v target_len + 17 + SZ.v host_len + 23 /\
          Seq.length 'b == SZ.v cap /\ SZ.v cap + 18 < pow2 32 /\
          Seq.length 'tm == SZ.v tmpcap /\ 0 < SZ.v tmpcap)
  returns ok: bool
  ensures
    pts_to target 't ** pts_to host 'hst **
    (exists* (rcv snt:TCP.bytes) (rq' bv tv:Seq.seq U8.t) (rl:SZ.t)
             (code:U16.t) (chk hc:bool) (cl:U32.t) (hd:SZ.t).
       TCP.is_channel ch rcv snt **
       pts_to reqbuf rq' ** pts_to buf bv ** pts_to tmp tv **
       R.pts_to prlen rl ** R.pts_to pcode code ** R.pts_to pchunked chk **
       R.pts_to phas_cl hc ** R.pts_to pcl cl ** R.pts_to phead hd **
       pure (Seq.length bv == SZ.v cap /\ SZ.v rl <= SZ.v cap /\ U32.v cl < W.max_len8 /\
             (ok == true ==>
               (13 <= SZ.v rl /\ SZ.v rl <= SZ.v cap /\ SZ.v hd <= SZ.v rl /\
                Seq.length bv == SZ.v cap /\
                100 <= U16.v code /\ U16.v code < 1000 /\
                W.dec3_ok (Seq.slice bv 9 12) /\
                Prims.op_Equality #nat (U16.v code) (W.dec_dec3 (Seq.slice bv 9 12))))))
{
  Req.http_emit_request_host target target_len host host_len reqbuf;
  Resp.lemma_fits32 (4 + SZ.v target_len);
  Resp.lemma_fits32 (4 + SZ.v target_len + 17);
  Resp.lemma_fits32 (4 + SZ.v target_len + 17 + SZ.v host_len);
  Resp.lemma_fits32 (4 + SZ.v target_len + 17 + SZ.v host_len + 23);
  let rlen_req = SZ.add (SZ.add (SZ.add (SZ.add 4sz target_len) 17sz) host_len) 23sz;
  let _nw = TCP.write ch reqbuf rlen_req;
  recv_to_eof ch buf cap tmp tmpcap prlen;
  let rl = !prlen;
  let ok = Resp.http_parse_response_head buf rl pcode pchunked phas_cl pcl phead;
  ok
}
#pop-options

(* Decode a chunked response body.  After `http_get` reports `pchunked == true`,
   the raw chunk-framed body occupies `buf[headlen .. rlen)`.  This copies that
   span down to a zero-based staging array `raw` and runs the verified chunked
   stream decoder `HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks`, writing
   the reassembled payload into `out` and its length into `poutlen`.  Returns
   the decoder's `ok` (the chunk stream was well-formed and terminated by a
   0-size last chunk).  Memory-safe; on success `poutlen <= outcap`. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_get_body_chunked
  (buf: array U8.t) (headlen: SZ.t) (rlen: SZ.t)
  (raw: array U8.t) (rawcap: SZ.t)
  (out: array U8.t) (outcap: SZ.t)
  (poutlen: R.ref SZ.t)
  requires
    pts_to buf 'b ** pts_to raw 'r ** pts_to out 'o ** R.pts_to poutlen 'l0 **
    pure (SZ.v headlen <= SZ.v rlen /\ SZ.v rlen <= Seq.length 'b /\
          SZ.v rlen - SZ.v headlen <= SZ.v rawcap /\
          Seq.length 'r == SZ.v rawcap /\ SZ.v rawcap < pow2 32 /\
          Seq.length 'o == SZ.v outcap /\ SZ.v outcap < pow2 32)
  returns ok: bool
  ensures
    pts_to buf 'b **
    (exists* (rv:Seq.seq U8.t) (ov:Seq.seq U8.t) (vo:SZ.t).
       pts_to raw rv ** pts_to out ov ** R.pts_to poutlen vo **
       pure (Seq.length rv == SZ.v rawcap /\ Seq.length ov == SZ.v outcap /\
             (ok == true ==> SZ.v vo <= SZ.v outcap)))
{
  let bodylen = SZ.sub rlen headlen;
  (* copy buf[headlen .. rlen) into raw[0 .. bodylen) *)
  let mut k = 0sz;
  while (SZ.lt !k bodylen)
  invariant exists* (vk:SZ.t) (rv:Seq.seq U8.t).
    R.pts_to k vk ** pts_to buf 'b ** pts_to raw rv **
    pure (SZ.v vk <= SZ.v bodylen /\ Seq.length rv == SZ.v rawcap /\
          SZ.v bodylen <= SZ.v rawcap /\ SZ.v headlen + SZ.v bodylen <= Seq.length 'b)
  {
    let vk = !k;
    let dv = buf.(SZ.add headlen vk);
    raw.(vk) <- dv;
    k := SZ.add vk 1sz;
  };
  let ok = CS.http_decode_chunks raw bodylen out outcap poutlen;
  ok
}
#pop-options

(* Like `http_get_body_chunked`, but uses the variable-width (RFC 9112) chunk
   decoder `HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks_var`, which parses
   a minimal-width hex chunk size as emitted by real origin servers (e.g.
   "1cf\r\n").  Memory-safe; on success `poutlen <= outcap`.  (This carries only
   a memory-safety contract, not the fixed-width parse_chunks spec relation.) *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_get_body_chunked_var
  (buf: array U8.t) (headlen: SZ.t) (rlen: SZ.t)
  (raw: array U8.t) (rawcap: SZ.t)
  (out: array U8.t) (outcap: SZ.t)
  (poutlen: R.ref SZ.t)
  requires
    pts_to buf 'b ** pts_to raw 'r ** pts_to out 'o ** R.pts_to poutlen 'l0 **
    pure (SZ.v headlen <= SZ.v rlen /\ SZ.v rlen <= Seq.length 'b /\
          SZ.v rlen - SZ.v headlen <= SZ.v rawcap /\
          Seq.length 'r == SZ.v rawcap /\ SZ.v rawcap < pow2 32 /\
          Seq.length 'o == SZ.v outcap /\ SZ.v outcap < pow2 32)
  returns ok: bool
  ensures
    pts_to buf 'b **
    (exists* (rv:Seq.seq U8.t) (ov:Seq.seq U8.t) (vo:SZ.t).
       pts_to raw rv ** pts_to out ov ** R.pts_to poutlen vo **
       pure (Seq.length rv == SZ.v rawcap /\ Seq.length ov == SZ.v outcap /\
             (ok == true ==> SZ.v vo <= SZ.v outcap)))
{
  let bodylen = SZ.sub rlen headlen;
  (* copy buf[headlen .. rlen) into raw[0 .. bodylen) *)
  let mut k = 0sz;
  while (SZ.lt !k bodylen)
  invariant exists* (vk:SZ.t) (rv:Seq.seq U8.t).
    R.pts_to k vk ** pts_to buf 'b ** pts_to raw rv **
    pure (SZ.v vk <= SZ.v bodylen /\ Seq.length rv == SZ.v rawcap /\
          SZ.v bodylen <= SZ.v rawcap /\ SZ.v headlen + SZ.v bodylen <= Seq.length 'b)
  {
    let vk = !k;
    let dv = buf.(SZ.add headlen vk);
    raw.(vk) <- dv;
    k := SZ.add vk 1sz;
  };
  let ok = CS.http_decode_chunks_var raw bodylen out outcap poutlen;
  ok
}
#pop-options

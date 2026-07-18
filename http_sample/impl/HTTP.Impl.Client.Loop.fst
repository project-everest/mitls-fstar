module HTTP.Impl.Client.Loop

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** HTTP/1.1 *chunked* client receive driver — the
  verified counterpart of HTTP.Impl.Server.Loop.http_server_run.

  `http_client_run` reads one HTTP chunk (header + body) off a connected
  `Common.TCP` channel, using the verified receive codec leaves
  (`http_peek_chunk_size` to decode the size header, then `http_recv_chunk` to
  copy + validate the body).  When it returns `true`, the copied output `out` is
  exactly the payload of the chunk the spec parser `http_parse` decodes from the
  header++body bytes.

  Like the server slice this is the single-chunk vertical slice: the transfer is
  one data chunk carrying the whole (<= 65535-byte) body, so the caller supplies
  the expected payload length `flen` (both peers agree on it, exactly as the TFTP
  vloop harness hands `nblocks`/`flen` to both sides).  Framing that needs a
  streaming reassembly over many chunks (offset writes into one buffer) is left
  to the full driver.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ    = FStar.SizeT
module Seq   = FStar.Seq
module TCP   = Common.TCP
module U8    = FStar.UInt8
module U16   = FStar.UInt16
module Codec = HTTP.Impl.Codec.Chunked
module W     = HTTP.Wire.Common

open HTTP.Wire.Chunked
open Pulse.Lib.BoundedIntegers

(* Receive one chunk (of the agreed length `flen`) over `ch`.  `hdr` (6 bytes)
   stages the size header, `body` (flen+2 bytes) the payload plus its CRLF, and
   `out` (flen bytes) receives the decoded payload.  Returns whether the chunk
   was well-formed and matched the expected length; on success `out` corresponds
   to the spec parse of the received frame.  (The RFC last-chunk terminator that
   the sender writes next is not drained here — the agreed `flen` delimits the
   body and the sender closes the channel afterwards.) *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
fn http_client_run
  (ch: TCP.channel)
  (hdr: array U8.t)
  (body: array U8.t)
  (out: array U8.t)
  (flen: SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to hdr 'h ** pts_to body 'b ** pts_to out 'o **
    pure (Seq.length 'h == 6 /\ Seq.length 'b == SZ.v flen + 2 /\
          Seq.length 'o == SZ.v flen /\ SZ.v flen <= 65535)
  returns ok: bool
  ensures
    (exists* (rcv snt:TCP.bytes) (hh bb o':Seq.seq U8.t).
       TCP.is_channel ch rcv snt **
       pts_to hdr hh ** pts_to body bb ** pts_to out o' **
       pure (Seq.length o' == SZ.v flen /\
             (ok == true ==>
                (SZ.v flen <= 65535 /\
                 http_parse (Seq.append hh bb) ==
                   Some (Msg_chunk o', Seq.empty #U8.t)))))
{
  let _n1 = TCP.read_full ch hdr 6sz;
  let pr = Codec.http_peek_chunk_size hdr;
  let (okh, n16) = pr;
  let nn = SZ.uint16_to_sizet n16;
  if (okh && SZ.eq nn flen) {
    Codec.lemma_fits32 (SZ.v flen + 2);
    let _n2 = TCP.read_full ch body (SZ.add flen 2sz);
    let crlf_ok = Codec.http_recv_chunk hdr body out flen;
    crlf_ok
  } else {
    false
  }
}
#pop-options

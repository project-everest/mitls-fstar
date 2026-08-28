module HTTP.Impl.Server.Loop

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** HTTP/1.1 *chunked* server-send driver.

  This is the "thin vertical slice": a verified Pulse loop that reuses the
  committed codec leaves (`HTTP.Impl.Codec.Chunked.http_emit_chunk` and
  `http_emit_empty_chunk`) and the verified `Common.TCP` socket interface to
  push a file body over a connected channel as a single HTTP chunk followed by
  the RFC last-chunk terminator, then closes the channel.

  Unlike the full TFTP framework loop (CanonicalProtocol / Log / Plan / ARQ
  coupling), this driver carries no protocol-state machine: it demonstrates the
  end-to-end pipeline (verify -> extract -> C -> interop) over the verified
  codec + verified TCP, which is exactly what the vertical slice needs to prove.

  The one HTTP chunk is `hex4(len) CRLF <file> CRLF`; the terminator is the
  empty chunk `"0000" CRLF CRLF`.  A receiver that understands chunked framing
  reconstructs the file and stops at the empty chunk.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ    = FStar.SizeT
module Seq   = FStar.Seq
module TCP   = Common.TCP
module U8    = FStar.UInt8
module A     = Pulse.Lib.Array
module W     = HTTP.Wire.Common
module Codec = HTTP.Impl.Codec.Chunked


open FStar.SizeT { (+), (-), ( * ), (/), (%), (<), (<=), (>), (>=) }
(* size_t is at least 32 bits on every real target, so any value below 2^32
   fits.  HTTP chunk lengths reach 8+65535 = 65543, which crosses F*'s SizeT
   2^16 auto-`fits` line, so we discharge it explicitly (same open assumption as
   the codec module). *)
let lemma_fits32 (x:nat)
  : Lemma (requires x < pow2 32) (ensures FStar.SizeT.fits x)
  = assume (FStar.SizeT.fits_u32);
    FStar.SizeT.fits_u32_implies_fits x

(* Send a whole (<=65535-byte) file body over `ch` as one HTTP chunk plus the
   RFC empty last-chunk, then close the channel.

   `scratch` is an (8 + file_len)-byte staging buffer for the data chunk;
   `term` is a dedicated 8-byte buffer for the terminator.  Both are supplied by
   the caller so the driver performs no heap allocation. *)
fn http_server_run
  (ch: TCP.channel)
  (file: array U8.t)
  (file_len: SZ.t)
  (scratch: array U8.t)
  (term: array U8.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to file 'f **
    pts_to scratch 's **
    pts_to term 't **
    pure (Seq.length 'f == SZ.v file_len /\
          SZ.v file_len <= 65535 /\
          Seq.length 's == 8 + SZ.v file_len /\
          Seq.length 't == 8)
  ensures
    pts_to file 'f **
    (exists* (s':Seq.seq U8.t) (t':Seq.seq U8.t).
       pts_to scratch s' **
       pts_to term t')
{
  (* Frame the data chunk into `scratch` and push it. *)
  Codec.http_emit_chunk file file_len scratch;
  lemma_fits32 (8 + SZ.v file_len);
  let n1 = TCP.write ch scratch (8sz + file_len);
  (* Frame the terminating empty chunk and push it. *)
  Codec.http_emit_empty_chunk term;
  let n2 = TCP.write ch term 8sz;
  TCP.close ch;
  ()
}

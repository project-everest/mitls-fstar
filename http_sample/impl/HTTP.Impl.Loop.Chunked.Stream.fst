module HTTP.Impl.Loop.Chunked.Stream

#lang-pulse

(**
  A minimal, **Low*-EXTRACTABLE** HTTP/1.1 *chunked streaming* driver pair over
  `Common.TCP`, composing the verified in-buffer reassembler
  `HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks`.

  The encoded stream length is agreed out of band (exactly as the single-chunk
  vloop harness hands `flen`/`nblocks` to both peers):

    * `http_server_send_stream` writes an already-built encoded chunk stream
      (many `hhhh CRLF data CRLF` frames + the `0000 CRLF CRLF` terminator) and
      closes the channel;
    * `http_client_recv_stream` reads the whole `enclen`-byte stream off the
      channel and reassembles it with `http_decode_chunks`.  On success the
      first `off` bytes of `out` are exactly `parse_chunks` of the received
      bytes, i.e. the concatenation of every chunk payload up to the terminator.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ     = FStar.SizeT
module Seq    = FStar.Seq
module TCP    = Common.TCP
module U8     = FStar.UInt8
module R      = Pulse.Lib.Reference
module Stream = HTTP.Impl.Codec.Chunked.Stream
module S      = HTTP.Wire.Chunked.Stream

(* Send a pre-built encoded chunk stream and close. *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
fn http_server_send_stream (ch: TCP.channel) (buf: array U8.t) (enclen: SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to buf 'b **
    pure (SZ.v enclen <= Seq.length 'b)
  ensures
    pts_to buf 'b
{
  let _n = TCP.write ch buf enclen;
  TCP.close ch;
}
#pop-options

(* Read the agreed `enclen`-byte encoded stream and reassemble it. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
fn http_client_recv_stream
    (ch: TCP.channel)
    (inp: array U8.t) (enclen: SZ.t)
    (out: array U8.t) (outcap: SZ.t)
    (poff: R.ref SZ.t)
  requires
    TCP.is_channel ch 'received 'sent **
    pts_to inp 'i ** pts_to out 'o ** R.pts_to poff 'po **
    pure (Seq.length 'i == SZ.v enclen /\ Seq.length 'o == SZ.v outcap /\
          SZ.v enclen < pow2 32 /\ SZ.v outcap < pow2 32)
  returns ok: bool
  ensures
    (exists* (rcv snt:TCP.bytes) (iv ov:Seq.seq U8.t) (vo:SZ.t).
       TCP.is_channel ch rcv snt **
       pts_to inp iv ** pts_to out ov ** R.pts_to poff vo **
       pure (Seq.length ov == SZ.v outcap /\ Seq.length iv == SZ.v enclen /\
             (ok == true ==>
                (SZ.v vo <= SZ.v outcap /\
                 (exists (rest:Seq.seq U8.t).
                    S.parse_chunks (Seq.slice iv 0 (SZ.v enclen)) ==
                      Some (Seq.slice ov 0 (SZ.v vo), rest))))))
{
  let _n = TCP.read_full ch inp enclen;
  let ok = Stream.http_decode_chunks inp enclen out outcap poff;
  ok
}
#pop-options

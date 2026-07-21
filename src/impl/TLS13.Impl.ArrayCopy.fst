module TLS13.Impl.ArrayCopy

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module A = Pulse.Lib.Array
module B = TLS13.Bytes
module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn copy_prefix
  (len:SZ.t)
  (src:array U8.t)
  (src_len:SZ.t)
  (dst:array U8.t)
  (dst_len:SZ.t)
  requires pts_to src 'src_bytes **
           pts_to dst 'dst_bytes **
           pure (B.length 'src_bytes == SZ.v src_len /\
                 B.length 'dst_bytes == SZ.v dst_len /\
                 SZ.v len <= SZ.v src_len /\
                 SZ.v len <= SZ.v dst_len)
  ensures exists* dst_after.
          pts_to src 'src_bytes **
          pts_to dst dst_after **
          pure (B.length (Ghost.reveal 'src_bytes) == SZ.v src_len /\
                B.length (Ghost.reveal 'dst_bytes) == SZ.v dst_len /\
                B.length dst_after == SZ.v dst_len /\
                SZ.v len <= SZ.v src_len /\
                SZ.v len <= SZ.v dst_len /\
                Seq.equal
                  dst_after
                  (Seq.append
                    (Seq.slice (Ghost.reveal 'src_bytes) 0 (SZ.v len))
                    (Seq.slice
                      (Ghost.reveal 'dst_bytes)
                      (SZ.v len)
                      (SZ.v dst_len))) /\
                Seq.equal
                  (Seq.slice dst_after 0 (SZ.v len))
                  (Seq.slice (Ghost.reveal 'src_bytes) 0 (SZ.v len)))
{
  A.pts_to_len src;
  A.pts_to_len dst;
  let src_slice = S.from_array src src_len;
  let src_parts = S.split src_slice len;
  let dst_slice = S.from_array dst dst_len;
  let dst_parts = S.split dst_slice len;
  S.pts_to_len (fst src_parts);
  S.pts_to_len (fst dst_parts);
  S.copy (fst dst_parts) (fst src_parts);
  Seq.lemma_split (Ghost.reveal 'src_bytes) (SZ.v len);
  Seq.lemma_split (Ghost.reveal 'dst_bytes) (SZ.v len);
  S.join (fst src_parts) (snd src_parts) src_slice;
  S.to_array src_slice;
  S.join (fst dst_parts) (snd dst_parts) dst_slice;
  S.to_array dst_slice;
  with dst_after. assert (pts_to dst dst_after);
  assert (pure (Seq.equal
    dst_after
    (Seq.append
      (Seq.slice (Ghost.reveal 'src_bytes) 0 (SZ.v len))
      (Seq.slice (Ghost.reveal 'dst_bytes) (SZ.v len) (SZ.v dst_len)))));
  Seq.lemma_len_slice dst_after 0 (SZ.v len);
  Seq.lemma_len_slice (Ghost.reveal 'src_bytes) 0 (SZ.v len)
}

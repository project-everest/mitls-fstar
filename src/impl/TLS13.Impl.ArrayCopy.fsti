module TLS13.Impl.ArrayCopy

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
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

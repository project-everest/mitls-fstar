module TLS13.Impl.Server.Material

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module Slice = Pulse.Lib.Slice
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn copy_server_random_and_private_from_payload
  (payload:array U8.t)
  (server_random:array U8.t)
  (server_private_key:array U8.t)
  requires pts_to payload 'payload_bytes **
           pts_to server_random 'old_server_random **
           pts_to server_private_key 'old_server_private_key **
           pure (B.length 'payload_bytes == 64 /\
                 B.length 'old_server_random == 32 /\
                 B.length 'old_server_private_key == 32)
  ensures pts_to payload 'payload_bytes **
          pts_to server_random (CL.raw_slice 'payload_bytes 0 32) **
          pts_to server_private_key (CL.raw_slice 'payload_bytes 32 64) **
          pure (B.length (CL.raw_slice 'payload_bytes 0 32) == 32 /\
                B.length (CL.raw_slice 'payload_bytes 32 64) == 32)
{
  pts_to_len payload;
  pts_to_len server_random;
  pts_to_len server_private_key;

  let payload_slice = Slice.from_array payload 64sz;
  let payload_split = Slice.split payload_slice 32sz;
  let random_slice = Slice.from_array server_random 32sz;
  let private_slice = Slice.from_array server_private_key 32sz;

  Slice.pts_to_len (fst payload_split);
  Slice.pts_to_len (snd payload_split);
  Slice.pts_to_len random_slice;
  Slice.pts_to_len private_slice;
  assert (pure (Slice.len (fst payload_split) == 32sz));
  assert (pure (Slice.len (snd payload_split) == 32sz));
  assert (pure (Slice.len random_slice == 32sz));
  assert (pure (Slice.len private_slice == 32sz));

  Slice.copy random_slice (fst payload_split);
  Slice.copy private_slice (snd payload_split);

  Slice.to_array random_slice;
  Slice.to_array private_slice;
  Slice.join (fst payload_split) (snd payload_split) payload_slice;
  SeqP.lemma_split 'payload_bytes 32;
  Slice.to_array payload_slice;

  Seq.lemma_len_slice 'payload_bytes 0 32;
  Seq.lemma_len_slice 'payload_bytes 32 64;
  assert (pure (CL.raw_slice 'payload_bytes 0 32 == Seq.slice 'payload_bytes 0 32));
  assert (pure (CL.raw_slice 'payload_bytes 32 64 == Seq.slice 'payload_bytes 32 64))
}

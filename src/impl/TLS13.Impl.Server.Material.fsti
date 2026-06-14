module TLS13.Impl.Server.Material

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
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

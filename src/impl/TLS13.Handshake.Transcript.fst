module TLS13.Handshake.Transcript

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module E = TLS13.Handshake.Transcript.External
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn hash_client_server_handshake
  (client_hello: array U8.t)
  (client_hello_len: SZ.t)
  (server_hello: array U8.t)
  (server_hello_len: SZ.t)
  (server_handshake: array U8.t)
  (server_handshake_len: SZ.t)
  (out: array U8.t)
  requires pts_to client_hello 'client_hello_bytes **
           pts_to server_hello 'server_hello_bytes **
           pts_to server_handshake 'server_handshake_bytes **
           pts_to out 'old_out **
           pure (B.length 'client_hello_bytes == SZ.v client_hello_len /\
                 B.length 'server_hello_bytes == SZ.v server_hello_len /\
                 B.length 'server_handshake_bytes == SZ.v server_handshake_len /\
                 B.length 'old_out == 32 /\
                 SZ.v client_hello_len + SZ.v server_hello_len + SZ.v server_handshake_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to client_hello 'client_hello_bytes **
          pts_to server_hello 'server_hello_bytes **
          pts_to server_handshake 'server_handshake_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (B.append (B.append 'client_hello_bytes 'server_hello_bytes) 'server_handshake_bytes)))
{
  E.sha256_three
    client_hello client_hello_len
    server_hello server_hello_len
    server_handshake server_handshake_len
    out
}

fn equal32
  (a: array U8.t)
  (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns eq: bool
  ensures pts_to a 'a_bytes ** pts_to b 'b_bytes
{
  pts_to_len a;
  pts_to_len b;
  let a0 = a.(0sz); let b0 = b.(0sz);
  let a1 = a.(1sz); let b1 = b.(1sz);
  let a2 = a.(2sz); let b2 = b.(2sz);
  let a3 = a.(3sz); let b3 = b.(3sz);
  let a4 = a.(4sz); let b4 = b.(4sz);
  let a5 = a.(5sz); let b5 = b.(5sz);
  let a6 = a.(6sz); let b6 = b.(6sz);
  let a7 = a.(7sz); let b7 = b.(7sz);
  let a8 = a.(8sz); let b8 = b.(8sz);
  let a9 = a.(9sz); let b9 = b.(9sz);
  let a10 = a.(10sz); let b10 = b.(10sz);
  let a11 = a.(11sz); let b11 = b.(11sz);
  let a12 = a.(12sz); let b12 = b.(12sz);
  let a13 = a.(13sz); let b13 = b.(13sz);
  let a14 = a.(14sz); let b14 = b.(14sz);
  let a15 = a.(15sz); let b15 = b.(15sz);
  let a16 = a.(16sz); let b16 = b.(16sz);
  let a17 = a.(17sz); let b17 = b.(17sz);
  let a18 = a.(18sz); let b18 = b.(18sz);
  let a19 = a.(19sz); let b19 = b.(19sz);
  let a20 = a.(20sz); let b20 = b.(20sz);
  let a21 = a.(21sz); let b21 = b.(21sz);
  let a22 = a.(22sz); let b22 = b.(22sz);
  let a23 = a.(23sz); let b23 = b.(23sz);
  let a24 = a.(24sz); let b24 = b.(24sz);
  let a25 = a.(25sz); let b25 = b.(25sz);
  let a26 = a.(26sz); let b26 = b.(26sz);
  let a27 = a.(27sz); let b27 = b.(27sz);
  let a28 = a.(28sz); let b28 = b.(28sz);
  let a29 = a.(29sz); let b29 = b.(29sz);
  let a30 = a.(30sz); let b30 = b.(30sz);
  let a31 = a.(31sz); let b31 = b.(31sz);
  (a0 = b0) && (a1 = b1) && (a2 = b2) && (a3 = b3) &&
  (a4 = b4) && (a5 = b5) && (a6 = b6) && (a7 = b7) &&
  (a8 = b8) && (a9 = b9) && (a10 = b10) && (a11 = b11) &&
  (a12 = b12) && (a13 = b13) && (a14 = b14) && (a15 = b15) &&
  (a16 = b16) && (a17 = b17) && (a18 = b18) && (a19 = b19) &&
  (a20 = b20) && (a21 = b21) && (a22 = b22) && (a23 = b23) &&
  (a24 = b24) && (a25 = b25) && (a26 = b26) && (a27 = b27) &&
  (a28 = b28) && (a29 = b29) && (a30 = b30) && (a31 = b31)
}

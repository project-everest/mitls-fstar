module TLS13.Crypto.Random

(**
  The operating system's random-number generator: the one cryptographic
  binding that stays in C (see c_stubs/tls13_crypto_external.c).  Everything
  else in [TLS13.Crypto] is Pulse code calling hacl-pulse.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn random_bytes (out: array U8.t) (out_len: SZ.t)
  requires pts_to out 'old ** pure (Seq.length 'old == SZ.v out_len)
  returns ok: bool
  ensures exists* bytes. pts_to out bytes ** pure (Seq.length bytes == SZ.v out_len)

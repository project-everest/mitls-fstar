module TLS13.Crypto.Secret

#lang-pulse

open Pulse.Lib.Pervasives

friend Hacl.Secret.UInt8

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module SB = Spec.Byte

let classify_seq s = s

let declassify_seq s = s

let classify_index s i = ()

let declassify_index s i = ()

let declassify_classify s = ()

let classify_declassify s = ()

let classify_slice s i j = ()

let declassify_slice s i j = ()

let declassify_append s1 s2 = ()

inline_for_extraction
let secret a = a

let secret_length a = ()

ghost fn to_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq U8.t))
  requires A.pts_to a #p s
  ensures A.pts_to (secret a) #p (classify_seq s)
{
  rewrite A.pts_to a #p s as A.pts_to (secret a) #p (classify_seq s)
}

ghost fn of_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq S8.t))
  requires A.pts_to (secret a) #p s
  ensures A.pts_to a #p (declassify_seq s)
{
  rewrite A.pts_to (secret a) #p s as A.pts_to a #p (declassify_seq s)
}

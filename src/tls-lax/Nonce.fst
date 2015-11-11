(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Nonce
open FStar.Seq
open Platform.Bytes
open Platform.Error


let timestamp () = bytes_of_int 4 (Platform.Date.secondsFromDawn ())

val random: n:nat -> lbytes 32
let random (n:nat) =
  let r = CoreCrypto.random n in
  let l = length r in
  if l = n then r
  else unexpected "CoreCrypto.random returned incorrect number of bytes"

val noCsr: bytes
let noCsr = random 64 // a constant value, with negligible probability of being sampled, excluded by idealization

let log: ref (list bytes) = ref [empty_bytes]
(* TODO : fixme 
   We don't know what that does, MK & JK 
   let log_modified () = log := []
*)

val mkHelloRandom: unit -> lbytes 32
let rec mkHelloRandom(): bytes =
    let cr = timestamp() @| random 28 in
#if ideal
      if List.mem cr !log then  //KB makes this mem,  but we're not sure about it
        mkHelloRandom () // we formally retry to exclude collisions.
      else
        (log := cr::!log;
         cr)
#else
  cr
#endif

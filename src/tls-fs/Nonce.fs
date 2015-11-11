(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Nonce
//open Seq 
open Bytes
open Error


let timestamp () = bytes_of_int 4 (Date.secondsFromDawn ())

let random (n:nat) = 
  let r = CoreRandom.random n in
  let l = length r in
  if l = n then r 
  else unexpected "CoreRandom.random returned incorrect number of bytes"


let noCsr = random 64 // a constant value, with negligible probability of being sampled, excluded by idealization

let log: ref<list<bytes>> = ref []

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

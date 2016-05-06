module Nonce

open FStar.Seq
open Platform.Bytes
open Platform.Error
open FStar.HyperHeap
 
let ideal = IdealFlags.ideal_Nonce // controls idealization of random sample: collision-avoidance.

val timestamp: unit -> ST (lbytes 4)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
 
let timestamp () = 
  let time = Platform.Date.secondsFromDawn () in
  lemma_repr_bytes_values time;
  bytes_of_int 4 time
  
val noCsr: bytes
let noCsr = CoreCrypto.random 64 // a constant value, with negligible probability of being sampled, excluded by idealization

//This workaround doesn't work
//let op_Colon_Equals (#a:Type) (#i:rid) (r:rref i a) (v:a) = op_Colon_Equals #a #i r v

let log: rref root (list bytes) = ST.alloc [empty_bytes]
// let log_modified = op_Colon_Equals #_ #root log []

val mkHelloRandom: unit -> ST (lbytes 32) 
  (requires (fun h -> True))
  (ensures (fun h0 n h1 -> 
    modifies (Set.singleton root) h0 h1 /\ 
    modifies_rref root !{ as_ref log } h0 h1 /\
    (ideal ==> ~(List.Tot.mem n (sel h0 log)) /\
             sel h1 log = n :: sel h0 log )))

let rec mkHelloRandom() =
  recall log; 
  let cr = timestamp() @| CoreCrypto.random 28 in
  if ideal then 
    if List.Tot.mem cr !log 
    then mkHelloRandom () // formally retry to exclude collisions.
    else (log := cr::!log; cr)
  else cr

module Nonce

open TLSConstants
open FStar.Seq
open Platform.Bytes
open Platform.Error

open Heap
open FStar.HyperHeap

type hh = HyperHeap.t
type random = lbytes 32
type rid = r:rid{r<>root}
assume val nonces_region : r:rid{parent r = root}
 
let ideal = IdealFlags.ideal_Nonce // controls idealization of random sample: collision-avoidance.

val timestamp: unit -> ST (lbytes 4)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
 
let timestamp () = 
  let time = Platform.Date.secondsFromDawn () in
  lemma_repr_bytes_values time;
  bytes_of_int 4 time
  
//This workaround doesn't work
//let op_Colon_Equals (#a:Type) (#i:rid) (r:rref i a) (v:a) = op_Colon_Equals #a #i r v

type nonce_entry = (r:role * random * rid)
//let nonce_log = if ideal then rref nonces_region (list nonce_entry) else unit
//let log = if ideal then ST.alloc #(list nonce_entry) [] else ()
let log : (rref nonces_region (list nonce_entry)) = ralloc #(list nonce_entry) nonces_region []

val mkHelloRandom: r:role -> region:rid -> ST random
  (requires (fun h -> True))
  (ensures (fun h0 n h1 -> 
    modifies (Set.singleton nonces_region) h0 h1 /\ 
    modifies_rref nonces_region !{ as_ref log } h0 h1 /\
    (ideal ==> ~(List.Tot.existsb (fun (r0, n0, _) -> r=r0 && n0=n) (sel h0 log)) /\
             sel h1 log = (r, n, region) :: sel h0 log )))

let rec mkHelloRandom r region =
  recall log;
  let n : random = timestamp() @| CoreCrypto.random 28 in
  if ideal then 
    if List.Tot.existsb (fun (r0, n0, _) -> r=r0 && n0=n) !log
    then mkHelloRandom r region // formally retry to exclude collisions.
    else (log := (r, n, region) :: !log; n)
  else n


val lookup: role:role -> n:random -> ST (option rid)
  (requires (fun h -> True))
  (ensures (fun h0 rid h1 -> modifies Set.empty h0 h1))

let lookup role n =
  let entry = List.Tot.tryFind (fun (r0, n0, _) -> role=r0 && n=n0) !log in
  match entry with
  | None -> None
  | Some (_, _, rid) -> Some rid

(*
val lookup_lemma: r:role -> n:random -> h:hh ->
  Lemma (requires True)
  (ensures 
    let rid = lookup r n in
    is_Some rid ==> List.Tot.mem (role, n, Some.v rid) (sel h0 log))

let lookup_lemma r n h = ()
*)

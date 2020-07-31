module Nonce

open FStar.Bytes
open FStar.Error

open Mem
open TLSConstants

module HS = FStar.HyperStack
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HST = FStar.HyperStack.ST

let timestamp () =
  let time = FStar.Date.secondsFromDawn () in
  lemma_repr_bytes_values time;
  //assume(Platform.Bytes.repr_bytes time = FStar.Bytes.repr_bytes time);// temporary
  bytes_of_int 4 time

//Although the table only maps nonces to rids, externally, we also
//want to associate the nonce with a role. Within this module
//what counts is the stable association of nonce to rid
//So, we define role_nonce as an abstract predicate to capture the
//"event" that mkHelloRandom was called for particular triple of values
let role_nonce (cs:role) (n:random) (r:ex_rid) = registered n r

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"

let rec mkHelloRandom cs r =
  HST.recall nonce_rid_table;
  let rand = Random.sample32 28ul in
  let ts = timestamp() in
  let n : random = ts @| rand in
  if ideal then
    match MDM.lookup nonce_rid_table n with
      | None   -> MDM.extend nonce_rid_table n r; n
      | Some _ -> mkHelloRandom cs r // formally retry to exclude collisions.
  else n

let lookup role n = MDM.lookup nonce_rid_table n

(* Would be nice to make this a local let in new_region.
   Except, implicit argument inference for testify_forall fails *)
private let nonce_rids_exists (m:MDM.map random n_rid) =
    forall (n:random{Some? (MDM.sel m n)}). 
      HST.witnessed (HST.region_contains_pred (Some?.v (MDM.sel m n)))

(*
   A convenient wrapper around FStar.ST.new_region,
   which proves that the returned region does not exist in the nonce_rid_table.

   Requires a bit of fancy footwork with reasoning about witnessed predicates
   underneath quantifiers. So, one should really use this version of new_region
   for every dynamic region allocation in TLS.
*)
let new_region parent =
  HST.recall nonce_rid_table;
  let m0 = HST.op_Bang nonce_rid_table in
  HST.testify_forall_region_contains_pred 
    #(n:random{Some? (MDM.sel m0 n)}) #(fun n -> Some?.v (MDM.sel m0 n)) ();
  let r = new_region parent in
  HST.witness_region r;
  r

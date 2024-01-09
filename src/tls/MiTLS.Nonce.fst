module MiTLS.Nonce

open FStar.Bytes
open FStar.Error

open MiTLS.Mem
open MiTLS.TLSConstants

module HS = FStar.HyperStack
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HST = FStar.HyperStack.ST

let role_nonce cs n r = registered n r

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

let new_region parent =
  HST.recall nonce_rid_table;
  let m0 = HST.op_Bang nonce_rid_table in
  HST.testify_forall_region_contains_pred 
    #(n:random{Some? (MDM.sel m0 n)}) #(fun n -> Some?.v (MDM.sel m0 n)) ();
  let r = new_region parent in
  HST.witness_region r;
  r

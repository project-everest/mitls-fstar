
module Nonce
module HST = FStar.HyperStack.ST //Added automatically

open Mem
open TLSConstants
open Platform.Bytes
open FStar.Error

module HS = FStar.HyperStack
module MM = FStar.Monotonic.Map
module ST = FStar.HyperStack.ST

type random = lbytes 32

let ideal = Flags.ideal_Nonce // controls idealization of random sample: collision-avoidance.

val timestamp: unit -> ST (lbytes 4)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies Set.empty h0 h1))
let timestamp () = 
  let time = Platform.Date.secondsFromDawn () in
  lemma_repr_bytes_values time;
  assume(Platform.Bytes.repr_bytes time = FStar.Bytes.repr_bytes time);// temporary
  bytes_of_int 4 time

// ex_rid: The type of a region id that is known 
//         to exist in the current heap and in every future one
type ex_rid = ST.ex_rid

// MM.map provide a dependent map type; 
// In this case, we don't need the dependencey
// The n_rid type has a trivial depdendence on (n:random)
let n_rid = fun (n:random) -> ex_rid

// A partial map from nonces to rid is injective, 
// if it maps distinct nonces to distinct rids
let injective (n:MM.map' random n_rid) = 
  forall n1 n2. n1=!=n2 ==> (match MM.sel n n1, MM.sel n n2 with
			  | Some r1, Some r2 -> r1 <> r2
			  | _ -> True)

//nonce_rid_table:
//  A monotone, injective partial map in the tls_tables_region, from random to rid
//  Essentially: m:(r:random  -> Tot (n_rid r)) {injective m}
//  Equivalently m:(random  -> Tot rid) {injective m}
//We could conditionally allocate this table based on the ideal flag
//See the style, e.g., in StreamAE
//However, in this case, we have just a single global table and the additional
//allocation seems rather mild. Still, would be nice to do remove this allocation someday.
let nonce_rid_table : MM.t tls_tables_region random n_rid injective =  
  MM.alloc #tls_tables_region #random #n_rid #injective

//A nonce n is fresh in h if the nonce_rid_table doesn't contain it
let fresh (n:random) (h:HS.mem) = MM.sel (HS.sel h nonce_rid_table) n = None

//A region is fresh if no nonce is associated with it
let fresh_region (r:ex_rid) (h:HS.mem) =
  forall n. Some r <> MM.sel (HS.sel h nonce_rid_table) n 

//A nonce n is registered to region r, if the table contains n -> Some r; 
//This mapping is stable (that's what the HST.witnessed means)
let registered (n:random) (r:ST.erid) = 
  witnessed (region_contains_pred r) /\
  witnessed (MM.contains nonce_rid_table n r)

let testify (n:random) (r:ST.erid)
  : ST unit (requires (fun h -> registered n r))
	    (ensures (fun h0 _ h1 -> 
		 h0==h1 /\
	         registered n r /\ 
		 MM.contains nonce_rid_table n r h1))
  = testify (MM.contains nonce_rid_table n r)
  
//Although the table only maps nonces to rids, externally, we also 
//want to associate the nonce with a role. Within this module
//what counts is the stable association of nonce to rid
//So, we define role_nonce as an abstract predicate to capture the 
//"event" that mkHelloRandom was called for particular triple of values
abstract let role_nonce (cs:role) (n:random) (r:ex_rid) = registered n r

val mkHelloRandom: cs:role -> r:ex_rid -> ST random
  (requires (fun h -> fresh_region r h))
  (ensures (fun h0 n h1 ->
    HS.modifies (Set.singleton tls_tables_region) h0 h1 /\ //modifies at most the tables region
//17-12-16 FIXME    HS.modifies_ref tls_tables_region (Set.singleton (Heap.addr_of (HH.as_ref (HS.MkRef?.ref nonce_rid_table_as_hsref)))) h0 h1 /\ //and within it, at most the nonce_rid_table
    (b2t ideal ==> fresh n h0  /\        //if we're ideal then the nonce is fresh
             registered n r /\     //the nonce n is associated with r
             role_nonce cs n r))) //and the triple are associated as well, for ever more

(*! 18-02-14 TODO switch to dependentmap? *)
#set-options "--lax"
let rec mkHelloRandom cs r =
  recall nonce_rid_table;
  let n : random = timestamp() @| CoreCrypto.random 28 in
  if ideal then 
    match MM.lookup nonce_rid_table n with 
      | None -> MM.extend nonce_rid_table n r; n
      | Some _ -> mkHelloRandom cs r // formally retry to exclude collisions.
  else n

val lookup: cs:role -> n:random -> ST (option (ex_rid))
  (requires (fun h -> True))
  (ensures (fun h0 ropt h1 ->
	        h0==h1 /\ 
	        (match ropt with
		 | Some r -> registered n r /\ role_nonce cs n r
		 | None -> fresh n h0)))
let lookup role n = MM.lookup nonce_rid_table n

(* Would be nice to make this a local let in new_region.
   Except, implicit argument inference for testify_forall fails *)
private let nonce_rids_exists (m:MM.map' random n_rid) = 
    forall (n:random{Some? (MM.sel m n)}). witnessed (region_contains_pred (Some?.v (MM.sel m n)))

(* 
   A convenient wrapper around FStar.ST.new_region, 
   which proves that the returned region does not exist in the nonce_rid_table.
   
   Requires a bit of fancy footwork with reasoning about witnessed predicates 
   underneath quantifiers. So, one should really use this version of new_region 
   for every dynamic region allocation in TLS.
*)   
val new_region: parent:ST.erid -> ST ex_rid 
  (requires (fun h -> witnessed (region_contains_pred parent)))
  (ensures (fun h0 r h1 -> 
	      extends r parent /\
	      HS.fresh_region r h0 h1 /\ //it's fresh with respect to the current heap
	      fresh_region r h1)) //and it's not in the nonce table
let new_region parent = 
  recall nonce_rid_table;
  let m0 = !nonce_rid_table in 
  let tok: squash (nonce_rids_exists m0) = () in   
  testify_forall_region_contains_pred tok;
  new_region parent

// a constant value, with negligible probability of being sampled, excluded by idealization
let noCsr : bytes = CoreCrypto.random 64 


(* With the upcoming improved support for top-level effects, 
   we could  prove that noCsr is not fresh in the initial state. 
   For example:

   let noCsr : ST random
      (requires (fun h -> Mr.m_sel h nonce_rid_table = MM.empty_map random ex_rid))
      (ensures (fun h0 r h1 -> ~ (fresh r h1)))
      = mkHelloRandom Client (new_region (FStar.ST.new_region HS.root))
*)

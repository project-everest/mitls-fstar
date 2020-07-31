module Nonce

open FStar.Bytes
open FStar.Error

open Mem
open TLSConstants

module HS = FStar.HyperStack
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HST = FStar.HyperStack.ST

type random = lbytes 32

inline_for_extraction noextract
let ideal = Flags.ideal_Nonce // controls idealization of random sample: collision-avoidance.

val timestamp: unit -> ST (lbytes 4)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HS.modifies Set.empty h0 h1))

// ex_rid: The type of a region id that is known
//         to exist in the current heap and in every future one
//2018.03.09 SZ: Excluded the case r = root
type ex_rid = r:HST.ex_rid{r <> root}

// MDM.map provide a dependent map type;
// In this case, we don't need the dependencey
// The n_rid type has a trivial depdendence on (n:random)
let n_rid = fun (n:random) -> ex_rid

// A partial map from nonces to rid is injective,
// if it maps distinct nonces to distinct rids
let injective (n:MDM.partial_dependent_map random n_rid) =
  forall n1 n2. n1=!=n2 ==> (match DM.sel n n1, DM.sel n n2 with
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
let nonce_rid_table : MDM.t tls_tables_region random n_rid injective =
  MDM.alloc ()

//A nonce n is fresh in h if the nonce_rid_table doesn't contain it
let fresh (n:random) (h:HS.mem) = MDM.sel (HS.sel h nonce_rid_table) n = None

//A region is fresh if no nonce is associated with it
let fresh_region (r:ex_rid) (h:HS.mem) =
  forall n. Some r <> MDM.sel (HS.sel h nonce_rid_table) n

//A nonce n is registered to region r, if the table contains n -> Some r;
//This mapping is stable (that's what the HST.witnessed means)
let registered (n:random) (r:ex_rid) =
  HST.witnessed (HST.region_contains_pred r) /\
  HST.witnessed (MDM.contains nonce_rid_table n r)

let testify (n:random) (r:ex_rid)
  : ST unit (requires (fun h -> registered n r))
      (ensures (fun h0 _ h1 ->
     h0==h1 /\
           registered n r /\
     MDM.contains nonce_rid_table n r h1))
  = HST.testify (MDM.contains nonce_rid_table n r)

//Although the table only maps nonces to rids, externally, we also
//want to associate the nonce with a role. Within this module
//what counts is the stable association of nonce to rid
//So, we define role_nonce as an abstract predicate to capture the
//"event" that mkHelloRandom was called for particular triple of values
val role_nonce (cs:role) (n:random) (r:ex_rid) : GTot Type0

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"

val mkHelloRandom: cs:role -> r:ex_rid -> ST random
  (requires (fun h -> fresh_region r h))
  (ensures (fun h0 n h1 ->
    let nonce_rid_table_as_hsref =  nonce_rid_table in
    HS.modifies (Set.singleton tls_tables_region) h0 h1 /\ //modifies at most the tables region
    HS.modifies_ref tls_tables_region (Set.singleton (HS.as_addr nonce_rid_table_as_hsref)) h0 h1 /\ //and within it, at most the nonce_rid_table
    (b2t ideal ==> 
      fresh n h0 /\        //if we're ideal then the nonce is fresh
      registered n r /\     //the nonce n is associated with r
      role_nonce cs n r))) //and the triple are associated as well, for ever more

(* This is super bizzare, the lack of pre/post seems to allow it to go through *)
noextract
val lookup: cs:role -> n:random -> ST (option ex_rid)
  (requires (fun h -> True))
  (ensures (fun _ _ _ -> True))
  (* (ensures (fun h0 ropt h1 ->
          h0==h1 /\
          (match ropt with
     | Some r -> registered n r /\ role_nonce cs n r
     | None -> fresh n h0))) *)

(*
   A convenient wrapper around FStar.ST.new_region,
   which proves that the returned region does not exist in the nonce_rid_table.

   Requires a bit of fancy footwork with reasoning about witnessed predicates
   underneath quantifiers. So, one should really use this version of new_region
   for every dynamic region allocation in TLS.
*)
noextract
val new_region: parent:HST.erid -> ST ex_rid
  (requires (fun h -> True))
  (ensures (fun h0 r h1 ->
        HS.extends r parent /\
        HS.fresh_region r h0 h1 /\ //it's fresh with respect to the current heap
        fresh_region r h1)) //and it's not in the nonce table

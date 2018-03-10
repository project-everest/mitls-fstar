(* An experiment towards the PRF in KeySchedule, collapsing master and key derivation *)
module MasterSecret (* : ST _ _ _ *)

open Mem
open TLSConstants
open StreamAE
open TLSInfo
open FStar.HyperStack

module AE = StreamAE
module DM = FStar.DependentMap
module MM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module N = Nonce
module I = IdNonce

//We maintain ms_tab, a map from ids i, to w:StreamAE.writer i
//such that, w's region is known to be a child region of the
//region associated with i's nonce
let writer (i:AE.id) = w:AE.writer i{
  N.registered (nonce_of_id i) (HS.parent w.region) /\
  HS.disjoint (HS.parent w.region) tls_region /\
  HST.witnessed (HST.region_contains_pred w.region) /\
  is_epoch_rgn w.region /\
  is_epoch_rgn (HS.parent w.region)
}

// A partial map from i:id to w:writer i is region_injective
// if it maps distinct ids to writers with distinct regions
let region_injective (m:MM.partial_dependent_map AE.id writer) =
  forall i1 i2.{:pattern (DM.sel m i1); (DM.sel m i2)}
       i1=!=i2 ==> (match DM.sel m i1, DM.sel m i2 with
                          | Some w1, Some w2 -> w1.region <> w2.region
                          | _ -> True)

let ms_tab : MM.t tls_tables_region AE.id writer region_injective =
  MM.alloc ()

//A region is fresh if no nonce is associated with it
let fresh_in_ms_tab (r:rgn) (h:mem) =
  forall i. match MM.sel (HS.sel h ms_tab) i with
       | Some w -> w.region <> r
       | None -> True

private let id_rgns_witnessed (m:MM.map AE.id writer) =
    forall (i:AE.id{Some? (MM.sel m i)}). HST.witnessed (HST.region_contains_pred ((Some?.v (MM.sel m i)).region))

private let contains_id_rgns (h:mem) =
    let m = HS.sel h ms_tab in
    forall (i:AE.id{Some? (MM.sel m i)}). Map.contains h.h ((Some?.v (MM.sel m i)).region)


(* private val all_ms_tab_regions_exists: unit -> ST unit //would be good to make such stateful lemmas STTot, once we have it; a bit loose for now *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 _ h1 ->  *)
(*            h0=h1 /\ *)
(*            contains_id_rgns h1)) *)
let all_ms_tab_regions_exists () =
  HST.recall ms_tab;
  let m0 = HST.op_Bang ms_tab in
  let tok : squash (id_rgns_witnessed m0) = () in
  HST.testify_forall tok

let derive (r:rgn) (i:AE.id)
  : ST (AE.writer i)
       (requires (fun h ->
           HS.disjoint r tls_region /\
           is_epoch_rgn r /\
           N.registered (nonce_of_id i) r))
       (ensures (fun h0 w h1 ->
           let ms_tab_as_hsref = ms_tab in
           HS.disjoint r tls_region
           /\ is_epoch_rgn r
           /\ N.registered (nonce_of_id i) r
           /\ HS.parent w.region = r
           /\ is_epoch_rgn w.region
           /\ modifies (Set.singleton tls_tables_region) h0 h1 //modifies at most the tls_tables region
           /\ HS.modifies_ref tls_tables_region (Set.singleton (as_addr ms_tab_as_hsref)) h0 h1 //and within it, at most ms_tab
           /\ HST.witnessed (HST.region_contains_pred w.region) //and the writer's region is witnessed to exists also
           /\ HST.witnessed (MM.contains ms_tab i w) //and the writer is witnessed to be in ms_tab
           /\ (let old_ms = HS.sel h0 ms_tab in
              let new_ms = HS.sel h1 ms_tab in
               old_ms == new_ms //either ms_tab didn't change at all
               \/ (MM.sel old_ms i == None
                  /\ new_ms == MM.upd old_ms i w //or we just added w to it
                  /\ (TLSInfo.authId i ==> HS.sel h1 (AE.ilog w.log) == Seq.createEmpty))))) //and it is a fresh log
  = HST.recall ms_tab;
    match MM.lookup ms_tab i with
    | None ->
      all_ms_tab_regions_exists ();
      let w = AE.gen r i in
      let wr = HST.witness_region w.region in //witness that it always exists
      MM.extend ms_tab i w;
      w
    | Some w ->
      N.testify (nonce_of_id i) r;   // n i -> r
      N.testify (nonce_of_id i) (HS.parent w.region); //n i -> HS.parent w.region ==> r=w.region;
      w

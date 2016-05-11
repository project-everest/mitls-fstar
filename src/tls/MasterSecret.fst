(* An experiment towards the PRF in KeySchedule, collapsing master and key derivation *)
module MasterSecret (* : ST _ _ _ *)
open FStar.HyperHeap
open TLSConstants
open StreamAE
module AE = StreamAE
module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module N = Nonce
module I = IdNonce

//We maintain ms_tab, a map from ids i, to w:StreamAE.writer i
//such that, w's region is known to be a child region of the 
//region associated with i's nonce
let writer (i:AE.id) = w:AE.writer i{
  N.registered (I.nonce_of_id i) (HH.parent w.region) /\ 
  HH.disjoint (HH.parent w.region) tls_region /\
  MR.witnessed (MR.rid_exists w.region)
}  

// A partial map from i:id to w:writer i is region_injective
// if it maps distinct ids to writers with distinct regions
let region_injective (m:MM.map' AE.id writer) = 
  forall i1 i2.{:pattern (MM.sel m i1); (MM.sel m i2)} 
       i1<>i2 ==> (match MM.sel m i1, MM.sel m i2 with
			  | Some w1, Some w2 -> w1.region <> w2.region
			  | _ -> True)

let ms_tab : MM.t tls_tables_region AE.id writer region_injective = 
  MM.alloc #TLSConstants.tls_tables_region #AE.id #writer #region_injective

//A region is fresh if no nonce is associated with it
let fresh_in_ms_tab (r:rgn) (h:HH.t) = 
  forall i. match MM.sel (MR.m_sel h ms_tab) i with 
       | Some w -> w.region <> r
       | None -> True

private let id_rgns_witnessed (m:MM.map' AE.id writer) = 
    forall (i:AE.id{is_Some (MM.sel m i)}). MR.witnessed (MR.rid_exists ((Some.v (MM.sel m i)).region))

private let contains_id_rgns (h:HH.t) = 
    let m = MR.m_sel h ms_tab in 
    forall (i:AE.id{is_Some (MM.sel m i)}). Map.contains h ((Some.v (MM.sel m i)).region)


(* private val all_ms_tab_regions_exists: unit -> ST unit //would be good to make such stateful lemmas STTot, once we have it; a bit loose for now *)
(*   (requires (fun h0 -> True)) *)
(*   (ensures (fun h0 _ h1 ->  *)
(* 	      h0=h1 /\ *)
(* 	      contains_id_rgns h1)) *)
let all_ms_tab_regions_exists () = 
  MR.m_recall ms_tab;
  let m0 = MR.m_read ms_tab in
  let tok : squash (id_rgns_witnessed m0) = () in   
  MR.testify_forall tok

let derive (r:rid) (i:AE.id) 
  : ST (AE.writer i)
       (requires (fun h -> 
	   HH.disjoint r tls_region /\
	   N.registered (I.nonce_of_id i) r))
       (ensures (fun h0 w h1 -> 
       	   HH.disjoint r tls_region 
	   /\ N.registered (I.nonce_of_id i) r
	   /\ HH.parent w.region = r
	   /\ modifies (Set.singleton tls_tables_region) h0 h1 //modifies at most the tls_tables region
	   /\ modifies_rref tls_tables_region !{HH.as_ref (MR.as_rref ms_tab)} h0 h1 //and within it, at most ms_tab
	   /\ MR.witnessed (MR.rid_exists w.region) //and the writer's region is witnessed to exists also
	   /\ MR.witnessed (MM.contains ms_tab i w) //and the writer is witnessed to be in ms_tab
	   /\ (let old_ms = MR.m_sel h0 ms_tab in
	      let new_ms = MR.m_sel h1 ms_tab in
 	       old_ms = new_ms //either ms_tab didn't change at all
	       \/ (MM.sel old_ms i = None
		  /\ new_ms = MM.upd old_ms i w //or we just added w to it
	   	  /\ (TLSInfo.authId i ==> MR.m_sel h1 (AE.ilog w.log) = Seq.createEmpty))))) //and it is a fresh log
  = MR.m_recall ms_tab;
    match MM.lookup ms_tab i with
    | None -> 
      all_ms_tab_regions_exists ();
      let w = AE.gen r i in 
      let wr = MR.ex_rid_of_rid w.region in //witness that it always exists
      MM.extend ms_tab i w;
      w
    | Some w -> 
      N.testify (I.nonce_of_id i) r;   // n i -> r
      N.testify (I.nonce_of_id i) (HH.parent w.region); //n i -> HH.parent w.region ==> r=w.region; 
      w

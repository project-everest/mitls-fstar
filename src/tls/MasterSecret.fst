(* An experiment towards the PRF in KeySchedule, collapsing master and key derivation *)
module MasterSecret (* : ST _ _ _ *)
open FStar.HyperHeap

(* tls_region is to be moved to TLSContants *)
let tls_region = new_region root

module AE = StreamAE
module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap

type writer (ids:(AE.id * rid)) = w:AE.writer (fst ids){HH.extends (StreamAE.State.region w) (snd ids)}
let ids = (AE.id * rid)

let region_exists (r:rid) = MR.witnessed (fun h -> Map.contains h r)
    
let map_invariant (m:MM.map' ids writer) =
  forall i r. 
    let wopt = MM.sel m (i, r) in
    is_Some wopt ==>
    HH.disjoint r tls_region 
    /\ region_exists (StreamAE.State.region (Some.v wopt))

  (* Failed attempt *)
  (* (forall i1 i2. is_Some (m i1) /\ is_Some (m i2) /\ fst i1 = fst i2 ==> i1 = i2) *)
  (* /\ (forall i. is_None (m i) ==> (forall j. fst i = fst j ==> is_None (m j))) *)

let ms_tab : MM.t tls_region ids writer map_invariant = 
  MM.alloc #tls_region #ids #writer #map_invariant

assume val gcut: f:(unit -> GTot Type){f()} -> Tot unit
assume val gadmit: f:(unit -> GTot Type) -> Tot (u:unit{f()})
assume val witness_rid: r:rid -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> 
	      h0 = h1 /\
	      Map.contains h0 r /\
	      region_exists r))
	      
let derive (r:rid) (i:AE.id) 
  : ST (AE.writer i)
       (requires (fun h -> disjoint r tls_region))
       (ensures (fun h0 w h1 -> 
	   HH.extends (StreamAE.State.region w) r 
	   /\ modifies (Set.singleton tls_region) h0 h1 //modifies at most the tls region
	   /\ modifies_rref tls_region !{HH.as_ref (MR.as_rref ms_tab)} h0 h1 //and within it, at most ms_tab
	   /\ MR.witnessed (MM.contains ms_tab (i,r) w) //and the writer is witnessed to be in ms_tab
	   /\ (let old_ms = MR.m_sel h0 ms_tab in
	      let new_ms = MR.m_sel h1 ms_tab in
 	       old_ms = new_ms //either ms_tab didn't change at all
	       \/ (new_ms = MM.upd old_ms (i,r) w //or we just added w to it
		  /\ (TLSInfo.authId i ==> MR.m_sel h1 (AE.ilog (StreamAE.State.log w)) = Seq.createEmpty))))) //and it is a fresh log
  = recall_region tls_region;
    let y = MM.lookup ms_tab (i, r) in
    match y with 
    | None -> 
      let w = AE.gen r i in 
      witness_rid (StreamAE.State.region w);
      MM.extend ms_tab (i,r) w;
      w
    | Some w -> 
      w

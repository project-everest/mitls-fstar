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
  HH.disjoint (HH.parent w.region) tls_region
}  
    
let ms_tab : MM.t tls_tables_region AE.id writer (fun x -> True) = 
  MM.alloc #TLSConstants.tls_tables_region #AE.id #writer #(fun x -> True)

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
	   /\ MR.witnessed (MM.contains ms_tab i w) //and the writer is witnessed to be in ms_tab
	   /\ (let old_ms = MR.m_sel h0 ms_tab in
	      let new_ms = MR.m_sel h1 ms_tab in
 	       old_ms = new_ms //either ms_tab didn't change at all
	       \/ (new_ms = MM.upd old_ms i w //or we just added w to it
	   	  /\ (TLSInfo.authId i ==> MR.m_sel h1 (AE.ilog w.log) = Seq.createEmpty))))) //and it is a fresh log
  = MR.m_recall ms_tab;
    match MM.lookup ms_tab i with
    | None -> 
      let w = AE.gen r i in 
      MM.extend ms_tab i w;
      w
    | Some w -> 
      N.testify (I.nonce_of_id i) r;   // n i -> r
      N.testify (I.nonce_of_id i) (HH.parent w.region); //n i -> HH.parent w.region ==> r=w.region; 
      w

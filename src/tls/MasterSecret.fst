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
let map_invariant (m:MM.map' ids writer) = True
  (* Failed attempt *)
  (* (forall i1 i2. is_Some (m i1) /\ is_Some (m i2) /\ fst i1 = fst i2 ==> i1 = i2) *)
  (* /\ (forall i. is_None (m i) ==> (forall j. fst i = fst j ==> is_None (m j))) *)

let ms_tab : MM.t tls_region ids writer map_invariant = 
  MM.alloc #tls_region #ids #writer #map_invariant

assume val gcut: f:(unit -> GTot Type){f()} -> Tot unit
assume val gadmit: f:(unit -> GTot Type) -> Tot (u:unit{f()})

let derive (r:rid) (i:AE.id) 
  : ST (AE.writer i)
       (requires (fun h -> disjoint r tls_region))
       (ensures (fun h0 w h1 -> 
	   HH.extends (StreamAE.State.region w) r 
	   /\ modifies (Set.singleton tls_region) h0 h1
	   /\ MR.witnessed (MM.t_contains ms_tab (i,r) w)))
  = recall_region tls_region;
    let y = MM.lookup ms_tab (i, r) in
    match y with 
    | None -> 
      let w = AE.gen r i in 
      MM.extend ms_tab (i,r) w;
      w
    | Some w -> 
      w

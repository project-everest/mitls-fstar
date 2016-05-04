(* An experiment towards the PRF in KeySchedule, collapsing master and key derivation *)
module MasterSecret (* : ST _ _ _ *)
open FStar.HyperHeap

(* tls_region is to be moved to TLSContants *)
let tls_region = new_region root

module AE = StreamAE
module MM = MonotoneMap
module MR = FStar.Monotonic.RRef

let ms_tab : MM.t tls_region AE.id AE.writer (fun x -> True) =
  MM.alloc #tls_region #AE.id #AE.writer #(fun x -> True)

let derive (r:rid) (i:AE.id) 
  : ST (AE.writer i)
       (requires (fun h -> disjoint r tls_region))
       (ensures (fun h0 w h1 -> 
	   (* StreamAE.State.region w = r *) //not yet sure how to prove this part
	   (* /\  *)modifies (Set.singleton tls_region) h0 h1
	   /\ MR.witnessed (MM.t_contains ms_tab i w)))
  = recall_region tls_region;
    let y = MM.lookup ms_tab i in
    match y with 
    | None -> 
      let w = AE.gen r i in 
      MM.extend ms_tab i w;
      w
    | Some w -> 
      w

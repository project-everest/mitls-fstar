module ConnInvariant
open TLSConstants

module Mm = MonotoneMap
module Mr = FStar.Monotonic.RRef
module Hh = FStar.HyperHeap
open TLSInfo
open Handshake
open Connection

type id = StreamAE.id
let r_conn (r:random) = c:connection{c.hs.id = r}

let pairwise_disjoint (m:Mm.map' random r_conn) = 
    forall r1 r2. r1<>r2 /\ is_Some (Mm.sel m r1) /\ is_Some (Mm.sel m r2)
	     ==> Hh.disjoint (Some.v (Mm.sel m r1)).region  
		             (Some.v (Mm.sel m r2)).region

module Ms = MasterSecret
let tls_region = Ms.tls_region

type conn_table_t = Mm.t tls_region random r_conn pairwise_disjoint

let conn_table : conn_table_t = 
  Mm.alloc #tls_region #random #r_conn #pairwise_disjoint

type ms_tab = Mm.map' Ms.ids Ms.writer 
type c_tab  = Mm.map' random r_conn 

assume val idNonce : id -> Tot random

let ms_conn_invariant (ms:ms_tab)
 		      (conn:c_tab)
		      (h:HyperHeap.t)
  = forall (i:id) (r:Hh.rid). authId i ==> 
	            (match MM.sel ms (i,r) with 
		     | None -> True
		     | Some w -> 
		       (* Mr.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)     //we don't even have a connection yet *)
		       (match Mm.sel conn (idNonce i) with
		        | None -> Mr.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty     //we don't even have a connection yet
		       	| Some c -> (exists e. SeqProperties.mem e  (Hh.sel h (HS.log c.hs)) /\ e.w == w)       //registered; NB: CHEAT! We will add a sum between the two kinds of state; a module Epoch with type StAE = StatefulLHAE | StreamAE
		       		 \/ Mr.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)) //not registered; not yet used either


let mc_inv (h:HyperHeap.t) = ms_conn_invariant (Mr.m_sel h Ms.ms_tab) (Mr.m_sel h conn_table) h

//Checking the stability of the invariant

//1. Adding a new log to the ms table (because we tried a lookup at id and it failed)
//   Easy: because a new log is empty and the id is not in the table already
//         so, we're in the second case
//   //3. No connection yet


val add_new_writer: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id -> r:Hh.rid -> w:Ms.writer (i,r) 
  -> Lemma (requires 
		 authId i /\
		 mc_inv h0 /\ //we're initially in the invariant
		 Hh.modifies (Set.singleton tls_region) h0 h1 /\ //we just changed the tls_region
		 Hh.modifies_rref tls_region !{Hh.as_ref (Mr.as_rref Ms.ms_tab)} h0 h1 /\ //and within it, the only thing that changed is the ms_tab
		 (let old_ms = Mr.m_sel h0 Ms.ms_tab in 
		  let new_ms = Mr.m_sel h1 Ms.ms_tab in
		  Mm.sel old_ms (i,r) = None /\
		  new_ms = Mm.upd old_ms (i,r) w) /\                                    //and it only changed by adding w
		 Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)             //and w's log is empty
	 (ensures mc_inv h1)                                                       //we're back in the invariant


assume val gcut: f:(unit -> GTot Type){f()} -> Tot unit
assume val gadmit: f:(unit -> GTot Type) -> Tot (u:unit{f()})


let add_new_writer h0 h1 i r w =  
  assume (Map.contains h0 tls_region);
  assume (Hh.contains_ref (Mr.as_rref Ms.ms_tab) h0);
  assume (Hh.contains_ref (Mr.as_rref conn_table) h0);
  let old_ms   = Mr.m_sel h0 Ms.ms_tab in
  let new_ms   = Mr.m_sel h1 Ms.ms_tab in
  assume (forall j r. 
	    let wopt = Mm.sel old_ms (j, r) in
	    is_Some wopt ==>
	    Hh.disjoint r tls_region 
	    /\ Map.contains h0 (StreamAE.State.region (Some.v wopt)));
  ()


  (* let j  : id = magic () in  *)
  (* assume (authId j); *)
  (* let r' : Hh.rid = magic () in  *)
  (* match Mm.sel old_ms (j, r') with  *)
  (*   | None -> admit() *)
  (*   | Some w' ->  *)
  (*     (\* assert (Hh.disjoint r' tls_region); *\) *)
  (*     (\* assert (Hh.disjoint (StreamAE.State.region w') tls_region); *\) *)
  (*     (\* assume (Map.contains h0 (StreamAE.State.region w')); *\) *)
  (*     assert (Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log w')) = Seq.createEmpty); *)
  (*     admit() *)



    
  assert (ms_conn_invariant old_ms new_conn h1);
  admit()
  
  
  
  admit()


  = admit()
		 
		    
		    	


//2. Adding a new epoch to a connection c, with a fresh index (hdId i) for c
//      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
//      -- we need to show that the (exists e. SeqProperties.mem ...) is false (because of the fresh index for c)
//      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)


//3. Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
//    --- we're in the first case, left disjunct


//4. Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
//    -- So, we cannot be in the Some w, None case, as this is only for bad writers
//    -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id

//    Note: we can prove that the having a doomed writer is a monotonic property of nonces

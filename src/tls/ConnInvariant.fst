module ConnInvariant
open TLSConstants


module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module MS = MasterSecret

open TLSInfo
open Handshake
open Connection

type id = StreamAE.id
let r_conn (r:random) = c:connection{c.hs.id = r}

let pairwise_disjoint (m:MM.map' random r_conn) = 
    forall r1 r2. r1<>r2 /\ is_Some (MM.sel m r1) /\ is_Some (MM.sel m r2)
	     ==> HH.disjoint (Some.v (MM.sel m r1)).region  
		             (Some.v (MM.sel m r2)).region


let tls_region = MS.tls_region

type conn_table_t = MM.t tls_region random r_conn pairwise_disjoint

let conn_table : conn_table_t = 
  MM.alloc #tls_region #random #r_conn #pairwise_disjoint

type ms_tab = MM.map' MS.ids MS.writer 
type c_tab  = MM.map' random r_conn 

assume val idNonce : id -> Tot random

let registered (i:id{StAE.is_stream_ae i}) (w:StreamAE.writer i) (c:connection) (h:HH.t) = 
  HH.disjoint (HS.region c.hs) tls_region /\
  HH.contains_ref (HS.log c.hs) h /\
  (exists e. SeqProperties.mem e  (HH.sel h (HS.log c.hs)) /\
      (let i' = Handshake.hsId (Handshake.Epoch.h e) in
        i=i' /\ StAE.stream_ae #i e.w == w))

let ms_conn_invariant (ms:ms_tab)
 		      (conn:c_tab)
		      (h:HyperHeap.t) 
  = forall (i:id) (r:HH.rid).{:pattern (MM.sel ms (i,r))}
	     authId i /\ StAE.is_stream_ae i ==>  //Focused only on TLS-1.3 for now, hence the is_stream_ae guard
	            (match MM.sel ms (i,r) with 
		     | None -> True
		     | Some w -> 
		       Map.contains h (StreamAE.State.region w) /\ //technical for framing; need to know that the writer's region exists
 		       (MR.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty  \/   //the writer is still unused; or
		        (let copt = MM.sel conn (idNonce i) in
  			 is_Some copt /\ registered i w (Some.v copt) h)))      //it's been assigned to a connection

let mc_inv (h:HyperHeap.t) = ms_conn_invariant (MR.m_sel h MS.ms_tab) (MR.m_sel h conn_table) h

//Checking the stability of the invariant

//1. Deriving a new key involves adding a new writer to the ms table (because we tried a lookup at id and it failed)
//   Easy: because a new log is empty and both cases of the conn table allow empty logs to be in ms
 
val ms_derive_is_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id -> r:HH.rid -> w:MS.writer (i,r) 
  -> Lemma (requires 
		 HH.contains_ref (MR.as_rref conn_table) h0 /\
		 HH.contains_ref (MR.as_rref MS.ms_tab) h0 /\
		 Map.contains h1 (StreamAE.State.region w) /\
		 authId i /\ 
		 StAE.is_stream_ae i /\
		 mc_inv h0 /\ //we're initially in the invariant
		 HH.modifies (Set.singleton tls_region) h0 h1 /\ //we just changed the tls_region
		 HH.modifies_rref tls_region !{HH.as_ref (MR.as_rref MS.ms_tab)} h0 h1 /\ //and within it, at most the ms_tab
		 (let old_ms = MR.m_sel h0 MS.ms_tab in 
		  let new_ms = MR.m_sel h1 MS.ms_tab in
		  MM.sel old_ms (i,r) = None /\
		  new_ms = MM.upd old_ms (i,r) w) /\                                    //and the ms_tab only changed by adding w
		 MR.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)             //and w's log is empty
	 (ensures mc_inv h1)                                                       //we're back in the invariant
let ms_derive_is_ok h0 h1 i r w = ()

//2. Adding a new epoch to a connection c, with a fresh index (hdId i) for c
//      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
//      -- we need to show that the (exists e. SeqProperties.mem ...) is false (because of the fresh index for c)
//      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)
val add_epoch_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id{StAE.is_stream_ae i /\ authId i} 
		-> c:r_conn (idNonce i) -> e:epoch (HS.region c.hs) (HS.peer c.hs) 
  -> Lemma (requires 
            (let ctab = MR.m_sel h0 conn_table in
	     let mstab = MR.m_sel h0 MS.ms_tab in
	     let old_hs_log = HH.sel h0 (HS.log c.hs) in
     	     let new_hs_log = HH.sel h1 (HS.log c.hs) in 
	     let rgn = HS.region c.hs in
	     HH.contains_ref (MR.as_rref conn_table) h0 /\
	     HH.contains_ref (MR.as_rref MS.ms_tab) h0 /\
	     HH.disjoint (HS.region c.hs) tls_region /\
	     HH.contains_ref (HS.log c.hs) h0 /\
	     HH.contains_ref (HS.log c.hs) h1 /\
	     mc_inv h0 /\ //we're initially in the invariant
	     i=hsId (Epoch.h e) /\ //the epoch has id it
	     (let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
	      let epochs = HH.sel h0 (HS.log c.hs) in
      	      Map.contains h1 (StreamAE.State.region w) /\
	      (forall e. SeqProperties.mem e epochs ==> hsId (Epoch.h e) <> i) /\ //i is fresh for c
 	      MM.sel mstab (i, rgn) = Some w /\ //we found the writer in the ms_tab
	      MM.sel ctab (idNonce i) = Some c /\ //we found the connection in the conn_table
	      HH.modifies_one (HS.region c.hs) h0 h1 /\ //we just modified this connection's handshake region
	      HH.modifies_rref (HS.region c.hs) !{HH.as_ref (HS.log c.hs)} h0 h1 /\ //and within it, just the epochs log
	      new_hs_log = SeqProperties.snoc old_hs_log e))) //and we modified it by adding this epoch to it
	  (ensures mc_inv h1) //we're back in the invariant

#reset-options "--z3timeout 10 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

let add_epoch_ok h0 h1 i c e = 
  assert (MR.m_sel h0 MS.ms_tab = MR.m_sel h1 MS.ms_tab);
  assert (MR.m_sel h0 conn_table = MR.m_sel h1 conn_table);
  let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
  assert (MR.m_sel h0 (StreamAE.ilog (StreamAE.State.log w)) = MR.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)));
  let ctab = MR.m_sel h0 conn_table in
  let mstab = MR.m_sel h0 MS.ms_tab in
  let copt = MM.sel ctab (idNonce i) in
  let old_hs_log = HH.sel h0 (HS.log c.hs) in
  assert (is_Some copt);
  assert (~ (registered i w (Some.v copt) h0));
  MonotoneSeq.lemma_mem_snoc old_hs_log e;
  assert (registered i w (Some.v copt) h1);
  let j : id  = magic () in 
  let s : HH.rid = magic () in 
  assume (StAE.is_stream_ae j);
  assume (authId j);
  assume (s <> HS.region c.hs);
  match MM.sel mstab (j, s) with 
  | None -> admit()
  | Some wj -> 
    assume (StreamAE.State.region wj <> HS.region c.hs); //can see here why the post-condition fails ... need better separation invariants between the HS.log and the writer logs
    assume (HH.contains_ref (MR.as_rref (StreamAE.ilog (StreamAE.State.log wj))) h0);
    assert (MR.m_sel h0 (StreamAE.ilog (StreamAE.State.log wj)) = MR.m_sel h1 (StreamAE.ilog (StreamAE.State.log wj)));
    admit()


//3. Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
//    --- we're in the first case, left disjunct (should be easy)


//4. Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
//    -- So, we cannot be in the Some w, None case, as this is only for bad writers
//    -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id

//    Note: we can prove that the having a doomed writer is a monotonic property of nonces

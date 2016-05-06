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

let registered (i:id{StAE.is_stream_ae i}) (w:StreamAE.writer i) (c:connection) (h:Hh.t) = 
  Hh.disjoint (HS.region c.hs) tls_region /\
  Hh.contains_ref (HS.log c.hs) h /\
  (exists e. SeqProperties.mem e  (Hh.sel h (HS.log c.hs)) /\
      (let i' = Handshake.hsId (Handshake.Epoch.h e) in
        i=i' /\ StAE.stream_ae #i e.w == w))

let ms_conn_invariant (ms:ms_tab)
 		      (conn:c_tab)
		      (h:HyperHeap.t) 
  = forall (i:id) (r:Hh.rid).{:pattern (MM.sel ms (i,r))}
	     authId i /\ StAE.is_stream_ae i ==>  //Focused only on TLS-1.3 for now, hence the is_stream_ae guard
	            (match MM.sel ms (i,r) with 
		     | None -> True
		     | Some w -> 
		       Map.contains h (StreamAE.State.region w) /\ //technical for framing; need to know that the writer's region exists
 		       (Mr.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty  \/   //the writer is still unused; or
		        (let copt = Mm.sel conn (idNonce i) in
  			 is_Some copt /\ registered i w (Some.v copt) h)))      //it's been assigned to a connection

let mc_inv (h:HyperHeap.t) = ms_conn_invariant (Mr.m_sel h Ms.ms_tab) (Mr.m_sel h conn_table) h

//Checking the stability of the invariant

//1. Deriving a new key involves adding a new writer to the ms table (because we tried a lookup at id and it failed)
//   Easy: because a new log is empty and both cases of the conn table allow empty logs to be in ms

val ms_derive_is_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id -> r:Hh.rid -> w:Ms.writer (i,r) 
  -> Lemma (requires 
		 Hh.contains_ref (Mr.as_rref conn_table) h0 /\
		 Hh.contains_ref (Mr.as_rref Ms.ms_tab) h0 /\
		 Map.contains h1 (StreamAE.State.region w) /\
		 authId i /\ 
		 StAE.is_stream_ae i /\
		 mc_inv h0 /\ //we're initially in the invariant
		 Hh.modifies (Set.singleton tls_region) h0 h1 /\ //we just changed the tls_region
		 Hh.modifies_rref tls_region !{Hh.as_ref (Mr.as_rref Ms.ms_tab)} h0 h1 /\ //and within it, at most the ms_tab
		 (let old_ms = Mr.m_sel h0 Ms.ms_tab in 
		  let new_ms = Mr.m_sel h1 Ms.ms_tab in
		  Mm.sel old_ms (i,r) = None /\
		  new_ms = Mm.upd old_ms (i,r) w) /\                                    //and the ms_tab only changed by adding w
		 Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)             //and w's log is empty
	 (ensures mc_inv h1)                                                       //we're back in the invariant
let ms_derive_is_ok h0 h1 i r w = ()

//2. Adding a new epoch to a connection c, with a fresh index (hdId i) for c
//      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
//      -- we need to show that the (exists e. SeqProperties.mem ...) is false (because of the fresh index for c)
//      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)
val add_epoch_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id{StAE.is_stream_ae i /\ authId i} 
		-> c:r_conn (idNonce i) -> e:epoch (HS.region c.hs) (HS.peer c.hs) 
  -> Lemma (requires 
            (let ctab = Mr.m_sel h0 conn_table in
	     let mstab = Mr.m_sel h0 Ms.ms_tab in
	     let old_hs_log = HH.sel h0 (HS.log c.hs) in
     	     let new_hs_log = HH.sel h1 (HS.log c.hs) in 
	     let rgn = HS.region c.hs in
	     Hh.contains_ref (Mr.as_rref conn_table) h0 /\
	     Hh.contains_ref (Mr.as_rref Ms.ms_tab) h0 /\
	     Hh.disjoint (HS.region c.hs) tls_region /\
	     Hh.contains_ref (HS.log c.hs) h0 /\
	     Hh.contains_ref (HS.log c.hs) h1 /\
	     mc_inv h0 /\ //we're initially in the invariant
	     i=hsId (Epoch.h e) /\ //the epoch has id it
	     (let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
	      let epochs = Hh.sel h0 (HS.log c.hs) in
      	      Map.contains h1 (StreamAE.State.region w) /\
	      (forall e. SeqProperties.mem e epochs ==> hsId (Epoch.h e) <> i) /\ //i is fresh for c
 	      Mm.sel mstab (i, rgn) = Some w /\ //we found the writer in the ms_tab
	      MM.sel ctab (idNonce i) = Some c /\ //we found the connection in the conn_table
	      Hh.modifies_one (HS.region c.hs) h0 h1 /\ //we just modified this connection's handshake region
	      Hh.modifies_rref (HS.region c.hs) !{Hh.as_ref (HS.log c.hs)} h0 h1 /\ //and within it, just the epochs log
	      new_hs_log = SeqProperties.snoc old_hs_log e))) //and we modified it by adding this epoch to it
	  (ensures mc_inv h1) //we're back in the invariant

#reset-options "--z3timeout 10 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

let add_epoch_ok h0 h1 i c e = 
  assert (Mr.m_sel h0 Ms.ms_tab = Mr.m_sel h1 Ms.ms_tab);
  assert (Mr.m_sel h0 conn_table = Mr.m_sel h1 conn_table);
  let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
  assert (Mr.m_sel h0 (StreamAE.ilog (StreamAE.State.log w)) = Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)));
  let ctab = Mr.m_sel h0 conn_table in
  let mstab = Mr.m_sel h0 Ms.ms_tab in
  let copt = Mm.sel ctab (idNonce i) in
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
  match Mm.sel mstab (j, s) with 
  | None -> admit()
  | Some wj -> 
    assume (StreamAE.State.region wj <> HS.region c.hs); //can see here why the post-condition fails ... need better separation invariants between the HS.log and the writer logs
    assume (HH.contains_ref (Mr.as_rref (StreamAE.ilog (StreamAE.State.log wj))) h0);
    assert (Mr.m_sel h0 (StreamAE.ilog (StreamAE.State.log wj)) = Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log wj)));
    admit()


//3. Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
//    --- we're in the first case, left disjunct (should be easy)


//4. Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
//    -- So, we cannot be in the Some w, None case, as this is only for bad writers
//    -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id

//    Note: we can prove that the having a doomed writer is a monotonic property of nonces

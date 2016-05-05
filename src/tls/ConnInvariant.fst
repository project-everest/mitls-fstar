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
  exists e. SeqProperties.mem e  (Hh.sel h (HS.log c.hs)) /\
      (let i' = Handshake.hsId (Handshake.Epoch.h e) in
        i=i' /\ StAE.stream_ae #i e.w == w)

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
 			 is_Some copt /\ registered i w (Some.v copt) h)))                         //it's been assigned to a connection

let mc_inv (h:HyperHeap.t) = ms_conn_invariant (Mr.m_sel h Ms.ms_tab) (Mr.m_sel h conn_table) h

//Checking the stability of the invariant

//1. Deriving a new key involves adding a new writer to the ms table (because we tried a lookup at id and it failed)
//   Easy: because a new log is empty and both cases of the conn table allow empty logs to be in ms

val ms_derive_is_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:id -> r:Hh.rid -> w:Ms.writer (i,r) 
  -> Lemma (requires 
		 Map.contains h1 (StreamAE.State.region w) /\
		 authId i /\ 
		 StAE.is_stream_ae i /\
		 mc_inv h0 /\ //we're initially in the invariant
		 Hh.modifies (Set.singleton tls_region) h0 h1 /\ //we just changed the tls_region
		 (let old_ms = Mr.m_sel h0 Ms.ms_tab in 
		  let new_ms = Mr.m_sel h1 Ms.ms_tab in
		  Mm.sel old_ms (i,r) = None /\
		  new_ms = Mm.upd old_ms (i,r) w) /\                                    //and the ms_tab only changed by adding w
		 Mr.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty)             //and w's log is empty
	 (ensures mc_inv h1)                                                       //we're back in the invariant
#reset-options "--log_queries"

let ms_derive_is_ok h0 h1 i r w =  ()

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

module ConnInvariant
open TLSConstants
open TLSInfo
open Handshake
open Connection

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module MS = MasterSecret
module N = Nonce
module I = IdNonce
module AE = StreamAE

type id = StreamAE.id
let r_conn (r:random) = c:connection{c.hs.nonce = r}

let pairwise_disjoint (m:MM.map' random r_conn) = 
    forall r1 r2. r1<>r2 /\ is_Some (MM.sel m r1) /\ is_Some (MM.sel m r2)
	     ==> HH.disjoint (Some.v (MM.sel m r1)).region  
		             (Some.v (MM.sel m r2)).region

type conn_table_t = MM.t tls_tables_region random r_conn pairwise_disjoint

let conn_table : conn_table_t = 
  MM.alloc #tls_tables_region #random #r_conn #pairwise_disjoint


type ms_tab = MM.map' AE.id MS.writer 
type c_tab  = MM.map' random r_conn 


let registered (i:id{StAE.is_stream_ae i}) (w:StreamAE.writer i) (c:connection) (h:HH.t) = 
  HH.disjoint (HS.region c.hs) tls_region /\
  HH.contains_ref (HS.log c.hs) h /\
  (exists e. SeqProperties.mem e  (HH.sel h (HS.log c.hs)) /\
      (let i' = Handshake.hsId (Handshake.Epoch.h e) in
        i=i' /\ StAE.stream_ae #i e.w == w))

let writer_separated_from_all_handshakes (#i:AE.id) (w:AE.writer i) (conn:c_tab) = 
  forall n.{:pattern (MM.sel conn n)}
       match MM.sel conn n with 
       | Some c -> HH.disjoint (HS.region (C.hs c)) (StreamAE.State.region w) 
       | None -> True

let ms_conn_inv (ms:ms_tab)
 		(conn:c_tab)
		(h:HyperHeap.t) 
		(i:id) 
   = authId i /\ StAE.is_stream_ae i ==>  //Focused only on TLS-1.3 for now, hence the is_stream_ae guard
     (match MM.sel ms i with 
      | None -> True
      | Some w -> 
	//technical: for framing; need to know that the writer's region exists
	Map.contains h (StreamAE.State.region w) /\  
	//separation: each writer is separated from every connection's handshake state, and from tls_tables_region
	(* HH.disjoint (StreamAE.State.region w) tls_tables_region /\ *)
	writer_separated_from_all_handshakes w conn /\
	//main application invariant:
	(MR.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty  \/   //the writer is either still unused; or
	             (let copt = MM.sel conn (I.nonce_of_id i) in
  		      is_Some copt /\ registered i w (Some.v copt) h)))            //it's been registered with the connection associated with its nonce

let ms_conn_invariant (ms:ms_tab)
 		      (conn:c_tab)
		      (h:HyperHeap.t) 
  = forall (i:id) .{:pattern (MM.sel ms i)} ms_conn_inv ms conn h i

let mc_inv (h:HyperHeap.t) = 
    HH.as_ref (MR.as_rref conn_table) =!= HH.as_ref (MR.as_rref MS.ms_tab)
    /\ ms_conn_invariant (MR.m_sel h MS.ms_tab) (MR.m_sel h conn_table) h

//Checking the stability of the invariant

//1. Deriving a new key involves adding a new writer to the ms table (because we tried a lookup at id and it failed)
//   Easy: because a new log is empty and both cases of the conn table allow empty logs to be in ms
val ms_derive_is_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:AE.id -> w:MS.writer i 
  -> Lemma (requires 
	        (let conn = MR.m_sel h0 conn_table in
	         let old_ms = MR.m_sel h0 MS.ms_tab in 
		 let new_ms = MR.m_sel h1 MS.ms_tab in
		 HH.contains_ref (MR.as_rref conn_table) h0 /\
		 HH.contains_ref (MR.as_rref MS.ms_tab) h0  /\
		 Map.contains h1 (StreamAE.State.region w)  /\
		 mc_inv h0 /\ //we're initially in the invariant
		 (* HH.disjoint (StreamAE.State.region w) tls_tables_region /\ *)
		 writer_separated_from_all_handshakes w conn /\
		 HH.modifies (Set.singleton tls_tables_region) h0 h1 /\ //we just changed the tls_region
		 HH.modifies_rref tls_tables_region !{HH.as_ref (MR.as_rref MS.ms_tab)} h0 h1 /\ //and within it, at most the ms_tab
		 (old_ms = new_ms //either ms_tab didn't change at all
		  \/ (MM.sel old_ms i = None /\
		     new_ms = MM.upd old_ms i w /\ //or we just added w to it
	   	     (TLSInfo.authId i ==> MR.m_sel h1 (AE.ilog (StreamAE.State.log w)) = Seq.createEmpty))))) //and it is a fresh log
	 (ensures (mc_inv h1))
(* assume val gadmit: f:(unit -> GTot Type0) -> Tot (u:unit{f()}) *)

let ms_derive_is_ok h0 h1 i w = 
  let aux :  j:id -> Lemma (let new_ms = MR.m_sel h1 MS.ms_tab in
			  let new_conn = MR.m_sel h1 conn_table in
			  ms_conn_inv new_ms new_conn h1 j) =
    fun j -> 			    
      let old_ms = MR.m_sel h0 MS.ms_tab in 
      let new_ms = MR.m_sel h1 MS.ms_tab in
      (* let old_conn = MR.m_sel h0 conn_table in *)
      let new_conn = MR.m_sel h1 conn_table in
      assert (ms_conn_inv new_ms new_conn h1 i);
      (* assert (old_conn = new_conn); *)
      if (authId j && StAE.is_stream_ae j)
      then match MM.sel new_ms j with 
           | None -> ()
           | Some ww -> 
     	     if ww=w 
	     then ()
	     else assert (Some ww=MM.sel old_ms j)
      else () in
  qintro aux

(* Here, we actually call MS.derive and check that it's post-condition 
   is sufficeitn to call ms_derive_is_ok and re-establish the invariant *)
let try_ms_derive (r:HH.rid) (i:AE.id) 
  : ST (AE.writer i)
       (requires (fun h -> 
       	   HH.disjoint r tls_region /\
	   N.registered (I.nonce_of_id i) r /\
	   authId i /\
	   mc_inv h))
       (ensures (fun h0 w h1 -> 
	   mc_inv h1))
  = let h0 = ST.get () in
    MR.m_recall conn_table;
    MR.m_recall MS.ms_tab;
    let w = MasterSecret.derive r i in 
    recall_region (StreamAE.State.region w);
    let h1 = ST.get () in 
    ms_derive_is_ok h0 h1 i w;
    w

let all_epoch_writers_share_conn_nonce (c:connection) (i:AE.id) (wi:AE.writer i) (h:HH.t)
    : Lemma (requires (registered i wi c h))
            (ensures (I.nonce_of_id i = c.hs.nonce))
    = ()

#reset-options "--z3timeout 10 --initial_ifuel 2 --initial_fuel 0"

let writer_registered_to_at_most_one_connection 
    (n1:random) (c1:r_conn n1)
    (n2:random) (c2:r_conn n2{n1 <> n2})
    (i:AE.id {I.nonce_of_id i = n1}) (w:AE.writer i) (h:HH.t)
    : Lemma (requires (registered i w c1 h))
	    (ensures (~ (registered i w c2 h)))
    = ()

let writer_region_within_connection
    (n:random) (c:r_conn n)
    (i:AE.id {I.nonce_of_id i = n}) (w:AE.writer i) (h:HH.t)
    : Lemma (requires (registered i w c h))
	    (ensures (HH.includes (C.region c) (StreamAE.State.region w)))
    = ()

#reset-options "--z3timeout 10 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

//2. Adding a new epoch to a connection c, with a fresh index (hdId i) for c
//      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
//      -- we need to show that the (exists e. SeqProperties.mem ...) is false (because of the fresh index for c)
//      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)
val register_writer_in_epoch_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:AE.id{authId i}
		-> c:r_conn (I.nonce_of_id i) -> e:epoch (HS.region c.hs) (I.nonce_of_id i)
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
	     i=hsId (Epoch.h e) /\ //the epoch has id i
	     (let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
	      let epochs = HH.sel h0 (HS.log c.hs) in
              N.registered (I.nonce_of_id i) (HH.parent (StreamAE.State.region w)) /\ 
	      HH.disjoint (HH.parent (StreamAE.State.region w)) tls_region /\
      	      Map.contains h1 (StreamAE.State.region w) /\
	      (forall e. SeqProperties.mem e epochs ==> hsId (Epoch.h e) <> i) /\ //i is fresh for c
 	      MM.sel mstab i = Some w /\ //we found the writer in the ms_tab
	      MM.sel ctab (I.nonce_of_id i) = Some c /\ //we found the connection in the conn_table
	      HH.modifies_one (HS.region c.hs) h0 h1 /\ //we just modified this connection's handshake region
	      HH.modifies_rref (HS.region c.hs) !{HH.as_ref (HS.log c.hs)} h0 h1 /\ //and within it, just the epochs log
	      new_hs_log = SeqProperties.snoc old_hs_log e))) //and we modified it by adding this epoch to it
	  (ensures mc_inv h1) //we're back in the invariant


#reset-options "--z3timeout 10 --initial_ifuel 2 --initial_fuel 0"

let register_writer_in_epoch_ok h0 h1 i c e = 
  assert (MR.m_sel h0 MS.ms_tab = MR.m_sel h1 MS.ms_tab);
  assert (MR.m_sel h0 conn_table = MR.m_sel h1 conn_table);
  let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
  assert (MR.m_sel h0 (StreamAE.ilog (StreamAE.State.log w)) = MR.m_sel h1 (StreamAE.ilog (StreamAE.State.log w)));
  let ctab = MR.m_sel h0 conn_table in
  let mstab = MR.m_sel h0 MS.ms_tab in
  let copt = MM.sel ctab (I.nonce_of_id i) in
  let old_hs_log = HH.sel h0 (HS.log c.hs) in
  assert (is_Some copt);
  assert (~ (registered i w (Some.v copt) h0));
  MonotoneSeq.lemma_mem_snoc old_hs_log e;
  assert (registered i w (Some.v copt) h1);
  let j : id  = magic () in
  let nonce = I.nonce_of_id i in 
  assume (StAE.is_stream_ae j);
  assume (authId j);
  match MM.sel mstab j with
  | None -> admit()
  | Some wj ->
    assume (registered j wj c h0);
    assert (HH.disjoint (StreamAE.State.region wj) (HS.region c.hs)); //can see here why the post-condition fails ... need better separation invariants between the HS.log and the writer logs
    assume (HH.contains_ref (MR.as_rref (StreamAE.ilog (StreamAE.State.log wj))) h0);
    assert (MR.m_sel h0 (StreamAE.ilog (StreamAE.State.log wj)) = MR.m_sel h1 (StreamAE.ilog (StreamAE.State.log wj)));
    admit()


//3. Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
//    --- we're in the first case, left disjunct (should be easy)


//4. Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
//    -- So, we cannot be in the Some w, None case, as this is only for bad writers
//    -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id

//    Note: we can prove that the having a doomed writer is a monotonic property of nonces

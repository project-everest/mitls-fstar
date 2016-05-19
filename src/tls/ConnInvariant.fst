module ConnInvariant
open TLSConstants
open TLSInfo
open Handshake
open Connection

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module MS = MasterSecret
module N  = Nonce
module I  = IdNonce
module AE = StreamAE

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

type id = StreamAE.id
//The type of connection with a particular nonce
//   `r_conn n` should never really have more than 1 inhabitant, 
//   one of the purposes of the conn_table defined below is to enforce that
type r_conn (nonce:random) = c:connection{c.hs.nonce = nonce}

//The connection associated with an id
type i_conn (i:id) = r_conn (I.nonce_of_id i)

(* -------------------------------------------------------------------------------- 
   The nonce to connection table, defined in a few steps: 

   1. The table is a partial map from (nonce:random) to (r_conn nonce)
   
   2. We have an `pairwise_disjoint` invariant on the 
      table that connections associated with distinct nonces 
      live in distinct regions. 
  -------------------------------------------------------------------------------- *)
let pairwise_disjoint (m:MM.map' random r_conn) = 
    forall r1 r2.{:pattern (is_Some (MM.sel m r1));
		      (is_Some (MM.sel m r2))}
	r1<>r2 /\ is_Some (MM.sel m r1) /\ is_Some (MM.sel m r2)
	     ==> HH.disjoint (Some.v (MM.sel m r1)).region  
		             (Some.v (MM.sel m r2)).region

type conn_tab_t = MM.t tls_tables_region random r_conn pairwise_disjoint

let conn_tab : conn_tab_t = 
  MM.alloc #tls_tables_region #random #r_conn #pairwise_disjoint

(*** MAIN STATEFUL INVARIANT ***)
(* --------------------------------------------------------------------------------
   We define a joint, stateful invariant to relate the contents 
   of MasterSecret.ms_tab and conn_tab above.

   The main application level invariant is:
     Every writer in the ms_tab has an empty log
     unless it has been registered within some epoch of a connection

   To maintain this invariant, we strengthen it with some technical
   nuances, mainly related to framing.
  -------------------------------------------------------------------------------- *)

//MS.ms_tab is a monontonic reference to an ms_t
type ms_t = MM.map' AE.id MS.writer 

//conn_tab is a monotonic reference to a c_t
type c_t  = MM.map' random r_conn 

//w is registered with c, in state h
let registered (i:id{StAE.is_stream_ae i}) (w:StreamAE.writer i) (c:connection) (h:HH.t) = 
  (exists e. SeqProperties.mem e  (HH.sel h (HS.log c.hs)) /\   //one of c's epochs, e
      (let i' = Handshake.hsId (Handshake.Epoch.h e) in   //has an id corresponding to i
        i=i' /\ StAE.stream_ae #i e.w == w))               //and holds w as as its writer
  /\ HH.contains_ref (HS.log c.hs) h                       //technical: the heap contains c's handshake log
	
//The main invariant, relating an ms_tab and a conn_tab at index i, in state h
let ms_conn_inv (ms:ms_t)
 		(conn:c_t)
		(h:HyperHeap.t) 
		(i:id) 
   = authId i /\ StAE.is_stream_ae i ==>  //Focused only on TLS-1.3 for now, hence the is_stream_ae guard
     (match MM.sel ms i with 
      | None -> True
      | Some w -> 
	//technical: for framing; need to know that the writer's region exists
	Map.contains h (StreamAE.State.region w) /\  
	//technical: for framing; need to know that when idealized, the log also exists 
	(authId i ==> HH.contains_ref (MR.as_rref (StreamAE.ilog (StreamAE.State.log w))) h) /\
	//main application invariant:
	(MR.m_sel h (StreamAE.ilog (StreamAE.State.log w)) = Seq.createEmpty  \/   //the writer is either still unused; or
	             (let copt = MM.sel conn (I.nonce_of_id i) in
  		      is_Some copt /\ registered i w (Some.v copt) h)))            //it's been registered with the connection associated with its nonce

//The main invariant, for all AE.ids
let ms_conn_invariant (ms:ms_t)
 		      (conn:c_t)
		      (h:HyperHeap.t) 
  = forall (i:id) .{:pattern (MM.sel ms i)} ms_conn_inv ms conn h i

//A technical condition for framing: 
//    Every handshake region exists in the current heap
let handshake_regions_exists (conn:c_t) (h:HH.t) = 
  forall n.{:pattern (is_Some (MM.sel conn n))}
      is_Some (MM.sel conn n) 
       ==> (let hs_rgn = HS.region (C.hs (Some.v (MM.sel conn n))) in 
 	    Map.contains h hs_rgn /\
	    HH.disjoint hs_rgn tls_tables_region)

//Finally packaging it up as the main invariant:
let mc_inv (h:HyperHeap.t) = 
    HH.as_ref (MR.as_rref conn_tab) =!= HH.as_ref (MR.as_rref MS.ms_tab)     //Technical:the conn_tab and ms_tab are not aliased
    /\ HH.contains_ref (MR.as_rref conn_tab) h                                //Technical:the heap contains the ms_tab
    /\ HH.contains_ref (MR.as_rref MS.ms_tab) h                               //Technical:the heap contains the conn_tab
    /\ handshake_regions_exists (MR.m_sel h conn_tab) h                       //Technical:every logged connection's handshake exists
    /\ ms_conn_invariant (MR.m_sel h MS.ms_tab) (MR.m_sel h conn_tab) h       //Main joint stateful invariant

(*** PROVING THE STABILITY OF mc_inv ***)
(* --------------------------------------------------------------------------------
   There are 4 main cases:
     1. Deriving a new writer, using MS.derive 
     2. Registering a writer with a connection
     3. Mutating the log of some writer
     4. Adding a new connection
  -------------------------------------------------------------------------------- *)     

(* 
   Case 1:
     Deriving a new key involves adding a new writer to the ms table (because we tried a lookup at id and it failed)
     It's ok, because a new log is empty and adding an empty writer is fine regardless of the connections 
*)
val ms_derive_is_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:AE.id -> w:MS.writer i 
  -> Lemma (requires 
	        (let conn = MR.m_sel h0 conn_tab in
	         let old_ms = MR.m_sel h0 MS.ms_tab in 
		 let new_ms = MR.m_sel h1 MS.ms_tab in
		 mc_inv h0 /\ //we're initially in the invariant
		 Map.contains h1 (StreamAE.State.region w)  /\ //the writer we're adding w is in an existing region
		 is_epoch_rgn (StreamAE.State.region w) /\     //that it is an epoch region
		 is_epoch_rgn (HH.parent (StreamAE.State.region w)) /\ //and it's parent is as well (needed for the ms_tab invariant)
		 HH.modifies (Set.singleton tls_tables_region) h0 h1 /\ //we just changed the tls_tables_region
		 HH.modifies_rref tls_tables_region !{HH.as_ref (MR.as_rref MS.ms_tab)} h0 h1 /\ //and within it, at most the ms_tab
		 (old_ms = new_ms //either ms_tab didn't change at all  (because we found w in the table already)
		  \/ (MM.sel old_ms i = None /\ //or, we had to generate a fresh writer w
		     new_ms = MM.upd old_ms i w /\ //and we just added w to the table
	   	     (TLSInfo.authId i ==>  //and if we're idealizing i
		         HH.contains_ref (MR.as_rref (StreamAE.ilog (StreamAE.State.log w))) h1 /\  //the log exists in h1
			 MR.m_sel h1 (AE.ilog (StreamAE.State.log w)) = Seq.createEmpty)))))       //and w is as yet unused
	 (ensures (mc_inv h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let ms_derive_is_ok h0 h1 i w = 
  let aux :  j:id -> Lemma (let new_ms = MR.m_sel h1 MS.ms_tab in
  			  let new_conn = MR.m_sel h1 conn_tab in
  			  ms_conn_inv new_ms new_conn h1 j) =
    fun j ->
      let old_ms = MR.m_sel h0 MS.ms_tab in
      let new_ms = MR.m_sel h1 MS.ms_tab in
      if authId j && StAE.is_stream_ae j
      then match MM.sel new_ms j with
           | None -> ()
           | Some ww ->
      	     if ww=w
      	     then ()
      	     else assert (Some ww=MM.sel old_ms j)
      else () in
  qintro aux

(* Here, we actually call MS.derive and check that its post-condition
   is sufficient to call ms_derive_is_ok and re-establish the invariant *)
let try_ms_derive (epoch_region:rgn) (i:AE.id)
  : ST (AE.writer i)
       (requires (fun h ->
       	   HH.disjoint epoch_region tls_region /\
	   N.registered (I.nonce_of_id i) epoch_region /\
	   is_epoch_rgn epoch_region /\
	   authId i /\
	   mc_inv h))
       (ensures (fun h0 w h1 ->
	   mc_inv h1))
  = let h0 = ST.get () in
    MR.m_recall conn_tab;
    MR.m_recall MS.ms_tab;
    let w = MasterSecret.derive epoch_region i in
    MR.m_recall (AE.ilog (StreamAE.State.log w));
    let h1 = ST.get () in
    ms_derive_is_ok h0 h1 i w;
    w

(* Some simply sanity checks on the association between connections, ids, nonces, writers regions *)
let all_epoch_writers_share_conn_nonce (c:connection) (i:AE.id) (wi:AE.writer i) (h:HH.t)
    : Lemma (requires (registered i wi c h))
            (ensures (I.nonce_of_id i = c.hs.nonce))
    = ()

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

//A wrapper around a Sequence lemma ... should move it
let lemma_mem_snoc (s:FStar.Seq.seq 'a) (x:'a)
  : Lemma (ensures (forall y.{:pattern (SeqProperties.mem y (SeqProperties.snoc s x))}
      SeqProperties.mem y (SeqProperties.snoc s x) <==> SeqProperties.mem y s \/ x=y))
  = SeqProperties.lemma_mem_snoc s x


(* Case 2:
     Adding a new epoch to a connection c, with a fresh index (hdId i) for c
      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
      -- we need to show that the (exists e. SeqProperties.mem ...) is false (because of the fresh index for c)
      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)
*)
val register_writer_in_epoch_ok: h0:HyperHeap.t -> h1:HyperHeap.t -> i:AE.id{authId i}
		-> c:r_conn (I.nonce_of_id i) -> e:epoch (HS.region c.hs) (I.nonce_of_id i)
  -> Lemma (requires
            (let ctab = MR.m_sel h0 conn_tab in
	     let mstab = MR.m_sel h0 MS.ms_tab in
	     let old_hs_log = HH.sel h0 (HS.log c.hs) in
     	     let new_hs_log = HH.sel h1 (HS.log c.hs) in
	     let rgn = HS.region c.hs in
	     mc_inv h0 /\ //we're initially in the invariant
	     HH.contains_ref (HS.log c.hs) h0 /\
	     HH.contains_ref (HS.log c.hs) h1 /\
	     i=hsId (Epoch.h e) /\ //the epoch has id i
	     (let w = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
	      let epochs = HH.sel h0 (HS.log c.hs) in
              N.registered (I.nonce_of_id i) (HH.parent (StreamAE.State.region w)) /\  //the writer's parent region is registered in the nonce table
	      HH.disjoint (HH.parent (StreamAE.State.region w)) tls_region /\          //technical: ... needed just for well-formedness of the rest of the formula
	      MR.witnessed (MR.rid_exists (StreamAE.State.region w)) /\                //technical: ... needed just for well-formedness of the rest of the formula
	      (forall e. SeqProperties.mem e epochs ==> hsId (Epoch.h e) <> i) /\            //i is fresh for c
 	      MM.sel mstab i = Some w /\ //we found the writer in the ms_tab
	      MM.sel ctab (I.nonce_of_id i) = Some c /\ //we found the connection in the conn_table
      	      HH.modifies_one (HS.region c.hs) h0 h1 /\ //we just modified this connection's handshake region
	      HH.modifies_rref (HS.region c.hs) !{HH.as_ref (HS.log c.hs)} h0 h1 /\ //and within it, just the epochs log
	      new_hs_log = SeqProperties.snoc old_hs_log e))) //and we modified it by adding this epoch to it
	  (ensures mc_inv h1) //we're back in the invariant
let register_writer_in_epoch_ok h0 h1 i c e =
  (* This proof can be simplified a lot.
     But, retaining it since it is actually quite informative
     about the structure of the invariant.
  *)
  let aux :  j:id -> Lemma (let new_ms = MR.m_sel h1 MS.ms_tab in
			   let new_conn = MR.m_sel h1 conn_tab in
			   ms_conn_inv new_ms new_conn h1 j) =
    fun j ->
      let old_ms = MR.m_sel h0 MS.ms_tab in
      let new_ms = MR.m_sel h1 MS.ms_tab in
      let old_conn = MR.m_sel h0 conn_tab in
      let new_conn = MR.m_sel h1 conn_tab in
      let old_hs_log = HH.sel h0 (HS.log c.hs) in
      let wi = StAE.stream_ae #i (Epoch.w e) in //the epoch writer
      let nonce = I.nonce_of_id i in
      lemma_mem_snoc old_hs_log e; //this lemma shows that everything that was registered to c remains registered to it
      assert (old_ms = new_ms);
      assert (old_conn = new_conn);
      cut (is_Some (MM.sel old_conn nonce)); //this cut is useful for triggering the pairwise_disjointness quantifier
      if (authId j && StAE.is_stream_ae j)
      then match MM.sel new_ms j with
           | None -> () //nothing allocated at id j yet; easy
           | Some wj ->
      	     let log_ref = StreamAE.ilog (StreamAE.State.log wj) in
      	     assert (Map.contains h1 (StreamAE.State.region wj)); //its region exists; from the 1st technical clause in ms_conn_inv
      	     assert (HH.contains_ref (MR.as_rref log_ref) h1);    //its log exists; from the 2nd technical clause in ms_conn_inv
	     assert (is_epoch_rgn (StreamAE.State.region wj));    //from the separation clause in ms_con_inv
      	     let log0 = MR.m_sel h0 log_ref in
      	     let log1 = MR.m_sel h1 log_ref in
      	     assert (log0 = log1); //the properties in the three asserts above are needed to show that j's log didn't change just by registering i
      	     if log0 = Seq.createEmpty
      	     then () //if the log remains empty, it's easy
      	     else if wj=wi
	     then () //if j is in fact the same as i, then i gets registered at the end, so that's easy too
	     else let nonce_j = I.nonce_of_id j in
		  if nonce_j = nonce
		  then assert (registered j wj c h0) //if j and i share the same nonce, then j is registered to c and c's registered writers only grows
		  else (match MM.sel old_conn nonce_j with
		        | None -> assert false //we've already established that the log is non-empty; so j must be registered and this case says that it is not
			| Some c' ->
			  assert (registered j wj c' h0); //it's registered initially
			  assert (HH.disjoint (C.region c) (C.region c')); //c's region is disjoint from c'; since the conn_tab is pairwise_disjoint
			  assert (registered j wj c' h1)) //so it remains registered
      else () (* not ideal; nothing much to say *) in
  qintro aux

(* Case 3:
    Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
    Basically, we have enough framing to know that nothing else changed if just the log changed.
    And since the log is registered, it is allowed to change, and it remains registered
*)
val mutate_registered_writer_ok : h0:HH.t -> h1:HH.t -> i:AE.id{authId i} -> w:MS.writer i -> c:r_conn (I.nonce_of_id i) -> Lemma
    (requires (mc_inv h0 /\                                       //initially in the invariant
	       HH.modifies_one (StreamAE.State.region w) h0 h1 /\ //we modified at most the writer's region
	       registered i w c h0 /\                             //the writer is registered in c
	       MM.sel (MR.m_sel h0 MS.ms_tab) i = Some w   /\     //the writer is logged in the ms_tab
	       MM.sel (MR.m_sel h0 conn_tab) (I.nonce_of_id i) = Some c /\ //the connection is logged in the conn_table
	       HH.contains_ref (MR.as_rref (StreamAE.ilog (StreamAE.State.log w))) h1)) //We say that we changed the w.region; but that doesn't necessarily mean that its log remains
    (ensures (mc_inv h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mutate_registered_writer_ok h0 h1 i w c = (* () *)
(* a slightly more detailed proof: *)
    let new_ms = MR.m_sel h1 MS.ms_tab in
    let new_conn = MR.m_sel h1 conn_tab in
    let aux :  j:id -> Lemma (ms_conn_inv new_ms new_conn h1 j) =
      fun j ->
    	if (authId j && StAE.is_stream_ae j)
        then match MM.sel new_ms j with //the case analysis is to trigger the pattern guarding MasterSecret.region_injective
             | None -> ()
             | Some wj -> () //basically, when i=j, the proof is easy as i remains registered; if i<>j then j didn't change since their regions are distinct
    	else () in
    qintro aux

(* Case 4:
    Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
     -- So, we cannot be in the Some w, None case, as this is only for bad writers
     -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id
    Note: we can prove that the having a doomed writer is a monotonic property of nonces
    TODO: We don't handle doomed writers at all yet
*)

(* An auxiliary formula, needed as a pre-condition to add a c to conn_tab *)
let conn_hs_region_exists (c:connection) (h:HH.t) =
   let hs_rgn = HS.region c.hs in
   Map.contains h hs_rgn /\
   HH.disjoint hs_rgn tls_tables_region

val add_connection_ok: h0:HH.t -> h1:HH.t -> i:id -> c:i_conn i -> Lemma
  (requires (mc_inv h0 /\ //we're initially in the invariant
	     HH.modifies (Set.singleton tls_tables_region) h0 h1 /\  //only modified some table
	     HH.modifies_rref tls_tables_region !{HH.as_ref (MR.as_rref conn_tab)} h0 h1 /\ //in fact, only conn_tab
	     conn_hs_region_exists c h0 /\ //we need to know that c is well-formed
	     (let old_conn = MR.m_sel h0 conn_tab in
    	      let new_conn = MR.m_sel h1 conn_tab in
	      let nonce = I.nonce_of_id i in
	      MM.sel old_conn nonce = None /\        //c wasn't in the table initially
	      new_conn = MM.upd old_conn nonce c))) //and the conn_tab changed just by adding c
  (ensures (mc_inv h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let add_connection_ok h0 h1 i c =
    cut (HH.contains_ref (MR.as_rref conn_tab) h1);
    let old_ms = MR.m_sel h0 MS.ms_tab in
    let new_ms = MR.m_sel h1 MS.ms_tab in
    let old_conn = MR.m_sel h0 conn_tab in
    let new_conn = MR.m_sel h1 conn_tab in
    let hs_region_exists : n:random -> Lemma
    	(is_Some (MM.sel new_conn n) ==> conn_hs_region_exists (Some.v (MM.sel new_conn n)) h1) =
      fun n -> match MM.sel new_conn n with
    	    | None -> ()
    	    | Some c' -> if c = c' then ()
    		        else cut (c' = Some.v (MM.sel old_conn n)) in
    qintro hs_region_exists;
    cut (handshake_regions_exists new_conn h1)

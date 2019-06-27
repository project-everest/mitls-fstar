module ConnInvariant

open Mem
open TLSConstants
open TLSInfo
open Negotiation
open Epochs
open Handshake
open Connection

module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module MonSeq = FStar.Monotonic.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module HMS = FStar.Monotonic.HyperStack
module HMH = FStar.Monotonic.Heap
module HH = FStar.Monotonic.HyperHeap
module MS = MasterSecret
module N  = Nonce
module I  = IdNonce
module AE = StreamAE

//17-04-13 this file is verified but not yet used.
//17-04-13 it should probably depend on StAE instead of StreamAE.

////////////////////////////////////////////////////////////////////////////////
//Framing writes to an epoch
////////////////////////////////////////////////////////////////////////////////
let epoch_regions_exist (s:hs) (h0:HS.mem) =
  let epochs = logT s h0 in
  Map.contains (HS.HS?.h h0) (region_of s)
  /\ (forall (k:nat{k < Seq.length epochs}).{:pattern (Seq.index epochs k)}
      let wr = writer_epoch (Seq.index epochs k) in
      Map.contains (HS.HS?.h h0) (StAE.region wr))

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val frame_epoch_writer: s:hs -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (let j = iT s Writer h0 in
                   let epochs = logT s h0 in
                     Seq.indexable epochs j
                   /\ epoch_regions_exist s h0
                   /\ (let e_j = Seq.index epochs j in
                      HH.modifies_one (StAE.region (writer_epoch e_j)) (HS.HS?.h h0) (HS.HS?.h h1))))
        (ensures (let epochs0 = logT s h0 in
                  let epochs1 = logT s h1 in
                  let j = iT s Writer h0 in
                  epochs0 == epochs1
                  /\(forall (k:nat{k < Seq.length epochs0 /\ j<>k}).
                      let wr = writer_epoch (Seq.index epochs0 k) in
                      HH.equal_on (Set.singleton (StAE.region wr)) (HS.HS?.h h0) (HS.HS?.h h1))))

let frame_epoch_writer s h0 h1 =
  let epochs = logT s h0 in
  let j = iT s Writer h0 in
  let e_j = Seq.index epochs j in
  reveal_epoch_region_inv e_j;
  let wj = writer_epoch e_j in
  let aux : (k:nat{k < Seq.length epochs /\ j<>k}) -> Lemma
    (let wr = writer_epoch (Seq.index epochs k) in
     HH.equal_on (Set.singleton (StAE.region wr)) (HS.HS?.h h0) (HS.HS?.h h1)) =
     fun k -> let wk = writer_epoch (Seq.index epochs k) in
	   reveal_epochs_inv'();
	   assert (HH.disjoint (StAE.region wk) (StAE.region wj)) in
  FStar.Classical.forall_intro aux

////////////////////////////////////////////////////////////////////////////////
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

//BIG TODO: Need to generalize this to all TLSInfo.id, or at least StAE.stae_id
type id = StreamAE.id
//The type of connection with a particular nonce
//   `r_conn n` should never really have more than 1 inhabitant,
//   one of the purposes of the conn_table defined below is to enforce that
type r_conn (nonce:random) = c:connection{random_of c.hs == nonce}

//The connection associated with an id
type i_conn (i:id) = r_conn (nonce_of_id i)

(* --------------------------------------------------------------------------------
   The nonce to connection table, defined in a few steps:

   1. The table is a partial map from (nonce:random) to (r_conn nonce)

   2. We have an `pairwise_disjoint` invariant on the
      table that connections associated with distinct nonces
      live in distinct regions.
  -------------------------------------------------------------------------------- *)
let pairwise_disjoint (m:MDM.partial_dependent_map random r_conn) =
    forall r1 r2.{:pattern (Some? (DM.sel m r1));
                      (Some? (DM.sel m r2))}
        r1<>r2 /\ Some? (DM.sel m r1) /\ Some? (DM.sel m r2)
             ==> HH.disjoint (Some?.v (DM.sel m r1)).region
                              (Some?.v (DM.sel m r2)).region

type conn_tab_t = MDM.t tls_tables_region random r_conn pairwise_disjoint

let conn_tab : conn_tab_t =
  MDM.alloc ()

(*** DEFINING MAIN STATEFUL INVARIANT ***)
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
type ms_t = MDM.map AE.id MS.writer

//conn_tab is a monotonic reference to a c_t
type c_t  = MDM.map random r_conn

//w is registered with c, in state h
let registered (i:id{StAE.is_stream i}) (w:StreamAE.writer i) (c:connection) (h:HS.mem) =
  (exists e. (epochs c h) `Seq.contains` e  /\               //one of c's epochs, e
      (let i' = Epochs.epoch_id e in   //has an id corresponding to i
        equals #id i i' /\ StAE.stream_state #i e.w == w))               //and holds w as as its writer
  /\ MonSeq.i_contains (MkEpochs?.es #(region_of c.hs) #(random_of c.hs) (epochs_of c.hs)) h                         //technical: the heap contains c's handshake log

//The main invariant, relating an ms_tab and a conn_tab at index i, in state h
let ms_conn_inv (ms:ms_t)
                (conn:c_t)
                (h:HS.mem)
                (i:id)
   = authId i /\ StAE.is_stream i ==>  //Focused only on TLS-1.3 for now, hence the is_stream guard
     (match MDM.sel ms i with
      | None -> True
      | Some w ->
        let log_as_hsref =  (StreamAE.ilog (StreamAE.State?.log w)) in
        //technical: for framing; need to know that the writer's region exists
        Map.contains (HS.HS?.h h) (StreamAE.State?.region w) /\
        //technical: for framing; need to know that when idealized, the log also exists
        (authId i ==> HMS.contains h log_as_hsref) /\
        //main application invariant:
        (HS.sel h (StreamAE.ilog (StreamAE.State?.log w)) == Seq.empty  \/   //the writer is either still unused; or
                     (let copt = MDM.sel conn (nonce_of_id i) in
                      Some? copt /\ registered i w (Some?.v copt) h)))            //it's been registered with the connection associated with its nonce

//The main invariant, for all AE.ids
let ms_conn_invariant (ms:ms_t)
                      (conn:c_t)
                      (h:HS.mem)
  = forall (i:id) .{:pattern (MDM.sel ms i)} ms_conn_inv ms conn h i

//A technical condition for framing:
//    Every handshake region exists in the current heap
let handshake_regions_exists (conn:c_t) (h:HH.hmap) =
  forall n.{:pattern (Some? (MDM.sel conn n))}
      Some? (MDM.sel conn n)
       ==> (let hs_rgn = region_of (C?.hs (Some?.v (MDM.sel conn n))) in
            Map.contains h hs_rgn /\
            HS.disjoint hs_rgn tls_tables_region)

//Finally packaging it up as the main invariant:
let mc_inv (h:HS.mem) =
    let conn_tab_as_hsref =  conn_tab in
    let ms_tab_as_hsref =  MS.ms_tab in
    (HMH.addr_of (HS.as_ref conn_tab_as_hsref) <> HMH.addr_of (HS.as_ref ms_tab_as_hsref)) //Technical:the conn_tab and ms_tab are not aliased
    /\ HS.contains h conn_tab_as_hsref                                                     //Technical:the heap contains the ms_tab
    /\ HS.contains h ms_tab_as_hsref                                                       //Technical:the heap contains the conn_tab
    /\ handshake_regions_exists (HS.sel h conn_tab) (HS.HS?.h h)                           //Technical:every logged connection's handshake exists
    /\ ms_conn_invariant (HS.sel h MS.ms_tab) (HS.sel h conn_tab) h                        //Main joint stateful invariant

(*** PROVING THE STABILITY OF mc_inv ***)
(* --------------------------------------------------------------------------------
   There are 4 main invariant-preservation cases, each with its lemma
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
val ms_derive_is_ok: h0:HS.mem -> h1:HS.mem -> i:AE.id -> w:MS.writer i
  -> Lemma (requires
                (let conn = HS.sel h0 conn_tab in
                 let old_ms = HS.sel h0 MS.ms_tab in
                 let new_ms = HS.sel h1 MS.ms_tab in
                 let ms_tab_as_hsref =  MS.ms_tab in
                 mc_inv h0 /\ //we're initially in the invariant
                 Map.contains (HS.HS?.h h1) (StreamAE.State?.region w)  /\ //the writer we're adding w is in an existing region
                 is_epoch_rgn (StreamAE.State?.region w) /\     //that it is an epoch region
                 is_epoch_rgn (HS.parent (StreamAE.State?.region w)) /\ //and it's parent is as well (needed for the ms_tab invariant)
                 HS.modifies_transitively (Set.singleton tls_tables_region) h0 h1 /\ //we just changed the tls_tables_region
                 HS.modifies_ref tls_tables_region (Set.singleton (Heap.addr_of (HS.as_ref ms_tab_as_hsref))) h0 h1 /\ //and within it, at most the ms_tab
                 (old_ms == new_ms //either ms_tab didn't change at all  (because we found w in the table already)
                  \/ (MDM.sel old_ms i == None /\ //or, we had to generate a fresh writer w
                     new_ms == MDM.upd old_ms i w /\ //and we just added w to the table
                     (TLSInfo.authId i ==>  //and if we're idealizing i
                         (let log_as_hsref =  (StreamAE.ilog (StreamAE.State?.log w)) in
                          HS.contains h1 log_as_hsref /\  //the log exists in h1
                          HS.sel h1 (AE.ilog (StreamAE.State?.log w)) == Seq.empty))))))       //and w is as yet unused
         (ensures (mc_inv h1))
val invertOption : a:Type -> Lemma
  (requires True)
  (ensures (forall (x:option a). None? x \/ Some? x))
  [SMTPat (option a)]
let invertOption a = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let ms_derive_is_ok h0 h1 i w =
  let aux :  j:id -> Lemma (let new_ms = HS.sel h1 MS.ms_tab in
                          let new_conn = HS.sel h1 conn_tab in
                          ms_conn_inv new_ms new_conn h1 j) =
    fun j ->
      let old_ms = HS.sel h0 MS.ms_tab in
      let new_ms = HS.sel h1 MS.ms_tab in
      if authId j && StAE.is_stream j
      then match MDM.sel new_ms j with
           | None -> ()
           | Some ww ->
             if i=j
             then ()
             else assert (Some ww==MDM.sel old_ms j)
      else () in
  FStar.Classical.forall_intro aux

(* Here, we actually call MS.derive and check that its post-condition
   is sufficient to call ms_derive_is_ok and re-establish the invariant *)
let try_ms_derive (epoch_region:rgn) (i:AE.id)
  : ST (AE.writer i)
       (requires (fun h ->
           HS.disjoint epoch_region tls_region /\
           N.registered (nonce_of_id i) epoch_region /\
           is_epoch_rgn epoch_region /\
           authId i /\
           mc_inv h))
       (ensures (fun h0 w h1 ->
           mc_inv h1))
  = let h0 = get () in
    HST.recall conn_tab;
    HST.recall MS.ms_tab;
    let w = MasterSecret.derive epoch_region i in
    HST.recall (AE.ilog (StreamAE.State?.log w));
    let h1 = get () in
    ms_derive_is_ok h0 h1 i w;
    w

(* Some simply sanity checks on the association between connections, ids, nonces, writers regions *)
let all_epoch_writers_share_conn_nonce (c:connection) (i:AE.id) (wi:AE.writer i) (h:HS.mem)
    : Lemma (requires (registered i wi c h))
            (ensures (nonce_of_id i == random_of c.hs))
    = ()

let writer_registered_to_at_most_one_connection
    (n1:random) (c1:r_conn n1)
    (n2:random) (c2:r_conn n2{n1 <> n2})
    (i:AE.id {nonce_of_id i == n1}) (w:AE.writer i) (h:HS.mem)
    : Lemma (requires (registered i w c1 h))
            (ensures (~ (registered i w c2 h)))
    = ()

let writer_region_within_connection
    (n:random) (c:r_conn n)
    (i:AE.id {nonce_of_id i == n}) (w:AE.writer i) (h:HS.mem)
    : Lemma (requires (registered i w c h))
            (ensures (HH.includes (C?.region c) (StreamAE.State?.region w)))
    = reveal_epoch_region_inv_all ()

(* Case 2:
     Adding a new epoch to a connection c, with a fresh index (hdId i) for c
      -- we found a writer w at (ms i), pre-allocated (we're second) or not (we're first)
      -- we need to show that the (exists e. Seq.contains ...) is false (because of the fresh index for c)
      -- so, we're in the "not yet used" case ... so, the epoch's writer is in its initial state and we can return it (our goal is to return a fresh epoch)
*)
val register_writer_in_epoch_ok: h0:HS.mem -> h1:HS.mem -> i:AE.id{authId i}
                -> c:r_conn (nonce_of_id i) -> e:epoch (region_of c.hs) (nonce_of_id i)
  -> Lemma (requires
            (let ctab = HS.sel h0 conn_tab in
             let mstab = HS.sel h0 MS.ms_tab in
             let old_hs_log = epochs c h0 in
             let new_hs_log = epochs c h1 in
             let rgn = region_of c.hs in
             let _ = reveal_epoch_region_inv_all () in
             mc_inv h0 /\ //we're initially in the invariant
             MonSeq.i_contains (MkEpochs?.es (epochs_of c.hs)) h0 /\
             MonSeq.i_contains (MkEpochs?.es (epochs_of c.hs)) h1 /\
             i = Epochs.epoch_id e /\ //the epoch has id i
             (let w = StAE.stream_state #i (Epoch?.w e) in //the epoch writer
              let es_log_as_hsref =  (MkEpochs?.es (epochs_of c.hs)) in
              let epochs = epochs c h0 in
              N.registered (nonce_of_id i) (HS.parent (StreamAE.State?.region w)) /\  //the writer's parent region is registered in the nonce table
              HS.disjoint (HS.parent (StreamAE.State?.region w)) tls_region /\          //technical: ... needed just for well-formedness of the rest of the formula
              HST.witnessed (HST.region_contains_pred (StreamAE.State?.region w)) /\                //technical: ... needed just for well-formedness of the rest of the formula
              (forall e. epochs `Seq.contains` e ==> Epochs.epoch_id e <> i) /\            //i is fresh for c
              MDM.sel mstab i == Some w /\ //we found the writer in the ms_tab
              MDM.sel ctab (nonce_of_id i) == Some c /\ //we found the connection in the conn_table
              HS.modifies_one (region_of c.hs) h0 h1 /\ //we just modified this connection's handshake region
              HS.modifies_ref (region_of c.hs) (Set.singleton (Heap.addr_of (HS.as_ref es_log_as_hsref))) h0 h1 /\ //and within it, just the epochs log
              new_hs_log == Seq.snoc old_hs_log e))) //and we modified it by adding this epoch to it
          (ensures mc_inv h1) //we're back in the invariant
let register_writer_in_epoch_ok h0 h1 i c e =
  (* This proof can be simplified a lot.
     But, retaining it since it is actually quite informative
     about the structure of the invariant.
  *)
  let aux :  j:id -> Lemma (let new_ms = HS.sel h1 MS.ms_tab in
                           let new_conn = HS.sel h1 conn_tab in
                           ms_conn_inv new_ms new_conn h1 j) =
    fun j ->
      let old_ms = HS.sel h0 MS.ms_tab in
      let new_ms = HS.sel h1 MS.ms_tab in
      let old_conn = HS.sel h0 conn_tab in
      let new_conn = HS.sel h1 conn_tab in
      let old_hs_log = epochs c h0 in
      let wi = StAE.stream_state #i (Epoch?.w e) in //the epoch writer
      let nonce = nonce_of_id i in
      Seq.contains_intro (Seq.snoc old_hs_log e) (Seq.length old_hs_log) e;
      Seq.contains_snoc old_hs_log e; //this lemma shows that everything that was registered to c remains registered to it
      assert (old_ms == new_ms);
      assert (old_conn == new_conn);
      cut (Some? (MDM.sel old_conn nonce)); //this cut is useful for triggering the pairwise_disjointness quantifier
      if (authId j && StAE.is_stream j)
      then match MDM.sel new_ms j with
           | None -> () //nothing allocated at id j yet; easy
           | Some wj ->
             let log_ref = StreamAE.ilog (StreamAE.State?.log wj) in
             let log_ref_as_hsref =  log_ref in
             assert (Map.contains (HS.HS?.h h1) (StreamAE.State?.region wj)); //its region exists; from the 1st technical clause in ms_conn_inv
             assert (HS.contains h1 log_ref_as_hsref);    //its log exists; from the 2nd technical clause in ms_conn_inv
             assert (is_epoch_rgn (StreamAE.State?.region wj));    //from the separation clause in ms_con_inv
             let log0 = HS.sel h0 log_ref in
             let log1 = HS.sel h1 log_ref in
             assert (log0 == log1); //the properties in the three asserts above are needed to show that j's log didn't change just by registering i
             assert (~(log0 == Seq.empty //if the log remains empty, it's easy
                       \/ wj==wi) //if j is in fact the same as i, then i gets registered at the end, so that's easy too
                     ==> (let nonce_j = nonce_of_id j in
                          if nonce_j = nonce
                          then registered j wj c h0 //if j and i share the same nonce, then j is registered to c and c's registered writers only grows
                          else (match MDM.sel old_conn nonce_j with
                                | None -> False //we've already established that the log is non-empty; so j must be registered and this case says that it is not
                                | Some c' ->
                                  (registered j wj c' h0) //it's registered initially
                                  /\ (HS.disjoint (C?.region c) (C?.region c')) //c's region is disjoint from c'; since the conn_tab is pairwise_disjoint
                                  /\ (registered j wj c' h1)))) //so it remains registered
      else () (* not ideal; nothing much to say *) in
  FStar.Classical.forall_intro aux

(* Case 3:
    Adding to a log registered in a connection: Need to prove that ms_conn_invariant is maintained
    Basically, we have enough framing to know that nothing else changed if just the log changed.
    And since the log is registered, it is allowed to change, and it remains registered
*)
val mutate_registered_writer_ok : h0:HS.mem -> h1:HS.mem -> i:AE.id{authId i} -> w:MS.writer i -> c:r_conn (nonce_of_id i) -> Lemma
    (requires (mc_inv h0 /\                                       //initially in the invariant
               HS.modifies_one (StreamAE.State?.region w) h0 h1 /\ //we modified at most the writer's region
               registered i w c h0 /\                             //the writer is registered in c
               MDM.sel (HS.sel h0 MS.ms_tab) i == Some w   /\     //the writer is logged in the ms_tab
               MDM.sel (HS.sel h0 conn_tab) (nonce_of_id i) == Some c /\ //the connection is logged in the conn_table
               (let ilog_log_as_hsref =  (StreamAE.ilog (StreamAE.State?.log w)) in
                HS.contains h1 ilog_log_as_hsref))) //We say that we changed the w.region; but that doesn't necessarily mean that its log remains
    (ensures (mc_inv h1))
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 100"
let mutate_registered_writer_ok h0 h1 i w c = (* () *)
(* a slightly more detailed proof: *)
    let new_ms = HS.sel h1 MS.ms_tab in
    let new_conn = HS.sel h1 conn_tab in
    let aux :  j:id -> Lemma (ms_conn_inv new_ms new_conn h1 j) =
      fun j ->
        if (authId j && StAE.is_stream j)
        then match MDM.sel new_ms j with //the case analysis is to trigger the pattern guarding MasterSecret.region_injective
             | None -> ()
             | Some wj -> () //basically, when i=j, the proof is easy as i remains registered; if i<>j then j didn't change since their regions are distinct
        else () in
    FStar.Classical.forall_intro aux

(* Case 4:
    Adding a connection (writing to conn table) we note that none of the bad writers can be attributed to this connection
     -- So, we cannot be in the Some w, None case, as this is only for bad writers
     -- We cannot also be in the first case, since the conn table is monotonic and it doesn't already contain the id
    Note: we can prove that the having a doomed writer is a monotonic property of nonces
    TODO: We don't handle doomed writers at all yet
*)

(* An auxiliary formula, needed as a pre-condition to add a c to conn_tab *)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let conn_hs_region_exists (c:connection) (h:HS.mem) =
   let hs_rgn = region_of c.hs in
   Map.contains (HS.HS?.h h) hs_rgn /\
   HS.disjoint hs_rgn tls_tables_region

val add_connection_ok: h0:HS.mem -> h1:HS.mem -> i:id -> c:i_conn i -> Lemma
  (requires (let conn_tab_as_hsref =  conn_tab in
             mc_inv h0 /\ //we're initially in the invariant
             HS.modifies_transitively (Set.singleton tls_tables_region) h0 h1 /\  //only modified some table
             HS.modifies_ref tls_tables_region (Set.singleton (Heap.addr_of (HS.as_ref conn_tab_as_hsref))) h0 h1 /\ //in fact, only conn_tab
             conn_hs_region_exists c h0 /\ //we need to know that c is well-formed
             (let old_conn = HS.sel h0 conn_tab in
              let new_conn = HS.sel h1 conn_tab in
              let nonce = nonce_of_id i in
              MDM.sel old_conn nonce == None /\        //c wasn't in the table initially
              new_conn == MDM.upd old_conn nonce c))) //and the conn_tab changed just by adding c
  (ensures (mc_inv h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 100" //NS: this one seems to require an inversion somewhere, but not sure exactly where
let add_connection_ok h0 h1 i c =
    cut (let conn_tab_as_hsref =  conn_tab in
         HS.contains h1 conn_tab_as_hsref);
    let old_conn = HS.sel h0 conn_tab in
    let new_conn = HS.sel h1 conn_tab in
    let hs_region_exists : n:random -> Lemma
        (match MDM.sel new_conn n with
         | None -> True
         | Some v -> conn_hs_region_exists v h1) =
      fun n -> match MDM.sel new_conn n with
            | None -> ()
            | Some c' ->
              assert (c =!= c' ==> (match MDM.sel old_conn n with
                                     | None -> True
                                     | Some c'' -> c' == c'')) in
    FStar.Classical.forall_intro hs_region_exists;
    cut (handshake_regions_exists new_conn (HS.HS?.h h1))

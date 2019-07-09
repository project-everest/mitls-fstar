module ConnectionTable

open FStar.Tactics
open FStar.Monotonic.DependentTable
open FStar.ReflexiveTransitiveClosure

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentTable

let connection_id = nat

let random = int

type connection =  
  | Sent_HRR: random -> connection
  | Sent_ServerHello: random -> connection
  | Complete: random -> connection

let nonce_of = function
  | Sent_HRR r | Sent_ServerHello r | Complete r -> r

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Sent_ServerHello r, Complete r' -> r == r'
  | _, _ -> False

unfold
let rel (id:connection_id) : Preorder.preorder connection = closure step

type connection_table (r:erid) = T.t r connection_id (fun id -> connection) (fun _ -> True) rel

val test: rgn:erid -> ST (connection_table rgn)
  (requires fun _ -> witnessed (region_contains_pred rgn))
  (ensures  fun h0 t h1 -> token_p t (fun h -> defined t 1 h /\ nonce_of (value_of t 1 h) == 1))
let test rgn =
  let t : connection_table rgn = T.alloc () in
  T.update t 1 (Sent_HRR 1);
  let h1 = get() in
  assert (T.contains t 1 (Sent_HRR 1) h1);
  T.update t 2 (Sent_ServerHello 2);
  stable_on_closure step (fun c -> nonce_of c = 1) ();
  // Not really needed as long as `grows` is transparent
  contains_stable t 1 (Sent_HRR 1) (fun c -> nonce_of c == 1) ();
  witness_p t (fun h -> defined t 1 h /\ nonce_of (value_of t 1 h) == 1);
  t

module DM = FStar.DependentMap

let p (m:partial_dependent_map connection_id (fun _ -> connection)) (id:connection_id) : Type0 =
  Some? (DM.sel m id) /\ (exists r. Some?.v (DM.sel m id) == Sent_HRR r)

val _p_stable:
  m1:map connection_id (fun _ -> connection) ->
  m2:map connection_id (fun _ -> connection) ->
  id:connection_id ->
  Lemma 
  (requires p (repr m1) id /\ grows #_ #_ #(fun _ -> True) rel m1 m2)
  (ensures  p (repr m2) id)
let _p_stable m1 m2 id =
  closure_inversion step (Some?.v (T.sel m1 id)) (Some?.v (T.sel m2 id))

val p_stable: squash (forall m1 m2 x. 
  p (repr m1) x /\ grows #connection_id #(fun _ -> connection) #(fun _ -> True) rel m1 m2 /\ True ==> p (repr m2) x)
let p_stable =
  assert (forall m1 m2 x. 
    p (repr m1) x /\ 
    grows #connection_id #(fun _ -> connection) #(fun _ -> True) rel m1 m2 /\ True ==> p (repr m2) x)
  by
    (let m1 = forall_intro () in
     let _ = forall_intro () in
     let _ = forall_intro () in
     let _ = implies_intro () in
     let m1 = unquote (binder_to_term m1) in
     mapply (quote (_p_stable m1)))

val test2: unit -> ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
let test2 _ =
  let r = new_region root in
  let t : connection_table r = T.alloc () in
  T.update t 1 (Sent_HRR 0);
  T.update t 2 (Sent_ServerHello 1);
  let h = get() in
  closure_step step (Sent_ServerHello 1) (Complete 1);
  T.update t 2 (Complete 1);
  // Not actually required as long as `grows` is transparent
  T.map_stable t p p_stable 2;
  witness_p t (fun h -> defined t 1 h /\ p (repr (sel h t)) 1)


/// We want to witness properties like the following
let q (m:partial_dependent_map connection_id (fun _ -> connection)) : Type0 =
  forall (id:connection_id{Some? (DM.sel m id)}).
   Sent_ServerHello? (Some?.v (DM.sel m id)) ==>
   (exists id'.
     Some? (DM.sel m id') /\ 
     Sent_HRR? (Some?.v (DM.sel m id')) /\
     nonce_of (Some?.v (DM.sel m id')) = nonce_of (Some?.v (DM.sel m id)))

let q' 
  (m:partial_dependent_map connection_id (fun _ -> connection)) 
  (id:connection_id{Some? (DM.sel m id)})
  (id':connection_id) 
=
  Sent_ServerHello? (Some?.v (DM.sel m id)) ==>
  (Some? (DM.sel m id') /\ 
   Sent_HRR? (Some?.v (DM.sel m id')) /\
   nonce_of (Some?.v (DM.sel m id')) = nonce_of (Some?.v (DM.sel m id)))

val q'_stable:
  m1:map connection_id (fun _ -> connection) ->
  m2:map connection_id (fun _ -> connection) ->
  id:connection_id{Some? (T.sel m1 id) /\ Sent_ServerHello? (Some?.v (T.sel m1 id))} ->
  id':connection_id ->
  Lemma 
  (requires q' (repr m1) id id' /\ grows #_ #_ #(fun _ -> True) rel m1 m2)
  (ensures  Some? (T.sel m2 id) /\ q' (repr m2) id id')
let q'_stable m1 m2 id id' =
  closure_inversion step (Some?.v (T.sel m1 id)) (Some?.v (T.sel m2 id));  
  if Sent_ServerHello? (Some?.v (T.sel m1 id)) then
    begin
    assert (Some? (T.sel m1 id'));
    assert (Some? (T.sel m2 id'));
    closure_inversion step (Some?.v (T.sel m1 id')) (Some?.v (T.sel m2 id'));
    assert (Sent_HRR? (Some?.v (T.sel m2 id')));
    assert (nonce_of (Some?.v (T.sel m1 id')) = nonce_of (Some?.v (T.sel m2 id')));    
    stable_on_closure step (fun c -> nonce_of c == nonce_of (Some?.v (T.sel m1 id))) ();
    assert (nonce_of (Some?.v (T.sel m1 id)) = nonce_of (Some?.v (T.sel m2 id)));
    assert (Some? (T.sel m2 id))
    end

val q_stable:
  m1:map connection_id (fun _ -> connection) ->
  m2:map connection_id (fun _ -> connection) ->
  Lemma 
  (requires q (repr m1) /\ grows #_ #_ #(fun _ -> True) rel m1 m2)
  (ensures  q (repr m2))
  [SMTPat (q (repr m1)); SMTPat (q (repr m2))]
let q_stable m1 m2 = 
  admit()

val test3: unit -> ST unit
  (requires fun _ -> True)
  (ensures  fun _ _ _ -> True)
let test3 _ =
  let r = new_region root in
  let t : connection_table r = T.alloc () in
  T.update t 1 (Sent_HRR 1);
  T.update t 2 (Sent_ServerHello 1);
  assert (stable_on (fun h -> q (repr (sel h t))) t);
  witness_p t (fun h -> q (repr (sel h t)))

module ConnectionTable2

open FStar.Tactics
open FStar.Monotonic.DependentTable
open FStar.ReflexiveTransitiveClosure

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentTable
module DM = FStar.DependentMap

let connection_id = nat

assume val client_hello: Type0

assume val has_cookie: client_hello -> bool

assume val cookie : Type0

assume val ch_cookie: ch:client_hello{has_cookie ch} -> cookie

assume val matches: cookie -> client_hello -> Type0

noeq
type connection =  
  | Sent_HRR: random:nat -> ch:client_hello -> connection
  | Sent_ServerHello: random:nat -> ch:client_hello -> connection
  | Complete: random:nat -> ch:client_hello -> connection

let nonce_of = function
  | Sent_HRR r _ | Sent_ServerHello r _ | Complete r _ -> r

let is_retry = function
  | Sent_HRR _ _ -> false
  | Sent_ServerHello _ ch | Complete _ ch -> has_cookie ch

let cookie_of (c:connection{is_retry c}) =
  match c with
  | Sent_ServerHello _ ch | Complete _ ch -> ch_cookie ch

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Sent_ServerHello r ch, Complete r' ch' -> r == r' /\ ch == ch'
  | _, _ -> False

unfold
let rel : Preorder.preorder connection = closure step

let recallable (#a:Type0) (#rel:Preorder.preorder a) (r:mreference a rel) =
  is_eternal_region (frameOf r) /\ not (is_mm r)

val inv: DM.t connection_id 
  (opt (fun _ -> c:mreference connection rel{recallable c})) -> Type0
let inv m = 
  forall (id:connection_id{Some? (DM.sel m id)}) (r:nat) (ck:cookie).
   let c = Some?.v (DM.sel m id) in
   (token_p c (fun h -> is_retry (sel h c)) /\
    token_p c (fun h -> 
     is_retry (sel h c) /\ cookie_of (sel h c) == ck /\ nonce_of (sel h c) == r))
   ==>
   (exists (id':connection_id{Some? (DM.sel m id')}).
     let c' = Some?.v (DM.sel m id') in
     token_p c' (fun h -> 
       Sent_HRR? (sel h c') /\ 
       nonce_of (sel h c') == r /\
       ck `matches` Sent_HRR?.ch (sel h c')))

type connection_table (r:erid) = 
  T.t r connection_id (fun _ -> c:mreference connection rel{recallable c}) 
    inv (fun _ _ _ -> True)

// This is not useful in hypothetical situations where 
// we only know one of token_p r p, token_p r (fun h -> ~(p h)))
val token_contradiction: 
    #a:Type 
  -> #rel:Preorder.preorder a 
  -> r:mreference a rel 
  -> p:mem_predicate 
  -> ST unit
  (requires fun h -> 
    h `HyperStack.contains` r /\ token_p r p /\ token_p r (fun h -> ~(p h)))
  (ensures  fun _ _ _ -> False)
let token_contradiction #a #rel r p =
  recall_p r p;
  recall_p r (fun h -> ~(p h))

// This is useful, but isn't provable without axioms 
assume 
val aseem: 
    #a:Type
  -> #rel:Preorder.preorder a
  -> r:mreference a rel{recallable r}
  -> p:mem_predicate
  -> ST unit
    (requires fun h -> token_p r (fun h -> ~(p h)))
    (ensures  fun h0 _ h1 -> h0 == h1 /\ ~(token_p r p))

val test: rgn:erid -> ch:client_hello -> ST (connection_table rgn)
  (requires fun _ -> witnessed (region_contains_pred rgn))
  (ensures  fun h0 _ h1 -> True)
let test rgn ch =
  let t : connection_table rgn = T.alloc () in
  let c1 : c:mreference connection rel{recallable c} = ralloc rgn (Sent_HRR 1 ch) in
  stable_on_closure step (fun c -> ~(is_retry c)) ();
  let h = get () in
  witness_p c1 (fun h -> ~(is_retry (sel h c1)));
  aseem c1 (fun h -> is_retry (sel h c1));
  assert (
    let m = DM.upd (repr (sel h t)) 1 (Some c1) in
    (forall (id:connection_id{Some? (DM.sel m id)}) (r:nat) (ck:cookie).
     let c = Some?.v (DM.sel m id) in
     c == c1 /\
     ~(token_p c (fun h -> is_retry (sel h c1)))));
  // Can't convince the typechecker that replacing c1 by c is the same
  assume (
    let m = DM.upd (repr (sel h t)) 1 (Some c1) in
    (forall (id:connection_id{Some? (DM.sel m id)}) (r:nat) (ck:cookie).
     let c = Some?.v (DM.sel m id) in
     ~(token_p c (fun h -> is_retry (sel h c)))));
  assert (
    let m = DM.upd (repr (sel h t)) 1 (Some c1) in
    (forall (id:connection_id{Some? (DM.sel m id)}) (r:nat) (ck:cookie).
     let c = Some?.v (DM.sel m id) in
     (token_p c (fun h -> is_retry (sel h c)) /\
      token_p c (fun h -> 
       is_retry (sel h c) /\ cookie_of (sel h c) == ck /\ nonce_of (sel h c) == r)) 
     ==>
     (exists (id':connection_id{Some? (DM.sel m id')}).
     let c' = Some?.v (DM.sel m id') in
     token_p c' (fun h -> 
       Sent_HRR? (sel h c') /\ 
       nonce_of (sel h c') == r /\
       ck `matches` Sent_HRR?.ch (sel h c')))));
  // This is just unfolding inv, but can't convince the typechecker
  assume (
    let m = DM.upd (repr (sel h t)) 1 (Some c1) in
    inv m <==>
    (forall (id:connection_id{Some? (DM.sel m id)}) (r:nat) (ck:cookie).
     let c = Some?.v (DM.sel m id) in
     (token_p c (fun h -> is_retry (sel h c)) /\
      token_p c (fun h -> 
       is_retry (sel h c) /\ cookie_of (sel h c) == ck /\ nonce_of (sel h c) == r)) 
     ==>
     (exists (id':connection_id{Some? (DM.sel m id')}).
     let c' = Some?.v (DM.sel m id') in
     token_p c' (fun h -> 
       Sent_HRR? (sel h c') /\ 
       nonce_of (sel h c') == r /\
       ck `matches` Sent_HRR?.ch (sel h c')))));
  T.update t 1 c1;
  t

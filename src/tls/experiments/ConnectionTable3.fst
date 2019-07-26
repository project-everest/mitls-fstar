module ConnectionTable3

open FStar.Tactics
open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentTable

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentTable
module DM = FStar.DependentMap

type connection_id = nat

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

type connection_table (rgn:erid) = 
  T.t rgn connection_id (fun _ -> mmmref connection rel) (fun _ -> True) (fun _ r1 r2 -> r1 == r2) 

val inv: rgn:erid -> t:connection_table rgn -> h:mem -> Type0
let inv rgn t h = 
  let m = T.repr (sel h t) in
  forall (id:connection_id).
   Some? (DM.sel m id) ==>
   (let c = Some?.v (DM.sel m id) in
    is_retry (sel h c) ==>
    (exists (id':connection_id).
     Some? (DM.sel m id') /\
     (let c' = Some?.v (DM.sel m id') in
      token_p c' (fun h0 -> 
        Sent_HRR? (sel h0 c') /\ 
        nonce_of (sel h0 c') == nonce_of (sel h c) /\
        cookie_of (sel h c) `matches` Sent_HRR?.ch (sel h0 c')))))

val test: rgn:erid -> ch1:client_hello -> ch2:client_hello{has_cookie ch2} 
  -> ST (connection_table rgn)
  (requires fun _ -> witnessed (region_contains_pred rgn) /\
                  ch_cookie ch2 `matches` ch1)
  (ensures  fun h0 t h1 -> h1 `contains` t /\ frameOf t == rgn /\ inv rgn t h1)
let test rgn ch1 ch2 =
  let t : connection_table rgn = T.alloc () in
  let c1 : mmmref connection rel = ralloc_mm rgn (Sent_HRR 1 ch1) in
  T.update t 1 c1;
  let h1 = get() in
  assert (inv rgn t h1);
  let c2 : mmmref connection rel = ralloc_mm rgn (Sent_ServerHello 1 ch2) in
  T.update t 2 c2;  
  let h2 = get() in
  let rhs (c:connection) = 
    Sent_HRR? c /\ 
    nonce_of c == 1 /\
    ch_cookie ch2 `matches` Sent_HRR?.ch c
  in
  stable_on_closure step rhs ();
  witness_p c1 (fun h -> rhs (sel h c1));
  assert (token_p c1 (fun h -> rhs (sel h c1)));
  assume (
   let m = T.repr (sel h2 t) in
   forall (id:connection_id).
     Some? (DM.sel m id) ==>
     (let c = Some?.v (DM.sel m id) in
      is_retry (sel h2 c) ==>
      (exists (id':connection_id).
        Some? (DM.sel m id) /\
        (let c' = Some?.v (DM.sel m id) in
        token_p c' (fun h0 -> rhs (sel h0 c'))))));
//  admit();
  assert (
  let m = T.repr (sel h2 t) in
  forall (id:connection_id).
   Some? (DM.sel m id) ==>
   (let c = Some?.v (DM.sel m id) in
    is_retry (sel h2 c) ==>
     Some? (DM.sel m 1) /\
     (let c' = Some?.v (DM.sel m 1) in
      token_p c' (fun h -> rhs (sel h c1)))));
  assume (
    inv rgn t h2 <==>
    (let m = T.repr (sel h2 t) in
  forall (id:connection_id).
   Some? (DM.sel m id) ==>
   (let c = Some?.v (DM.sel m id) in
    is_retry (sel h2 c) ==>
    (exists (id':connection_id).
     Some? (DM.sel m id') /\
     (let c' = Some?.v (DM.sel m id') in
      token_p c' (fun h0 -> rhs (sel h0 c')))))));
  admit();
  t

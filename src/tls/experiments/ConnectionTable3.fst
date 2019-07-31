module ConnectionTable3

open FStar.Tactics
open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

type connection_id = nat

assume val client_hello: Type0

assume val cookie : Type0

assume val has_cookie: client_hello -> bool

assume val ch_cookie: ch:client_hello{has_cookie ch} -> cookie

assume val matches: cookie -> client_hello -> Type0

noeq
type connection =
  | Init: connection
  | Sent_HRR: random:nat -> ch:client_hello -> connection
  | Sent_ServerHello: random:nat -> ch:client_hello -> id1:connection_id -> connection
  | Complete: random:nat -> ch:client_hello -> id1:connection_id -> connection

let nonce_of (c:connection{~(Init? c)}) =
  match c with
  | Sent_HRR r _ | Sent_ServerHello r _ _ | Complete r _ _ -> r

let ch_of (c:connection{~(Init? c)}) =
  match c with
  | Sent_HRR _ ch | Sent_ServerHello _ ch _ | Complete _ ch _ -> ch

let cookie_of (c:connection{~(Init? c) /\ has_cookie (ch_of c)}) =
  ch_cookie (ch_of c)

let id0_of (c:connection{Sent_ServerHello? c \/ Complete? c}) =
  match c with
  | Sent_ServerHello _ _ id0 | Complete _ _ id0 -> id0

let step (s1 s2:connection) : Type0 =
  match s1, s2 with
  | Init, Sent_HRR _ _ -> True
  | Init, Sent_ServerHello _ _ _ -> True
  | Sent_ServerHello r ch id0, Complete r' ch' id0' -> r == r' /\ ch == ch' /\ id0 == id0'
  | _, _ -> False

let rel : Preorder.preorder connection = closure step

assume val rgn:erid

let connection_ref (id:connection_id) = r:mmmref connection rel{frameOf r `extends` rgn}

let minv (m:partial_dependent_map connection_id connection_ref) =
  forall id1 id2.{:pattern (Some? (DM.sel m id1)); (Some? (DM.sel m id2))}
    (id1 <> id2 /\ Some? (DM.sel m id1) /\ Some? (DM.sel m id2)) ==>
    frameOf (Some?.v (DM.sel m id1)) `disjoint` frameOf (Some?.v (DM.sel m id2))

type connection_table = T.t rgn connection_id connection_ref minv

val connection_inv: 
    m:T.imap connection_id connection_ref minv
  -> c:connection
  -> Type0
let connection_inv m c =
  match c with
  | Sent_ServerHello r ch id0 | Complete r ch id0 ->
    if has_cookie ch then
      match T.sel m id0 with
      | Some c' ->
        token_p c' (fun h0 -> 
          Sent_HRR? (sel h0 c') /\ 
          nonce_of (sel h0 c') == r /\
          ch_cookie ch `matches` Sent_HRR?.ch (sel h0 c'))
      | _ -> False
    else True
  | _ -> True

(*
  Stateful invariant
  It can't be attached to the table because it needs to dereferences connections
*)
val inv: t:connection_table -> h:mem -> Type0
let inv t h = 
  let m = sel h t in
  forall (id:connection_id).{:pattern (T.defined t id h)}
    (T.defined t id h /\ h `contains` (T.value_of t id h))    
    ==> connection_inv m (sel h (Some?.v (T.sel m id)))

val alloc: unit -> ST (connection_table)
  (requires fun _ -> witnessed (region_contains_pred rgn))
  (ensures  fun h0 t h1 -> ralloc_post rgn T.empty h0 t h1)
let alloc _ =
  T.alloc ()

val create: t:connection_table -> id:connection_id -> ST (connection_ref id)
  (requires fun h0 -> h0 `contains` t /\ inv t h0 /\ ~(T.defined t id h0))
  (ensures  fun h0 c h1 -> 
    mods [Ref t] h0 h1 /\ 
    h1 `contains` t /\ 
    inv t h1 /\
    T.defined t id h1 /\
    sel h1 t == T.upd (sel h0 t) id c /\
    ~(h0 `contains` c) /\
    h1 `contains` c /\
    sel h1 c == Init)
let create t id =
  let h0 = get () in
  let p (id:connection_id{T.defined t id h0}) = frameOf (T.value_of t id h0) in
  testify_forall_region_contains_pred #_ #p ();
  let rgn1 = new_region rgn in
  let c : mmmref connection rel = ralloc_mm rgn1 Init in
  let h1 = get () in
  assert (forall (id:connection_id). T.defined t id h0 ==> ~(c == T.value_of t id h0));
  assert (inv t h1);
  T.extend t id c;
  assert (
    let m0 = sel h0 t in
    forall (id':connection_id).{:pattern (T.value_of t id' h0)}
      (T.defined t id' h0 /\ h0 `contains` (T.value_of t id' h0) /\ ~(c == T.value_of t id' h0)) ==>
      connection_inv m0 (sel h1 (T.value_of t id' h0)));
  c

val free: t:connection_table -> id:connection_id -> ST unit
  (requires fun h0 -> 
    h0 `contains` t /\ inv t h0 /\ T.defined t id h0 /\
    T.value_of t id h0 `is_live_for_rw_in` h0 /\ inv t h0)
  (ensures  fun h0 _ h1 -> 
    h0 `contains` (T.value_of t id h0) /\
    h1 == HyperStack.free (T.value_of t id h0) h0 /\
    inv t h1)
let free t id =
  let c = Some?.v (T.lookup t id) in
  let h0 = get() in
  rfree c;
  let h1 = get() in
  assert (
    let m = sel h1 t in
    forall (id:connection_id).{:pattern (T.defined t id h1)}
    (T.defined t id h0 /\ h1 `contains` (T.value_of t id h1)) ==> 
    connection_inv m (sel h1 (T.value_of t id h1)))

(* Added a pattern; all alternatives I tried didn't work or were too cumbersome *)
val token_functoriality
  (#a:Type0) (#rel:Preorder.preorder a) (r:mreference a rel)
  (p:mem_predicate{token_p r p}) (q:mem_predicate{forall (h:mem). p h ==> q h})
  : Lemma (token_p r q)
   [SMTPat (token_p r p); SMTPat (token_p r q)]
let token_functoriality #a #rel r p q = 
  token_functoriality r p q

#set-options "--z3rlimit 100"

(*
   This tests the server side of a full handshake with mismatched parameters:

   1. Allocate an empty connection table 
   2. Create a first connection c1 with id = 1 (in Init state)
   3. Receive a ClientHello ch1 with random 0 on c1. Transition c1 to Sent_HRR 0 ch1
   4. Deallocate c1
   5. Create a second connection c2 (in Init state)
   6. Receive a ClientHello ch2 on c2 with a random and cookie extension matching ch1.
      Transition c2 to Sent_ServerHello 0 ch2 1, with c1 as the matching initial connection 
   7. Receive a ClientFinished on c2. Transition c2 to Complete 0 ch2 1
   8. Deallocate c2
*)
val test: ch1:client_hello -> ch2:client_hello{has_cookie ch2} -> ST connection_table
  (requires fun _ -> witnessed (region_contains_pred rgn) /\
                  ch_cookie ch2 `matches` ch1)
  (ensures  fun h0 t h1 -> h1 `contains` t /\ inv t h1)
let test ch1 ch2 =
  let t = alloc () in
  let c1 = create t 1 in
  c1 := Sent_HRR 0 ch1;
  stable_on_closure (closure step) 
    (fun c ->
      Sent_HRR? c /\ 
      nonce_of c == 0 /\
      ch_cookie ch2 `matches` Sent_HRR?.ch c) ();
  witness_p c1 
    (fun h -> 
      Sent_HRR? (sel h c1) /\ 
      nonce_of (sel h c1) == 0 /\
      ch_cookie ch2 `matches` Sent_HRR?.ch (sel h c1));
  free t 1;
  let c2 = create t 2 in
  c2 := Sent_ServerHello 0 ch2 1;
  c2 := Complete 0 ch2 1;  
  free t 2;
  t

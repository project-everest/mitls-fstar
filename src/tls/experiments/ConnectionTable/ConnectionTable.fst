module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

open ConnectionTable_Aux

let minv (m:partial_dependent_map connection_id connection_ref) =
  forall id1 id2.{:pattern (Some? (DM.sel m id1)); (Some? (DM.sel m id2))}
    (id1 <> id2 /\ Some? (DM.sel m id1) /\ Some? (DM.sel m id2)) ==>
    frameOf (Some?.v (DM.sel m id1)) `disjoint` frameOf (Some?.v (DM.sel m id2))

let empty = T.empty

val connection_inv:
    m:T.imap connection_id connection_ref minv
  -> c:connection
  -> Type0
let connection_inv m c =
  match c with
  | Sent_ServerHello r ch id1 | Complete r ch id1 ->
    if has_cookie ch then
      match T.sel m id1 with
      | Some c' ->
        token_p c' (fun h0 ->
          Sent_HRR? (sel h0 c') /\
          nonce_of (sel h0 c') == r /\
          ch_of_cookie ch == Sent_HRR?.ch (sel h0 c'))
      | _ -> False
    else True
  | _ -> True

(*
  Stateful invariant
  Can't be attached to the table because it needs to dereference connections
*)
let inv t h =
  let m = sel h t in
  forall (id:connection_id).{:pattern (T.defined t id h)}
    (T.defined t id h /\ h `contains` (T.value_of t id h))
    ==> connection_inv m (sel h (Some?.v (T.sel m id)))

let alloc _ = T.alloc ()

let create t id cfg =
  recall t;
  let h0 = get () in
  let p (id:connection_id{T.defined t id h0}) = frameOf (T.value_of t id h0) in
  testify_forall_region_contains_pred #_ #p ();
  let rgn1 = new_region rgn in
  let c : mmmref connection rel = ralloc_mm rgn1 (Init cfg) in
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

let free_connection t id =
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

let receive_client_hello1 t id ch =
  let h0 = get () in
  let c = Some?.v (T.lookup t id) in
  if ch_compatible ch (Init?.cfg !c) then
    c := Sent_ServerHello (ch_random ch) ch 0ul
  else
    c := Sent_HRR (ch_random ch) ch;
  let h1 = get () in
  assert (
    let m = sel h1 t in
    forall (id:connection_id).{:pattern (T.defined t id h1)}
    (T.defined t id h0 /\ h1 `contains` (T.value_of t id h1)) ==>
    connection_inv m (sel h1 (T.value_of t id h1)))

(*
   Validates a cookie and returns the id of the connection where it originates, if valid.
   Ideally, we can enforce that authentic cookies come from an earlier honest connection.
*)
[@"opaque_to_smt"]
val id_of_cookie:
  t:connection_table ->
  ch:client_hello{has_cookie ch} ->
  ST (option connection_id)
  (requires fun h0 -> inv t h0)
  (ensures  fun h0 o h1 ->
    match o with
    | None -> h0 == h1
    | Some id1 ->
      h0 == h1 /\
      T.defined t id1 h0 /\
      (let c' = T.value_of t id1 h0 in
       token_p c' (fun h0 ->
         Sent_HRR? (sel h0 c') /\
         nonce_of (sel h0 c') == ch_random ch /\
         ch_of_cookie ch == Sent_HRR?.ch (sel h0 c'))))
let id_of_cookie t ch =
  assume (False); // For the sake of testing extraction
  Some 0ul

let receive_client_hello2 t id ch =
  let h0 = get () in
  let c = Some?.v (T.lookup t id) in
  match id_of_cookie t ch with
  | None -> false
  | Some id1 ->
    if ch_compatible ch (Init?.cfg !c) then
      begin
      c := Sent_ServerHello (ch_random ch) ch id1;
      let h1 = get () in
      assert (
        let m = sel h1 t in
        forall (id:connection_id).{:pattern (T.defined t id h1)}
        (T.defined t id h0 /\ h1 `contains` (T.value_of t id h1)) ==>
        connection_inv m (sel h1 (T.value_of t id h1)));
      true
      end
    else false

let receive_client_finished t id =
  let c = Some?.v (T.lookup t id) in
  let c0 = !c in
  let h0 = get() in
  c := Complete (Sent_ServerHello?.random c0)
               (Sent_ServerHello?.ch c0)
               (Sent_ServerHello?.id1 c0);
  let h1 = get () in
  assert (
    let m = sel h1 t in
    forall (id:connection_id).{:pattern (T.defined t id h1)}
      (T.defined t id h0 /\ h1 `contains` (T.value_of t id h1)) ==>
      connection_inv m (sel h1 (T.value_of t id h1)))

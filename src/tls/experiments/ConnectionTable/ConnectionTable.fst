module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

open ConnectionTable_Aux

// For the sake of testing extraction
[@"opaque_to_smt"]
let model = false

let minv (m:partial_dependent_map maybe_id connection_ref) =
  forall id1 id2.{:pattern (Some? (DM.sel m id1)); (Some? (DM.sel m id2))}
    (id1 <> id2 /\ Some? (DM.sel m id1) /\ Some? (DM.sel m id2)) ==>
    frameOf (Some?.v (DM.sel m id1)) `disjoint` frameOf (Some?.v (DM.sel m id2))

let empty = T.empty

val connection_inv:
    m:T.imap maybe_id connection_ref minv
  -> c:connection
  -> Type0
let connection_inv m c =
  if model then
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
  else True

(*
  Stateful invariant
  Can't be attached to the table because it needs to dereference connections
*)
let inv t h =
  let m = sel h t in
  forall (id:maybe_id).{:pattern (T.defined t id h)}
    (T.defined t id h /\ h `contains` (T.value_of t id h))
    ==> connection_inv m (sel h (Some?.v (T.sel m id)))

let alloc _ =
  if model then
    T.alloc () <: _connection_table
  else ()

let create t id cfg =
  if model then
    begin
    let t:_connection_table = t in
    recall t;
    let h0 = get () in
    let p (id:connection_id{T.defined t id h0}) = frameOf (T.value_of t id h0) in
    testify_forall_region_contains_pred #_ #p ()
    end;

  let h0 = get () in
  let rgn1 = new_region rgn in
  let c : mmmref connection rel = ralloc_mm rgn1 (Init cfg) in
  let h1 = get () in

  if model then
    begin
    let t:_connection_table = t in
    assert (forall (id:connection_id).
      T.defined t id h0 ==> ~(c == T.value_of t id h0));
    T.extend t id c;
    let h2 = get() in
    assert (
      forall (id':connection_id).{:pattern (T.value_of t id' h2)}
        T.defined t id' h2 ==> (T.defined t id' h0 \/ T.value_of t id' h2 == c))
    end;
    
  c

let free_connection t id c =
  let h0 = get () in
  rfree c;
  if model then
    let h1 = get () in
    let t:_connection_table = t in
    assert (
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0)

(* Added a pattern; all alternatives I tried didn't work or were too cumbersome *)
val token_functoriality
  (#a:Type0) (#rel:Preorder.preorder a) (r:mreference a rel)
  (p:mem_predicate{token_p r p}) (q:mem_predicate{forall (h:mem). p h ==> q h})
  : Lemma (token_p r q)
   [SMTPat (token_p r p); SMTPat (token_p r q)]
let token_functoriality #a #rel r p q =
  token_functoriality r p q

let receive_client_hello1 t id c ch =
  let h0 = get () in
  if ch_compatible ch (Init?.cfg !c) then
    c := Sent_ServerHello (ch_random ch) ch (if model then 0ul else ())
  else
    c := Sent_HRR (ch_random ch) ch;
  if model then
    let h1 = get () in
    let t:_connection_table = t in
    assert (
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0)

//[@"opaque_to_smt"]
let validate_cookie t ch2 =
  if model then
    begin
    let h0 = get () in
    // For the sake of testing extraction, return always id1 = 0ul
    assume (
      let t:_connection_table = t in
      let id1 = 0ul in
      T.defined t id1 h0 /\
      (let c' = T.value_of t id1 h0 in
        token_p c' (fun h0 ->
          Sent_HRR? (sel h0 c') /\
          nonce_of (sel h0 c') == ch_random ch2 /\
          ch_of_cookie ch2 == Sent_HRR?.ch (sel h0 c'))));
    Some 0ul
    end
  else Some ()

let receive_client_hello2 t id c ch2 =
  let h0 = get () in
  match validate_cookie t ch2 with
  | None -> false
  | Some id1 -> 
    if ch_compatible ch2 (Init?.cfg !c) then
      begin
      c := Sent_ServerHello (ch_random ch2) ch2 id1;
      let h1 = get () in
      assert (
        if model then
          let t:_connection_table = t in
          forall (id:connection_id).{:pattern (T.defined t id h1)}
            T.defined t id h1 ==> T.defined t id h0
        else True);
      true
      end
    else false


let receive_client_finished t id c =
  let c0 = !c in
  let h0 = get() in
  c := Complete (Sent_ServerHello?.random c0)
               (Sent_ServerHello?.ch c0)
               (Sent_ServerHello?.id1 c0);
  let h1 = get () in
  assert (
    if model then
      let t:_connection_table = t in
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0
    else True)

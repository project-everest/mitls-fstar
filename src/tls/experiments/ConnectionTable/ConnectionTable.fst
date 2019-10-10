module ConnectionTable

open FStar.ReflexiveTransitiveClosure
open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap
module B = LowStar.Buffer
module AEAD = Crypto.AEAD
module AE = Crypto.AE
module EE = EverCrypt.Error

open ConnectionTable_Aux

// References to connections live in pairwise disjoint regions
let minv (m:partial_dependent_map maybe_id connection_ref) =
  forall id1 id2.{:pattern (Some? (DM.sel m id1)); (Some? (DM.sel m id2))}
    (id1 <> id2 /\ Some? (DM.sel m id1) /\ Some? (DM.sel m id2)) ==>
    frameOf (Some?.v (DM.sel m id1)) `disjoint` frameOf (Some?.v (DM.sel m id2))

let empty = T.empty

val connection_inv:
    T.imap maybe_id connection_ref minv
  -> connection
  -> Type0
let connection_inv m c =
  if model then
    match c with
    | Sent_ServerHello ch id1 | Complete ch id1 ->
      if has_cookie ch then
        match T.sel m id1 with
        | Some c' ->
          token_p c' (fun h0 ->
            Sent_HRR? (sel h0 c') /\
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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"

let table : connection_table = 
  recall_region rgn;
  witness_region rgn;
  alloc ()

val key : b:B.lbuffer UInt8.t 16{B.recallable b}
let key = 
  B.gcmalloc_of_list
    cookie_rgn
    [ 0x00uy; 0x01uy; 0x02uy; 0x03uy;
      0x04uy; 0x05uy; 0x06uy; 0x07uy;
      0x08uy; 0x09uy; 0x0Auy; 0x0Buy;
      0x0Cuy; 0x0Duy; 0x0Euy; 0x0Fuy ]

let phi s = 
  Seq.length s >= 32 /\
  (if model then
    let random = Seq.slice s 0 32 in
    let id = id_of_random random in
    let t:_connection_table = table in
    token_p t (fun h -> 
      T.defined t id h /\
      (let c = T.value_of t id h in
      token_p c (fun h' -> 
        Sent_HRR? (sel h' c) /\
        CH1 random == Sent_HRR?.ch (sel h' c))))
   else True)

let cookie_key : option (k:AE.state alg phi{model ==> AE.safe k}) =
  B.recall key;
  if model then
    Some (AE.create cookie_rgn alg key phi)
  else
    AE.coerce cookie_rgn alg key phi

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 10"

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
    let id0 : maybe_id = if model then 0uy else () in
    c := Sent_ServerHello ch id0
  else
    c := Sent_HRR ch;
  if model then
    let h1 = get () in
    let t:_connection_table = t in
    assert (
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0)

assume val random_of_buffer: b:B.buffer UInt8.t -> ST random
  (requires  fun h -> B.live h b /\ B.length b >= 32)
  (ensures   fun h0 r h1 -> h0 == h1 /\ r == Seq.slice (B.as_seq h0 b) 0 32)

val validate_cookie':
    ck:cookie
  -> Stack (option (maybe_id & random))
  (requires fun h0 ->
    Some? cookie_key /\
    AE.invariant h0 (Some?.v cookie_key) /\ 
    B.live h0 ck /\
    (model ==> inv table h0))
  (ensures  fun h0 o h1 ->
    B.modifies (AE.footprint (Some?.v cookie_key)) h0 h1 /\
    AE.invariant h1 (Some?.v cookie_key) /\ 
    (match o with
    | None -> True
    | Some (id, random) ->
      if model then
        let t:_connection_table = table in
        id == id_of_random random /\
        T.defined t id h0 /\
        (let c = T.value_of t id h0 in
           token_p c (fun h ->
             Sent_HRR? (sel h c) /\
             CH1 random == Sent_HRR?.ch (sel h c)))
      else True))

let validate_cookie' ck =
  let h0 = get () in
  match cookie_key with
  | None -> None
  | Some cookie_key ->
    begin
    push_frame();
    let plain = B.alloca 0uy 64ul in
    let h1 = get () in
    AE.frame_invariant h0 cookie_key B.loc_none h1;
    assume (B.loc_includes (B.loc_region_only true cookie_rgn) (AE.footprint cookie_key));
    assume (B.loc_disjoint (AE.footprint cookie_key) (B.loc_buffer ck));
    let res : option (maybe_id & random) =
      match AE.decrypt cookie_key ck 92ul plain with
      | EE.AuthenticationFailure -> None
      | EE.Success ->
        let random = random_of_buffer plain in
        let id = id_of_random random in
        if model then
          let h2 = get () in
          assert (phi (B.as_seq h2 plain));
          let t:_connection_table = table in
          recall_p t (fun h -> 
            T.defined t id h /\
            (let c = T.value_of t id h in
             token_p c (fun h' -> 
             Sent_HRR? (sel h' c) /\
             CH1 random == Sent_HRR?.ch (sel h' c))));
          Some (id, random)
        else Some ((), random)
    in
    pop_frame();
    let h1 = get () in
    assume (B.modifies B.loc_none h0 h1);
    AE.frame_invariant h0 cookie_key B.loc_none h1;
    res
    end


let receive_client_hello2 t id c ch2 =
  let h0 = get () in
  match validate_cookie t ch2 with
  | None -> false
  | Some id0 -> 
    if ch_compatible ch2 (Init?.cfg !c) then
      begin
      c := Sent_ServerHello ch2 id0;
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
  c := Complete (Sent_ServerHello?.ch c0)
               (Sent_ServerHello?.id1 c0);
  let h1 = get () in
  assert (
    if model then
      let t:_connection_table = t in
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0
    else True)

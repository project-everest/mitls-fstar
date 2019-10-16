module ConnectionTable
friend ConnectionTable_Aux

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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 30"

#push-options "--max_ifuel 1"

let create id cfg =
  if model then
    begin
    let t:_connection_table = table in
    recall t;
    let h0 = get () in
    let p (id:connection_id{T.defined t id h0}) = frameOf (T.value_of t id h0) in
    testify_forall_region_contains_pred #_ #p ()
    end;

  let h0 = get () in
  let rgn1 = new_region rgn in
  let c : mmmref connection rel = ralloc_mm rgn1 (Init cfg) in

  if model then
    begin
    let t:_connection_table = table in
    assert (forall (id:connection_id).
      T.defined t id h0 ==> ~(c == T.value_of t id h0));
    let h1 = get () in
    T.extend t id c;
    let h2 = get() in
    B.modifies_loc_regions_intro (Set.singleton (frameOf t)) h1 h2;
    B.modifies_loc_addresses_intro (frameOf t) (Set.singleton (as_addr t)) B.loc_none h1 h2;
    assert (
      forall (id':connection_id).{:pattern (T.value_of t id' h2)}
        T.defined t id' h2 ==> (T.defined t id' h0 \/ T.value_of t id' h2 == c))
    end;
  c

#pop-options

let free_connection id c =
  let h0 = get () in
  rfree c;
  if model then
    let h1 = get () in
    let t:_connection_table = table in
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

let receive_client_hello1 id c ch =
  let h0 = get () in
  if ch_compatible ch (Init?.cfg !c) then
    let id0 : maybe_id = if model then 0uy else () in
    c := Sent_ServerHello ch id0
  else
    c := Sent_HRR ch;
  if model then
    let h1 = get () in
    let t:_connection_table = table in
    assert (
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0)

assume
val _random_of_buffer: b:B.buffer UInt8.t -> ST random
  (requires fun h -> B.live h b /\ B.length b >= 32)
  (ensures  fun h0 r h1 -> h0 == h1 /\ r == Seq.slice (B.as_seq h0 b) 0 32)

let random_of_buffer = _random_of_buffer

let validate_cookie ck =
    begin
    let h0 = get () in
    push_frame();
    let plain = B.alloca 0uy 64ul in
    let h1 = get () in
    let res : option (maybe_id & random) =
      match TS.decrypt TS.ServerCookie plain 64ul ck with
      | EE.Success ->
        let random = random_of_buffer plain in
        let id = id_of_random random in
        if model then
          let t:_connection_table = table in
          recall_p t (fun h -> 
            T.defined t id h /\
            (let c = T.value_of t id h in
             token_p c (fun h' -> 
             Sent_HRR? (sel h' c) /\
             CH1 random == Sent_HRR?.ch (sel h' c))));
          Some (id, random)
        else Some ((), random)
      | _ -> None
    in
    let h3 = get () in
    pop_frame();
    let h4 = get () in
    res
    end

let receive_client_hello2 id c ch2 =
  let h0 = get () in
  let CH2 random ck = ch2 in
  match validate_cookie ck with
  | None -> 
    begin
    let h1 = get() in  
    assert (
      if model then
        let t:_connection_table = table in
        forall (id:connection_id).{:pattern (T.defined t id h1)}
          T.defined t id h1 ==> T.defined t id h0
      else True);
    false
    end
  | Some (id0, random0) -> 
    let cfg = Init?.cfg !c in
    if ch_compatible ch2 cfg && random = random0 then
      begin
      let h0' = get () in
      c := Sent_ServerHello ch2 id0;
      let h1 = get () in
      assert (
        if model then
        let t:_connection_table = table in
        forall (id:connection_id).{:pattern (T.defined t id h1)}
          T.defined t id h1 ==> T.defined t id h0
      else True);
      true
      end
    else
    begin
      let h1 = get() in  
      assert (
        if model then
          let t:_connection_table = table in
          forall (id:connection_id).{:pattern (T.defined t id h1)}
            T.defined t id h1 ==> T.defined t id h0
        else True);
      false
      end

let receive_client_finished id c =
  let c0 = !c in
  let h0 = get() in
  c := Complete (Sent_ServerHello?.ch c0) (Sent_ServerHello?.id1 c0);
  let h1 = get () in
  assert (
    if model then
      let t:_connection_table = table in
      forall (id:connection_id).{:pattern (T.defined t id h1)}
        T.defined t id h1 ==> T.defined t id h0
    else True)

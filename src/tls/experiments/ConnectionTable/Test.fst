module Test

open ConnectionTable_Aux
open ConnectionTable

open FStar.HyperStack.ST

module T = FStar.Monotonic.DependentMap
module B = LowStar.Buffer
module AE = Crypto.AEAD
module HS = FStar.HyperStack

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

(* Added a pattern; all alternatives I tried didn't work or were too cumbersome *)
val token_functoriality
  (#a:Type0) (#rel:Preorder.preorder a) (r:mreference a rel)
  (p:mem_predicate{token_p r p}) (q:mem_predicate{forall (h:HS.mem). p h ==> q h})
  : Lemma (token_p r q)
   [SMTPat (token_p r p); SMTPat (token_p r q)]
let token_functoriality #a #rel r p q =
  token_functoriality r p q

val frame_invariant
  (h: HS.mem) (s: AE.state alg phi)
  (l: B.loc) (h' : HS.mem)
: Lemma
  (requires B.modifies l h h' /\ B.loc_disjoint l (AE.footprint s) /\ AE.invariant h s)
  (ensures  AE.invariant h' s)
  [SMTPat (AE.invariant h s); SMTPat (B.modifies l h h')] 
let frame_invariant h s l h' =
  AE.frame_invariant h s l h'

(*
   This tests the server side of a full handshake with mismatched parameters:

   1. Assume the global connection table is empty
   2. Create a first connection c1 with id = 1 (in Init state)
   3. Receive a ClientHello ch1 on c1. Transition c1 to Sent_HRR ch1
   4. Deallocate c1
   5. Create a second connection c2 with the same configuration (in Init state)
   6. Create a cookie matching ch1 and encrypt it using Crypto.AE
   7. Receive a ClientHello ch2 with this cookie on c2.
   7. If the configuration of c2 is compatible with ch2,
      a. Transition c2 to Sent_ServerHello ch2 1, with c1 as the matching 
         initial connection
      b. Receive a ClientFinished on c2 and transition c2 to Complete ch2 1
   8. Deallocate c2
   
   The connection table invariant is preserved throughout. 
   For example, before deallocating c2 we can prove there was a matching
   connection in the table that ended in Sent_HRR state, even if it was freed.
*)

val test (cfg:configuration) : ST unit 
  (requires fun h0 ->
    Some? cookie_key /\
    AE.invariant h0 (Some?.v cookie_key) /\ 
    (if model then
      let t : _connection_table = table in
      inv t h0 /\
      HS.contains h0 t /\ 
      HS.sel h0 t == T.empty
    else True) /\
    witnessed (region_contains_pred rgn))
  (ensures  fun _ t h1 -> model ==> inv table h1)

let test cfg =
  let h0 = get () in
  let id1 = if model then 1uy else () in
  let id2 = if model then 2uy else () in
  let c1 = create id1 cfg in
  let ch1 = CH1 (Seq.create 32 1uy) in
  receive_client_hello1 id1 c1 ch1;  
  if model then
    begin
    let s = Seq.create 64 1uy in
    let random = Seq.slice s 0 32 in
    let id = id_of_random random in  
    let t : _connection_table = table in
    assert (Seq.eq random (Seq.create 32 1uy));
    T.contains_stable t 1uy c1;
    witness_p c1 (fun h' -> 
      Sent_HRR? (HS.sel h' c1) /\
      CH1 random == Sent_HRR?.ch (HS.sel h' c1));
    witness_p t (fun h -> 
      T.contains t id c1 h /\
      token_p c1 (fun h' ->
        Sent_HRR? (HS.sel h' c1) /\
        CH1 random == Sent_HRR?.ch (HS.sel h' c1)));
    assert (phi s)
    end;
  free_connection id1 c1;
  let c2 = create id2 cfg in
  let h1 = get () in
  let plain = B.malloc other_rgn 1uy 64ul in
  let ck = B.malloc other_rgn 0uy 92ul in
  let h2 = get () in  
  //AE.frame_invariant h0 (Some?.v cookie_key) (B.loc_all_regions_from true rgn) h2;
  Crypto.AE.encrypt (Some?.v cookie_key) plain 64ul ck;
  let ch2 = CH2 (Seq.create 32 0uy) ck in
  let h3 = get () in
  if model then
    begin
    let t : _connection_table = table in
    // malloc seems underspecified. It can allocate other buffers in other regions
    assume (forall a rel (r:mreference a rel). 
      HS.frameOf r `HS.extends` table_rgn ==> 
      h2 `HS.contains` r ==> h1 `HS.contains` r);
    framing h1 t (B.loc_union (AE.footprint (Some?.v cookie_key)) (B.loc_buffer ck)) h3
    end;
  if receive_client_hello2 id2 c2 ch2 then receive_client_finished id2 c2;
  free_connection id2 c2

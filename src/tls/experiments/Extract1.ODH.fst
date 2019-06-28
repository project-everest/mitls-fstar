module Extract1.ODH 

open Mem
open Pkg
open Idx 
open Pkg.Tree
open KDF // avoid?

module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap

open Extract1.PRF // for now

// temporary
noextract
let there = Mem.tls_tables_region


/// ODH (precisely tracking the games)
/// --------------------------------------------------------------------------------------------------

// Ideally, we maintain a monotonic map from every honestly-sampled
// initiator share gX to its set of honestly-sampled responders shares
// (i,gY).
// The table exists when [Flags.ideal_KDF], a precondition for [flag_odh]

// Wen need a variant of FStar.Monotonic.Map that enables monotonic updates to
// each entry. We used nested ones to re-use existing libraries, but
// may instead invest is a custom library.
//
// how to share the u and a parameters? intuitively, u is statically
// fixed for everyone, and a is determined by the index i.

//17-10-30 unclear how to fix the usage at packaging-time.  This
// should be entirely static. Intuitively, there is a function from
// indexes to usage. Probably definable with the actual usage (big
// mutual reduction?)
assume val u_of_i: i:id -> d:nat & usage d

type odhid = x:CommonDH.dhi{CommonDH.registered_dhi x}

type peer_index (x:odhid) =
  i:regid & y:CommonDH.dhr x {CommonDH.registered_dhr y /\ registered (Derive i "" (ExtractDH (IDH x y)))}

type peer_instance (#x:odhid) (iy:peer_index x) =
  (let (| d, u |) = u_of_i (dfst iy) in
  secret d u (Derive (dfst iy) "" (ExtractDH (IDH x (dsnd iy)))))

let peer_table (x:odhid): Type0 =
  MDM.t there (peer_index x) (peer_instance #x) (fun _ -> True)
type odh_table = MDM.t there odhid peer_table (fun _ -> True)

let odh_state : (if model then odh_table else unit) =
  if model then MDM.alloc #odhid #peer_table #(fun _ -> True) #there ()
  else ()

type odh_fresh (i:odhid) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    MDM.fresh log i h
  else True)

let lemma_fresh_odh (i:CommonDH.dhi) (h:mem)
  : Lemma (CommonDH.fresh_dhi i h ==> odh_fresh i h)
  = admit () // i:dhi implies registered_dhi i and registered_dhi i /\ fresh_dhi i h ==> False

let lemma_fresh_odh_framing (i:CommonDH.dhi) (h0:mem) (h1:mem)
  : Lemma (odh_fresh i h0 /\ modifies_one CommonDH.dh_region h0 h1 ==> odh_fresh i h1)
  = admit() // assume(HS.disjoint there CommonDH.dh_region)

type odh_defined (i:odhid) =
  (if model then
    let log : odh_table = odh_state in
    witnessed (MDM.defined log i)
  else True)

type odhr_fresh (#i:odhid) (r:peer_index i) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    (match MDM.sel (sel h log) i with
    | Some t ->
      (match MDM.sel (sel h t) r with
      | None -> True
      | _ -> False)
    | _ -> False)
  else True)

let lemma_fresh_dhr (#i:odhid) (r:peer_index i) (h:mem)
  : Lemma (CommonDH.fresh_dhr (dsnd r) h ==> odhr_fresh r h)
  = admit () // contradition on  CommonDH.registered_dhr y

let lemma_fresh_dhr_framing (#i:odhid) (r:peer_index i) (h0:mem) (h1:mem)
  : Lemma (odhr_fresh r h0 /\ modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton tls_honest_region)) h0 h1 ==> odhr_fresh r h1)
  = admit() // assume(HS.disjoint there CommonDH.dh_region)

/// Client-side instance creation
/// (possibly used by many honest servers)
val odh_init: g: CommonDH.group -> ST (CommonDH.ikeyshare g)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    let gx : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton there)) h0 h1
    /\ model ==> (odh_fresh gx h0 /\ odh_defined gx /\ CommonDH.honest_dhi gx))

#set-options "--admit_smt_queries true"
let odh_init g =
  let h0 = get () in
  let x = CommonDH.keygen g in
  let h1 = get () in
  if model then
   begin
    let log : odh_table = odh_state in
    let i : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    lemma_fresh_odh i h0;
    lemma_fresh_odh_framing i h0 h1;
    assert(MDM.sel (sel h1 log) i == None);
    let peers = alloc tls_tables_region <: peer_table i in //17-11-22   MDM.alloc #there #(peer_index i) #(peer_instance #i) #(fun _ -> True) in
    let h2 = get () in
    assume(MDM.sel (sel h2 log) i == None); // FIXME allocate peers somewhere else !!
    MDM.extend log i peers;
    assume(stable_on_t log (MDM.defined log i));
    mr_witness log (MDM.defined log i)
   end;
  x

// TODO crypto agility: do we record keygen as honest for a bad group?

/// Server-side creation and completion
///
/// An elaboration of "derive" for two-secret extraction
/// - kdf is the child KDF package.
/// - HKDF is the concrete algorithm
///
/// We require that gX be the share of a honest initiator,
/// but not that they agree on the salt index

private let register_odh (i:regid) (gX:CommonDH.dhi) (gY:CommonDH.dhr gX)
  : ST (j:regid{j == Derive i "" (ExtractDH (IDH gX gY))})
  (requires fun h0 -> model /\ CommonDH.honest_dhr gY)
  (ensures fun h0 _ h1 -> modifies_one tls_honest_region h0 h1)
  =
  let idh = IDH gX gY in
  let ctx = ExtractDH idh in
  assert(honest_idh ctx);
  let j = Derive i "" ctx in // N.B. this is the only case where i can be corrupt and j honest
  let hlog : i_honesty_table = honesty_table in
  recall hlog;
  match MDM.lookup hlog j with
  | None ->
    let m = !hlog in
    assume(honesty_invariant (MDM.repr (MDM.upd m j true))); // Sepcial case: honest IDH
    MDM.extend hlog j true;
    MDM.contains_stable hlog j true;
    mr_witness hlog (MDM.contains hlog j true); j
  | Some b -> j

val odh_test:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt d u i ->
  gX: odhid{odh_defined gX} ->
  ST (j:peer_index gX{dfst j == i} & peer_instance j)
  (requires fun h0 -> model /\ CommonDH.honest_dhi gX)
  (ensures fun h0 r h1 ->
    // todo, as sanity check
    // let (|gY, s|) = dfst r in
    // flag_odh ==> s == peer_gX gY
    True)

#set-options "--admit_smt_queries true" //17-12-08 

let odh_test #d #u #i a s gX =
  assume ((| d, u |) == u_of_i i); //17-11-01 TODO modelling
  (* we get the same code as in the game by unfolding dh_responder, e.g.
  let y = CommonDH.keygen g in
  let gY = CommonDH.pubshare y in
  let gZ: bytes (*CommonDH.share g*) = ... in  // used only when (not flag_odh)
  *)
  let h0 = get() in
  let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
  let j = register_odh i gX gY in
  let j' : peer_index gX = (| i, gY |) in
  let h1 = get() in
  lemma_fresh_dhr j' h0;
  lemma_fresh_dhr_framing j' h0 h1;
  assert(odhr_fresh j' h1);
  assert(a == get_info j);
  let k: secret d u j =
    if Flags.flag_ODH d then create d u j a (* narrow *)
    else (
      assert(~(idealPRF1 d));
      let raw = HKDF.extract #a.ha (prf_leak s) gZ (* wide, concrete *) in
      assume(~(idealKDF d)); // FIXME(adl): fix the loop in the flag order dependency. See definition of usage for proposed solution
      coerce d u j a raw
    ) in
  let h2 = get() in
  assume(odhr_fresh j' h2); // TODO framing of KDF
  let t: odh_table = odh_state in
  testify(MDM.defined t gX);
  let peers = Some?.v (MDM.lookup t gX) in
  MDM.extend peers j' k;
  (| j' , k |)

unfold let idh_of (#g:CommonDH.group) (x:CommonDH.ikeyshare g) (gY:CommonDH.rshare g (CommonDH.ipubshare x)) =
  IDH (| g, CommonDH.ipubshare x |) gY

// the PRF-ODH oracle, computing with secret exponent x
val odh_prf:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  a: info {a == get_info i}->
  s: salt d u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST (_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))}
   & secret d u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX
    /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
  (ensures fun h0 _ h1 -> True)

// FIXME. Lemma is false. Not sure how to fix
let lemma_fresh_dhr_hinv (#x:CommonDH.dhi) (y:CommonDH.dhr x) (h:mem)
  : Lemma (requires (model ==> CommonDH.fresh_dhr #x y h))
          (ensures ~(honest_idh (ExtractDH (IDH x y))))
  = admit()

let odh_prf #d #u #i a s g x gY =
  let h = get () in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let idh = IDH gX gY in
  assert_norm(idh == idh_of x gY);
  lemma_fresh_dhr_hinv #gX gY h;
  let gZ = CommonDH.dh_initiator g x gY in
  let (| uu, k |) = prf_extract1 #d #u #i a s idh gZ in
  let k' : secret d u (Derive i "" (ExtractDH idh)) = k in
  (| (), k' |)


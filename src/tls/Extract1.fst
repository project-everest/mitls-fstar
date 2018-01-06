module Extract1

open Mem
open Pkg
open Idx 
open Pkg.Tree
open KDF // avoid?

module MM = FStar.Monotonic.Map

// for now 
open Extract1.PRF
open Extract1.ODH

// TODO: instead of CommonDH.keyshare g, we need an abstract stateful
// [abstract type private_keyshare g = mref bool ...] that enables
// calling it exactly once

/// Initiator computes DH keyshare, irrespective of the KDF & salt.
let initI (g:CommonDH.group) = odh_init g

/// Responder computes DH secret material
val extractR:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  s: salt d u i ->
  a: info {a == get_info i} ->
  gX: odhid ->
  ST (i_gY: peer_index gX{dfst i_gY == i} & peer_instance i_gY)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)

let extractR #d #u #i s a gX =
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
   begin
    let t: odh_table = odh_state in
    (if None? (MM.lookup t gX) then
      let peers = MM.alloc #there #(peer_index gX) #(peer_instance #gX) #(fun _ -> True) in
      let h = get() in
      assume(None? (MM.sel (sel h t) gX));
      MM.extend t gX peers;
      assume(stable_on_t t (MM.defined t gX));
      mr_witness t (MM.defined t gX));
    odh_test a s gX
   end
  else
   begin
    // real computation: gY is honestly-generated but the exchange is doomed
    let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
    let idh = IDH gX gY in
    assume(~(honest_idh (ExtractDH idh))); // FIXME
    let (| _ , k |) : ext1 d u i idh = prf_extract1 a s idh gZ in
    let k : secret d u (Derive i "" (ExtractDH idh)) = k in
    let i_gY : peer_index gX = (| i, gY |) in
    let s : peer_instance #gX i_gY = admit() in
    (| i_gY, s |)
   end

(*)
     let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
     CommonDH.honest_dhi gX /\ odh_defined gX
     /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
*)

/// Initiator computes DH secret material
val extractI:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt d u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST(_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))}
    & secret d u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX)
  (ensures fun h0 k h1 -> True)

let extractI #d #u #i a s g x gY =
  let gX: CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
    let t: odh_table = odh_state in
    testify(MM.defined t gX);
    let peers = Some?.v (MM.lookup t gX) in
    let idh = IDH gX gY in
    let i' = Derive i "" (ExtractDH idh) in
    assume(registered i');
    assert(wellformed_id i);
    assume(wellformed_id i'); //17-11-01 same as above?
    let i_gY : peer_index gX = (| i, gY |) in
    let ot = secret d u i' in
    assume ((| d, u |) == u_of_i i); //17-11-01 indexing does not cover u yet
    let o : option ot = MM.lookup peers i_gY in
    match o with
    | Some k -> (| (), k |)
    | None -> assume false; //17-11-22 why?
           odh_prf #d #u #i a s g x gY
  else odh_prf #d #u #i a s g x gY

val extractP:
  #d: nat ->
  #u: usage d ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt d u i ->
  ST(_:unit{registered (Derive i "" (ExtractDH NoIDH))}
    & secret d u (Derive i "" (ExtractDH NoIDH)))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)

let extractP #d #u #i a s =
  let gZ = Hashing.Spec.zeroHash a.ha in
   let (| _, k |) = prf_extract1 a s NoIDH gZ in
   assert(registered (Derive i "" (ExtractDH NoIDH)));
   let k : secret d u (Derive i "" (ExtractDH NoIDH)) = k in
   (| (), k |)

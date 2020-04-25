module ConnectionTable_Aux

module AE = Crypto.AEAD
module B = LowStar.Buffer
module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap
module S = Spec.Agile.AEAD
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let ch_compatible ch cfg = false

let minv (m:T.partial_dependent_map maybe_id connection_ref) =
  forall id1 id2.{:pattern (Some? (DM.sel m id1)); (Some? (DM.sel m id2))}
    (id1 <> id2 /\ Some? (DM.sel m id1) /\ Some? (DM.sel m id2)) ==>
    HS.frameOf (Some?.v (DM.sel m id1)) `HS.disjoint` HS.frameOf (Some?.v (DM.sel m id2))

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
          HST.token_p c' (fun h0 ->
            Sent_HRR? (HS.sel h0 c') /\
            ch_of_cookie ch == Sent_HRR?.ch (HS.sel h0 c'))
        | _ -> False
      else True
    | _ -> True
  else True

(*
  Stateful invariant
  Can't be attached to the table because it needs to dereference connections
*)
let inv t h =
  h `HS.contains` t /\
  (let m = HS.sel h t in
  forall (id:maybe_id).{:pattern (T.defined t id h)}
    (T.defined t id h /\ h `HS.contains` (T.value_of t id h))
    ==> connection_inv m (HS.sel h (Some?.v (T.sel m id))))

let framing h0 t l h1 =
  assert (B.loc_includes (B.loc_all_regions_from true rgn) (B.loc_mreference t));
  assert (forall (id:maybe_id).{:pattern (T.defined t id h1)}
    (T.defined t id h1 /\ h1 `HS.contains` (T.value_of t id h1)) ==>
    B.loc_includes (B.loc_all_regions_from true rgn) 
                   (B.loc_mreference (T.value_of t id h1)));
  assert (forall (id:maybe_id).{:pattern (T.defined t id h1)}
    (T.defined t id h0 /\ h0 `HS.contains` (T.value_of t id h1)) ==>
    B.loc_includes (B.loc_all_regions_from true rgn) 
                   (B.loc_mreference (T.value_of t id h0)))

let alloc _ =
  if model then T.alloc () <: _connection_table

let table = 
  HST.recall_region rgn;
  HST.witness_region rgn;
  alloc ()

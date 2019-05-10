module DefineTable

open Mem

module M = LowStar.Modifies
module DM = FStar.DependentMap
module MH = FStar.Monotonic.Heap
module HS = FStar.HyperStack

friend FStar.Monotonic.DependentMap

let dt_forall #it #vt t pred h =
  model ==> (forall (i:it) (k:vt i).
  {:pattern (defined_as t i k h)}
  defined_as t i k h ==> pred i k h)

let lemma_forall_empty #it #vt t pred h = ()

let lemma_forall_elim #it #vt t pred i k h = ()

val lemma_forall_extend_wit:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: MDM.map it vt ->
  t': MDM.map it vt ->
  pred: (i:it -> vt i -> mem -> GTot Type0) ->
  i: it -> k: vt i ->
  h: mem ->
  x:it -> y:vt x ->
  Lemma
    (requires model /\ pred i k h /\
      ((MDM.sel t x == Some y) ==> pred x y h) /\
      t' == (| i, k |) :: t)
    (ensures (MDM.sel t' x == Some y) ==> pred x y h)

let lemma_forall_extend_wit #it #vt t t' pred i k h x y = ()

let lemma_forall_extend #it #vt t pred pred_frame i k h0 h1 =
  if model then
    let t0 = HS.sel h0 (ideal t) in
    let t1 = HS.sel h1 (ideal t) in
    let pred_frame' (i:it) (k:vt i) (h0:mem) (h1:mem)
      : Lemma ((pred i k h0 /\ M.modifies (loc t) h0 h1) ==> pred i k h1) =
      FStar.Classical.move_requires (pred_frame i k h0) h1
      in
    let lupd (x:it) (y:vt x) : Lemma
      (requires (MDM.sel t0 x == Some y) ==> pred x y h0)
      (ensures (MDM.sel t1 x == Some y) ==> pred x y h1) =
      assert(MDM.sel t1 x == (if x = i then Some k else MDM.sel t0 x));
      if x = i then ()
      else pred_frame' x y h0 h1
      in
    let prove_on_witness (x:it) (y:vt x)
      : Lemma (MDM.sel t1 x == Some y ==> pred x y h1)
      =
      lemma_forall_elim t pred x y h0;
      lupd x y;
      lemma_forall_extend_wit t0 t1 pred i k h1 x y in
    FStar.Classical.forall_intro_2 prove_on_witness
  else ()

val lemma_forall_frame_wit:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (i:it -> vt i -> mem -> GTot Type0) ->
  pred_fp: M.loc ->
  pred_frame: (i:it -> k:vt i -> h0:mem -> l:M.loc -> h1:mem -> Lemma
    ((pred i k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l pred_fp)
     ==> pred i k h1)) ->
  h0: mem -> l:M.loc -> h1: mem ->
  x:it -> y:vt x ->
  Lemma
    (requires M.modifies l h0 h1 /\ t `used_in` h0 /\
      (defined_as t x y h0 ==> pred x y h0) /\
      M.loc_disjoint (loc t) l /\ M.loc_disjoint pred_fp l)
    (ensures defined_as t x y h1 ==> pred x y h1)

let lemma_forall_frame_wit #it #vt t pred pred_fp pred_frame h0 l h1 x y =
  lemma_frame_dt t h0 l h1;
  pred_frame x y h0 l h1

let lemma_forall_frame #it #vt t pred pred_fp pred_frame h0 l h1 =
  if model then 
    let pred_frame' (i:it) (k:vt i) (h0:mem) (l:M.loc) (h1:mem)
      : Lemma ((pred i k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l pred_fp)
         ==> pred i k h1) =
      FStar.Classical.move_requires (pred_frame i k h0 l) h1
      in
    let prove_on_witness (x:it) (y:vt x)
      : Lemma (defined_as t x y h1 ==> pred x y h1)
      =
      lemma_forall_elim t pred x y h0;
      lemma_forall_frame_wit t pred pred_fp pred_frame' h0 l h1 x y in
    FStar.Classical.forall_intro_2 prove_on_witness
  else ()

val fold_gtot: ('a -> 'b -> GTot 'a) -> 'a -> l:list 'b -> GTot 'a (decreases l)
let rec fold_gtot f x l = match l with
  | [] -> x
  | hd::tl -> fold_gtot f (f x hd) tl

let footprint #it #vt t fp h =
  if model then 
    let l = HS.sel h (ideal t) in
    fold_gtot (fun l (| i, k |) -> M.loc_union l (fp i k)) M.loc_none l
  else M.loc_none


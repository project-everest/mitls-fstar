module DefineTable

open Mem

module M = LowStar.Modifies
module DM = FStar.DependentMap
module MH = FStar.Monotonic.Heap
module HS = FStar.HyperStack

open FStar.HyperStack.ST

friend FStar.Monotonic.DependentMap

let alloc #it vt =
  if model then
    MDM.alloc #it #vt #(fun _ -> True) #tls_define_region ()
  else ()

let extend #it #vt t i k =
  if model then
   begin
    let t0 = ideal t in
    recall t0;
    t0 := MDM.upd !t0 i k;
    mr_witness t0 (MDM.contains t0 i k)
   end
  else ()

let dt_forall #it #vt t pred h =
  model ==> (forall (i:it) (k:vt i).
  {:pattern (defined_as t i k h)}
  defined_as t i k h ==> pred k h)

val fold_gtot: ('a -> 'b -> GTot 'a) -> 'a -> l:list 'b -> GTot 'a (decreases l)
let rec fold_gtot f x l = match l with
  | [] -> x
  | hd::tl -> f (fold_gtot f x tl) hd

let fp_add (#it:eqtype) (#vt:it->Type) (#p:M.loc) (fp:local_fp vt p)
  (l:sub_loc p) (cur:(i:it & vt i)) : GTot (sub_loc p) =
  let (| i, k |) = cur in
  M.loc_union l (fp k)

let footprint #it #vt t #parent fp h =
  if model then 
    let l = HS.sel h (ideal t) in
    fold_gtot (fp_add fp) M.loc_none l
  else M.loc_none

let lemma_footprint_frame #it #vt t #p fp h0 h1 = ()

let lemma_footprint_extend #it #vt t #p fp i k h0 h1 = ()

let rec lemma_fp_includes (#it:eqtype) (vt:it->Type) (t:MDM.map it vt)
  (#p:M.loc) (fp:local_fp vt p) (i:it) (k:vt i)
  : Lemma (requires (MDM.sel t i == Some k))
  (ensures fold_gtot (fp_add fp) M.loc_none t `M.loc_includes` (fp k))
  (decreases %[t])
  =
  match t with
  | [] -> ()
  | (| x, y |) :: tl ->
    if x = i then ()
    else lemma_fp_includes vt tl fp i k

let lemma_footprint_includes #it #vt t #p fp i k h =
  if model then
    let t0 = HS.sel h (ideal t) in
    lemma_fp_includes vt t0 fp i k
  else ()

let lemma_forall_empty #it #vt t pred h = ()

let lemma_forall_elim #it #vt t pred i k h = ()

val lemma_forall_extend_wit:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: MDM.map it vt ->
  t': MDM.map it vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  #i: it -> k: vt i ->
  h: mem ->
  x:it -> y:vt x ->
  Lemma
    (requires model /\ pred k h /\
      ((MDM.sel t x == Some y) ==> pred #x y h) /\
      t' == (| i, k |) :: t)
    (ensures (MDM.sel t' x == Some y) ==> pred #x y h)

let lemma_forall_extend_wit #it #vt t t' pred #i k h x y = ()

let lemma_forall_extend #it #vt t pred #p fp pred_frame #i k h0 h1 =
  if model then
    let t0 = HS.sel h0 (ideal t) in
    let t1 = HS.sel h1 (ideal t) in
    let pred_frame' (#i:it) (k:vt i) (h0:mem) (l:M.loc) (h1:mem)
      : Lemma ((pred k h0 /\ M.modifies l h0 h1 /\
        M.loc_disjoint l (fp k)) ==> pred k h1) =
      FStar.Classical.move_requires (pred_frame k h0 l) h1
      in
    let lupd (#x:it) (y:vt x) : Lemma
      (requires (MDM.sel t0 x == Some y) ==> pred #x y h0)
      (ensures (MDM.sel t1 x == Some y) ==> pred #x y h1) =
      assert(MDM.sel t1 x == (if x = i then Some k else MDM.sel t0 x));
      if x = i then ()
      else pred_frame' #x y h0 (loc t) h1
      in
    let prove_on_witness (x:it) (y:vt x)
      : Lemma (MDM.sel t1 x == Some y ==> pred #x y h1)
      =
      lemma_forall_elim t pred x y h0;
      lupd #x y;
      lemma_forall_extend_wit t0 t1 pred #i k h1 x y
      in
    FStar.Classical.forall_intro_2 prove_on_witness
  else ()

val lemma_forall_frame_wit:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  pred_frame: (#i:it -> k:vt i -> h0:mem -> l:M.loc -> h1:mem -> Lemma
    ((pred k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l (fp k))
     ==> pred k h1)) ->
  h0: mem -> l:M.loc -> h1: mem ->
  x:it -> y:vt x ->
  Lemma
    (requires M.modifies l h0 h1 /\ t `live` h0 /\
      (defined_as t x y h0 ==> pred y h0) /\
      M.loc_disjoint l (loc t) /\ M.loc_disjoint l (fp y))
    (ensures defined_as t x y h1 ==> pred y h1)

let lemma_forall_frame_wit #it #vt t pred #p fp pred_frame h0 l h1 x y =
  lemma_unchanged_frame t h0 l h1;
  pred_frame y h0 l h1

// Could be simplified if FStar.Classical had
// move_requires_2 or forall_impl_intro_2
let lemma_forall_frame #it #vt t pred #p fp pred_frame h0 l h1 =
  if model then 
    let pred_frame' (#i:it) (k:vt i) (h0:mem) (l:M.loc) (h1:mem)
      : Lemma ((pred k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l (fp k))
         ==> pred k h1) =
      FStar.Classical.move_requires (pred_frame k h0 l) h1
      in
    let prove_on_witness (v:(i:it & vt i))
      : Lemma (requires defined_as t (dfst v) (dsnd v) h1)
        (ensures pred (dsnd v) h1)
      =
      let (| x, y |) = v in
      lemma_forall_elim t pred x y h0;
      lemma_footprint_includes t fp x y h0;
      lemma_forall_frame_wit t pred fp pred_frame' h0 l h1 x y
      in
    let prove_on_witness2 (x:it) (y:vt x)
      : Lemma (defined_as t x y h1 ==> pred y h1)
      = FStar.Classical.move_requires prove_on_witness (|x,y|)
      in
    FStar.Classical.forall_intro_2 prove_on_witness2
  else ()

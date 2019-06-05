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

let extend #it #vt t #i k =
  if model then
   begin
    let t0 = ideal t in
    recall t0;
    t0 := MDM.upd !t0 i k;
    mr_witness t0 (MDM.contains t0 i k)
   end
  else ()

let dt_forall #it #vt t pred h =
  model ==> (forall (i:it) (k:vt i{defined_as t k h}).
  {:pattern (defined_as t k h)} pred k h)

val fold_gtot: ('a -> 'b -> GTot 'a) -> 'a -> l:list 'b -> GTot 'a (decreases l)
let rec fold_gtot f x l = match l with
  | [] -> x
  | hd::tl -> f (fold_gtot f x tl) hd

let fp_add (#it:eqtype) (#vt:it->Type)
  (fp:local_fp vt) (l:M.loc) (cur:(i:it & vt i)) =
  let (| i, k |) = cur in
  M.loc_union l (fp k)

let empty_fp #it vt =
  fun (#i:it) (k:vt i) -> M.loc_none

let lemma_empty_fp_none #it #vt #i k = ()

let rec lemma_fold_constant (#it:eqtype) (#vt:it->Type)
  (f: M.loc -> (i:it & vt i) -> GTot M.loc)
  (x0:M.loc) (l: list (i:it & vt i))
  : Lemma
    (requires (forall (x:M.loc) (y:(i:it & vt i)). f x y == x))
    (ensures fold_gtot f x0 l == x0)
  =
  match l with
  | [] -> ()
  | h :: t -> lemma_fold_constant f x0 t

let footprint #it #vt t fp h =
  if model then 
    let l = HS.sel h (ideal t) in
    fold_gtot (fp_add fp) M.loc_none l
  else M.loc_none

let lemma_footprint_empty_fp #it #vt t h =
  if model then
    let l = HS.sel h (ideal t) in
    lemma_fold_constant (fp_add (empty_fp vt)) M.loc_none l
  else ()

let lemma_footprint_empty #it #vt t fp h0 = ()

let lemma_footprint_frame #it #vt t fp h0 h1 = ()

let lemma_footprint_extend #it #vt t fp #i k h0 h1 = ()

let rec lemma_fp_includes (#it:eqtype) (vt:it->Type) (t:MDM.map it vt)
  (fp:local_fp vt) (#i:it) (k:vt i)
  : Lemma (requires (MDM.sel t i == Some k))
  (ensures fold_gtot (fp_add fp) M.loc_none t `M.loc_includes` (fp k))
  (decreases %[t])
  =
  match t with
  | [] -> ()
  | (| x, y |) :: tl ->
    if x = i then ()
    else lemma_fp_includes vt tl fp k

let lemma_footprint_includes #it #vt t fp #i k h =
  if model then
    let t0 = HS.sel h (ideal t) in
    lemma_fp_includes vt t0 fp k
  else ()

let lemma_forall_empty #it #vt t pred h = ()

let lemma_forall_elim #it #vt t pred h #i k = ()

let lemma_forall_extend #it #vt t pred fp pred_frame #i k h0 h1 =
  if model then
    let prove_on_witness (x:it) (y:vt x{defined_as t y h1})
      : Lemma (pred y h1) =
      if x = i then ()
      else (
        lemma_forall_elim t pred h0 y;
        lemma_footprint_includes t fp y h0;
        pred_frame y h0 (loc t) h1
      ) in
    FStar.Classical.forall_intro_2 prove_on_witness
  else ()

let lemma_forall_frame #it #vt t pred fp pred_frame h0 l h1 =
  if model then 
    let prove_on_witness (x:it) (y:vt x{defined_as t y h1})
      : Lemma (ensures pred y h1)
      =
      lemma_forall_elim t pred h0 y;
      lemma_footprint_includes t fp y h0;
      pred_frame y h0 l h1
      in
    FStar.Classical.forall_intro_2 prove_on_witness
  else ()

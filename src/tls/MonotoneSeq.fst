module MonotoneSeq
open FStar.Seq
open FStar.SeqProperties

val forall_intro: #a:Type -> #p:(x:a -> GTot Type0) 
		-> =f:(x:a -> Lemma (p x))
		-> Lemma (forall (x:a). p x)
let forall_intro #a #p f = admit()

(* Some basic stuff, should be moved to FStar.Squash, probably *)
val forall_intro_2: #a:Type -> #b:(a -> Type) -> #p:(x:a -> b x -> GTot Type0) 
          -> =f: (x:a -> y:b x -> Lemma (p x y))
	  -> Lemma (forall (x:a) (y:b x). p x y)
let forall_intro_2 #a #b #p f = 
  let g : x:a -> Lemma (forall (y:b x). p x y) = fun x -> forall_intro (f x) in
  forall_intro g

val forall_intro_3: #a:Type -> #b:(a -> Type) -> #c:(x:a -> y:b x -> Type) -> #p:(x:a -> y:b x -> z:c x y -> Type0) 
          -> =f: (x:a -> y:b x -> z:c x y -> Lemma (p x y z))
	  -> Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)
let forall_intro_3 #a #b #c #p f = 
  let g : x:a -> Lemma (forall (y:b x) (z:c x y). p x y z) = fun x -> forall_intro_2 (f x) in
  forall_intro g

val exists_intro: #a:Type -> p:(a -> Type) -> witness:a -> Lemma
  (requires (p witness))
  (ensures (exists (x:a). p x))
let exists_intro (#a:Type) (p:(a -> Type)) witness = ()

val exists_elim:
      #a:Type
    -> #p:(a -> Type)
    -> #b:Type
    -> #q:(b -> Type)
    -> #r:Type
    -> =f:(x:a -> Lemma (p x ==> r))
    -> Lemma ((exists (x:a). p x) ==> r)
let exists_elim #a #p #b #q #r f = forall_intro f

val exists_elim_2: 
      #a:Type
    -> #p:(a -> Type)
    -> #b:Type
    -> #q:(b -> Type)
    -> #r:Type
    -> =f:(x:a -> y:b -> Lemma ((p x /\ q y) ==> r))
    -> Lemma (((exists (x:a). p x) /\ (exists (y:b). q y)) ==> r)
let exists_elim_2 #a #p #b #q #r f = forall_intro_2 f

////////////////////////////////////////////////////////////////////////////////

abstract let seq_extension (#a:Type) (s1:seq a) (s2:seq a) (s3:seq a) =
  equal s3 (append s1 s2)
  
abstract let grows (#a:Type) (s1:seq a) (s3:seq a) =
  exists (s2:seq a). seq_extension s1 s2 s3
  
val seq_extension_reflexive: #a:Type -> s:seq a -> Lemma
  (ensures (grows s s))
let seq_extension_reflexive #a s =
  exists_intro (fun w -> seq_extension s w s) (Seq.createEmpty #a)

val seq_extension_transitive: #a:Type
  -> s1:seq a
  -> s2:seq a
  -> s3:seq a
  -> s1':seq a
  -> s2':seq a
  -> Lemma
    ((seq_extension s1 s1' s2 
      /\ seq_extension s2 s2' s3)
      ==> seq_extension s1 (Seq.append s1' s2') s3)
let seq_extension_transitive #a s1 s2 s3 s1' s2' = ()

val seq_extends_to_transitive_aux: #a:Type
  -> s1:seq a
  -> s2:seq a
  -> s3:seq a
  -> s1':seq a
  -> s2':seq a
  -> Lemma ((seq_extension s1 s1' s2 
            /\ seq_extension s2 s2' s3)
          ==> grows s1 s3)
let seq_extends_to_transitive_aux #a s1 s2 s3 s1' s2' =
  seq_extension_transitive s1 s2 s3 s1' s2'


val grows_transitive: #a:Type
  -> s1:seq a
  -> s2:seq a
  -> s3:seq a
  -> Lemma ((grows s1 s2 /\ grows s2 s3)
           ==> grows s1 s3)
let grows_transitive #a s1 s2 s3 =
  exists_elim_2 (seq_extends_to_transitive_aux s1 s2 s3)

////////////////////////////////////////////////////////////////////////////////
open FStar.Monotonic.RRef
open FStar.HyperHeap

val lemma_grows_monotone: #a:Type
  -> Lemma (monotonic (seq a) (grows #a))
let lemma_grows_monotone #a =
  forall_intro (seq_extension_reflexive #a);
  forall_intro_3 (grows_transitive #a)

val snoc : #a:Type -> seq a -> a -> Tot (seq a)
let snoc #a s x = Seq.append s (Seq.create 1 x)

val lemma_snoc_extends: #a:Type 
  -> s:seq a
  -> x:a 
  -> Lemma (requires True)
	  (ensures (grows s (snoc s x)))
	  [SMTPat (grows s (snoc s x))]
let lemma_snoc_extends #a s x = ()

val lemma_mem_snoc: #a:Type 
  -> s:seq a
  -> x:a 
  -> Lemma 
    (ensures (SeqProperties.mem x (snoc s x)))
let lemma_mem_snoc #a s x = SeqProperties.lemma_append_count s (Seq.create 1 x)

val alloc_mref_seq: #a:Type -> r:FStar.HyperHeap.rid -> init:seq a
  -> ST (m_rref r (seq a) grows)
       (requires (fun _ -> True))
       (ensures (fun h0 m h1 -> FStar.ST.ralloc_post r init h0 (as_rref m) h1))
let alloc_mref_seq #a r init = 
  lemma_grows_monotone #a;
  FStar.Monotonic.RRef.m_alloc r init


(* TODO: this fails with a silly inconsistent qualifier error *)
(* logic val mem_index: #a:Type -> #i:rid -> n:nat -> x:a -> r:m_rref i (seq a) grows -> t -> GTot Type0 *)
(* logic let mem_index #a #i n x r h =  *)
(*       mem x r h *)
(*       /\ Seq.length (m_sel h r) > n *)
(*       /\ Seq.index (m_sel h r) n = x *)

val mem : #a:Type -> #i:rid -> x:a -> r:m_rref i (seq a) grows -> t -> GTot Type0
let mem #a #i x r h = b2t (SeqProperties.mem x (m_sel h r))

let at_least (#a:Type) (#i:rid) (n:nat) (x:a) (r:m_rref i (seq a) grows) (h:t) = 
      mem x r h
      /\ Seq.length (m_sel h r) > n
      /\ Seq.index (m_sel h r) n = x

val at_least_is_stable: #a:Type -> #i:rid
		   -> n:nat
		   -> x:a
		   -> r:m_rref i (seq a) grows
		   -> Lemma (ensures stable_on_t r (at_least n x r))
let at_least_is_stable #a #i n x r = 
  let at_least_is_stable_aux: 
		     h0:t
		   -> h1:t
		   -> Lemma ((at_least n x r h0
			    /\ grows (m_sel h0 r) (m_sel h1 r))
			    ==> at_least n x r h1) = 
       fun h0 h1 -> forall_intro_2 (lemma_mem_append #a) in
  forall_intro_2 at_least_is_stable_aux

val write_at_end: #a:Type -> #i:rid
	       -> r:m_rref i (seq a) grows
	       -> x:a
	       -> ST unit
 		 (requires (fun h -> True))
		 (ensures (fun h0 _ h1 ->
	               m_contains r h1
		     /\ modifies (Set.singleton i) h0 h1
		     /\ modifies_rref i !{as_ref (as_rref r)} h0 h1
		     /\ m_sel h1 r = snoc (m_sel h0 r) x
		     /\ witnessed (at_least (Seq.length (m_sel h0 r)) x r)))
let write_at_end #a #i r x =
  m_recall r;
  let s0 = m_read r in
  let n = Seq.length s0 in
  m_write r (snoc s0 x);
  at_least_is_stable n x r;
  lemma_mem_snoc s0 x;
  witness r (at_least n x r)


(* An earlier experiment with a weaker witnessed predicate *)
(* val write_at_end: #a:Type -> #i:rid *)
(* 	       -> r:m_rref i (seq a) grows *)
(* 	       -> x:a *)
(* 	       -> ST unit *)
(*  		 (requires (fun h -> True)) *)
(* 		 (ensures (fun h0 _ h1 -> *)
(* 	               m_contains r h1 *)
(* 		     /\ modifies (Set.singleton i) h0 h1 *)
(* 		     /\ modifies_rref i !{as_ref (as_rref r)} h0 h1 *)
(* 		     /\ m_sel h1 r = snoc (m_sel h0 r) x *)
(* 		     /\ witnessed (mem x r))) *)
(* let write_at_end #a #i r x = *)
(*   m_recall r; *)
(*   let s0 = m_read r in *)
(*   m_write r (snoc s0 x); *)
(*   mem_is_stable r x; *)
(*   lemma_mem_snoc s0 x; *)
(*   witness r (mem x r) *)



(* val mem_is_stable: #a:Type -> #i:rid *)
(* 		   -> r:m_rref i (seq a) grows *)
(* 		   -> x:a *)
(* 		   -> Lemma (ensures stable_on_t r (mem x r)) *)
(* let mem_is_stable #a #i r x =  *)
(*   let mem_is_stable_aux:  *)
(* 		     h0:t *)
(* 		   -> h1:t *)
(* 		   -> Lemma ((mem x r h0 *)
(* 			    /\ grows (m_sel h0 r) (m_sel h1 r)) *)
(* 			    ==> mem x r h1) =  *)
(*        fun h0 h1 -> forall_intro_2 (lemma_mem_append #a) in *)
(*   forall_intro_2 mem_is_stable_aux *)

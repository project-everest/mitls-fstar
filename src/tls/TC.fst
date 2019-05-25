module TC 

open FStar.Preorder
open FStar.Tactics

noeq
type closure (#a:Type0) (r:relation a) : a -> a -> Type0 =
| Refl: x:a -> closure r x x
| Step: x:a -> y:a -> r x y -> closure r x y
| Closure: x:a -> y:a -> z:a -> closure r x y -> closure r y z -> closure r x z

val closure_reflexive: #a:Type0 -> r:relation a -> Lemma (reflexive (closure r))
let closure_reflexive #a r =
  assert (forall x. closure r x x) by
    (let x = forall_intro () in mapply (quote Refl))

val closure_transitive: #a:Type0 -> r:relation a -> Lemma (transitive (closure r))
let closure_transitive #a r =
  assert (transitive (closure r)) by
    (let x = forall_intro () in
     let y = forall_intro () in
     let z = forall_intro () in
     let h = implies_intro () in
     and_elim (binder_to_term h);
     let h1 = implies_intro () in
     let h2 = implies_intro () in
     mapply (quote (Closure #a #r));
     assumption ();
     assumption ())

val reflexive_transitive_closure: #a:Type0 -> relation a -> preorder a
let reflexive_transitive_closure #a r =
  closure_reflexive r;
  closure_transitive r;
  closure r

// anticipating abstraction 
let step #a #r (x y:a) (#h: r x y): closure r x y = Step x y h

assume val inv_closure:
  #a: Type0 -> 
  step: relation a ->
  p: (a -> Type0) -> 
  hr: (x:a -> y:a {p x /\ step x y} -> Lemma(p y)) ->
  x: a -> y: a {p x /\ closure step x y} -> Lemma(p y)

// test 
type state = 
  | A 
  | B 
  | C 
let r x y = 
  match x, y with 
  | A, B
  | B, C
  | C, B -> True
  | _ -> False
let cl = reflexive_transitive_closure r
let p = function | A -> False | B | C -> True 
let q = function | A | B -> False | C -> True 

let hp (x:state) (y:state{p x /\ r x y}): Lemma(p y) = ()
// match x, y with 
// | B, C -> assert(p y)
// | C, B -> assert(p y)

// let hq x y: Lemma(q x /\ r x y ==> q y) = ()

let test = inv_closure r p hp 

let f (x:state{ cl B x }) = 
  test B x;
  assert(x <> A)




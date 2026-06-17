module TLS13.Impl.Parser.PureExists

(**
  Helper machinery for *producing* a "pure-only" existential separation-logic
  predicate, i.e. one of the shape

      exists* x. pure (q x)

  with no heap (slprop) anchor that pins the existential witness.

  The Pulse prover cannot directly [fold]/[intro] such an existential when the
  body [q] is a non-trivial proposition (conjunction, witness under a
  constructor, abstract predicate): its witness solver only handles a bare
  equality body [pure (x == t)].

  We work around this here, using only the public [Pulse.Lib.Core] slprop
  equivalence API (no [PulseCore] internals, no admits):

    * [core_rewrite] : a thin, non-#lang-pulse wrapper around
      [Pulse.Lib.Core.rewrite] (the bare name [rewrite] is a Pulse keyword and
      cannot be applied as a function inside a #lang-pulse module).

    * [mk_pure_exists_equiv] : builds [slprop_equiv (exists* x. pure (x == a))
      named] from (i) a *definitional* equality witnessing that [named] unfolds
      to [exists* x. pure (q x)] and (ii) a per-element propositional
      equivalence [(x == a) <==> q x].

  The caller then introduces the *simple-bodied* existential
  [exists* x. pure (x == a)] (whose witness IS solvable) and rewrites it into
  [named] across the equivalence.  Framing the simple-bodied existential works
  because its re-introduced witness obligation [pure (?u == a)] is exactly the
  bare-equality shape the witness solver handles.
*)

open Pulse.Lib.Core
module CL = FStar.Classical

(* Function-form wrapper of the [rewrite] ghost step (keyword clash workaround). *)
let core_rewrite (p q:slprop) (e:slprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)
  = rewrite p q e

(* Build [slprop_equiv (exists* x. pure (x == a)) named] given:
   - [def_eq]: [named] is definitionally [exists* x. pure (q x)];
   - [iff]   : for every [x], [(x == a) <==> q x]. *)
let mk_pure_exists_equiv (#t:Type) (a:t) (q:t -> prop) (named:slprop)
  (def_eq: squash (op_exists_Star (fun (x:t) -> pure (q x)) == named))
  (iff: (x:t -> Lemma ((x == a) <==> q x)))
  : slprop_equiv (op_exists_Star (fun (x:t) -> pure (x == a))) named
  =
  let pp : (t -> slprop) = (fun (x:t) -> pure (x == a)) in
  let rr : (t -> slprop) = (fun (x:t) -> pure (q x)) in
  let pelem (x:t) : slprop_equiv (pp x) (rr x) =
    iff x;
    FStar.PropositionalExtensionality.apply (x == a) (q x);
    slprop_equiv_ext (pp x) (rr x) ()
  in
  let _fa : (forall (x:t). slprop_equiv (pp x) (rr x)) =
    CL.forall_intro_squash_gtot pelem in
  let step1 : slprop_equiv (op_exists_Star pp) (op_exists_Star rr) =
    slprop_equiv_exists pp rr () in
  let step2 : slprop_equiv (op_exists_Star rr) named =
    slprop_equiv_ext (op_exists_Star rr) named def_eq in
  slprop_equiv_trans (op_exists_Star pp) (op_exists_Star rr) named step1 step2

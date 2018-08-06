module LowParse.TacLib
include FStar.Tactics

module L = FStar.List.Tot

noextract
let conclude ()
: Tac unit
= // dump "conclude before";
  norm [delta; iota; primops];
  first [
    trefl;
    trivial;
  ];
//  dump "conclude after";
  qed ()

noextract
let solve_vc ()
: Tac unit
= exact_guard (quote ()); conclude ()

noextract
let rec app_head_rev_tail (t: term) :
  Tac (term * list argv)
=
  let ins = inspect t in
  if Tv_App? ins
  then
    let (Tv_App u v) = ins in
    let (x, l) = app_head_rev_tail u in
    (x, v :: l)
  else
    (t, [])

noextract
let app_head_tail (t: term) :
    Tac (term * list argv)
= let (x, l) = app_head_rev_tail t in
  (x, L.rev l)

noextract
let tassert (b: bool) : Tac (squash b) =
  if b
  then ()
  else
    let s = term_to_string (quote b) in
    fail ("Tactic assertion failed: " ^ s)

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

noextract
let rec to_all_goals (t: (unit -> Tac unit)) : Tac unit =
  if ngoals () = 0
  then ()
  else
    let _ = divide 1 t (fun () -> to_all_goals t) in ()

noextract
let rec intros_until_squash
  ()
: Tac binder
= let i = intro () in
  let (tm, _) = app_head_tail (cur_goal ()) in
  if tm `term_eq` (`squash)
  then i
  else intros_until_squash ()

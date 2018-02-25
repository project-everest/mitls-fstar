module LowParse.Math
include FStar.Math.Lemmas
open FStar.Mul

let mul_reg_r
  (a b x: int)
: Lemma
  (requires (
    x <> 0 /\
    a * x == b * x
  ))
  (ensures (a == b))
= ()

let mul_reg_l
  (x a b: int)
: Lemma
  (requires (
    x <> 0 /\
    x * a == x * b
  ))
  (ensures (a == b))
= ()

let lt_mul_add_reg_r
  (x y: nat)
  (s: pos)
: Lemma
  (requires (x * s < y * s + s))
  (ensures (x <= y))
= distributivity_add_left x (y + 1) s

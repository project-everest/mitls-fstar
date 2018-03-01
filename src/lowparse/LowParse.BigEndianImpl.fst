module LowParse.BigEndianImpl
include LowParse.BigEndian

module U = FStar.UInt
module U8 = FStar.UInt8

noeq
type uinttype (t: Type0) (n: nat) =
  | UIntType:
    (v: (t -> Tot (y: nat { U.fits y n } ))) ->
    (to_byte: ((x: t) -> Tot (y: U8.t { U8.v y == v x % 256 } ))) ->
    (from_byte: ((x: U8.t) -> Tot (y: t { v y == U8.v x } ))) ->
    (zero: t { v zero == 0 } ) ->
    (v_inj: ((x1: t) -> (x2: t) -> Lemma (requires (v x1 == v x2)) (ensures (x1 == x2)))) ->
    (add: ((x: t) -> (y: t) -> Pure t (requires (U.fits (v x + v y) n)) (ensures (fun z -> v z == v x + v y)))) ->
    (mul256: ((x: t) -> Pure t (requires (U.fits (Prims.op_Multiply (v x) 256) n)) (ensures (fun z -> v z == Prims.op_Multiply (v x) 256)))) ->
    (div256: ((x: t) -> Pure t (requires True) (ensures (fun z -> v z == v x / 256)))) ->
    uinttype t n

module Seq = FStar.Seq
module B32 = FStar.Bytes
module U32 = FStar.UInt32
module M = LowParse.Math
module G = FStar.Ghost

#reset-options "--z3rlimit 16"

inline_for_extraction
let be_to_n_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.bytes)
  (i: U32.t)
  (accu: t)
: Pure t
  (requires (
    0 < U32.v i /\
    U32.v i <= B32.length s /\
    Prims.op_Multiply 8 (B32.length s) <= n /\
    u.v accu == be_to_n (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i))
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (Seq.slice (B32.reveal s) 0 (B32.length s - (U32.v i - 1)))
  ))
= match u with
  | UIntType u_v _ u_from_byte _ _ u_add u_mul256 _ ->
  let sq = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i)) in
  let sq' = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - (U32.v i - 1))) in
  let b = B32.get s (U32.sub (B32.len s) i) in
  assert (b == Seq.last (G.reveal sq'));
  assert (Seq.slice (G.reveal sq') 0 (Seq.length (G.reveal sq') - 1) == G.reveal sq);
  lemma_be_to_n_is_bounded (G.reveal sq);
  M.pow2_plus (8 `Prims.op_Multiply` Seq.length (G.reveal sq)) 8;
  assert (u_v accu `Prims.op_Multiply` 256 < pow2 (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8));
  M.pow2_le_compat n (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8);
  assert (u_v accu `Prims.op_Multiply` 256 < pow2 n);
  let accu256 = u_mul256 accu in
  let accu' = u_add (u_from_byte b) accu256 in
  accu'

inline_for_extraction
let be_to_n_1
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 1)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res =
    be_to_n_body' t n u s 1ul u_zero
  in
  res

inline_for_extraction
let be_to_n_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 2)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res2 =
    be_to_n_body' t n u s 2ul u_zero
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 3)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res3 =
    be_to_n_body' t n u s 3ul u_zero
  in
  let res2 =
    be_to_n_body' t n u s 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1

inline_for_extraction
let be_to_n_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.lbytes 4)
: Pure t
  (requires (
    Prims.op_Multiply 8 (B32.length s) <= n
  ))
  (ensures (fun accu' ->
    u.v accu' == be_to_n (B32.reveal s)
  ))
= match u with
  | UIntType _ _ _ u_zero _ _ _ _ ->
  let res4 =
    be_to_n_body' t n u s 4ul u_zero
  in
  let res3 =
    be_to_n_body' t n u s 3ul res4
  in
  let res2 =
    be_to_n_body' t n u s 2ul res3
  in
  let res1 =
    be_to_n_body' t n u s 1ul res2
  in
  res1


inline_for_extraction
let n_to_be_body'
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
  (i: U32.t)
  (x: t)
  (accu: B32.bytes)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` B32.length accu <= n /\
    U32.v i <= B32.length accu /\
    0 < U32.v i /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` B32.length accu) /\
    u.v x < pow2 (8 `Prims.op_Multiply` U32.v i) /\
    n_to_be (B32.len accu) (u.v x0) == Seq.append (n_to_be i (u.v x)) (Seq.slice (B32.reveal accu) (U32.v i) (B32.length accu))
  ))
  (ensures (fun accu' ->
    B32.length accu' == B32.length accu /\ (
    let x' = u.div256 x in
    let i' = U32.sub i 1ul in
    u.v x' < pow2 (8 `Prims.op_Multiply` U32.v i') /\
    n_to_be (B32.len accu') (u.v x0) == Seq.append (n_to_be i' (u.v x')) (Seq.slice (B32.reveal accu') (U32.v i') (B32.length accu'))
  )))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let b = u_to_byte x in
  let i' = U32.sub i 1ul in
  let accu' = B32.set_byte accu i' b in
  M.pow2_plus 8 (8 `Prims.op_Multiply` U32.v i');
  let x' = G.hide (u_div256 x) in
  assert (u_v (G.reveal x') < pow2 (8 `Prims.op_Multiply` U32.v i'));
  assert (n_to_be i (u_v x) == Seq.append (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 b));
  assert (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu') == Seq.slice (B32.reveal accu) (U32.v i) (B32.length accu));
  assert (Seq.slice (B32.reveal accu') (U32.v i') (B32.length accu') `Seq.equal` Seq.append (Seq.create 1 b) (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu')));
  Seq.append_assoc (n_to_be i' (u_v (G.reveal x'))) (Seq.create 1 b) (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu'));
  accu'

inline_for_extraction
let n_to_be_1
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 1 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 1)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 1 /\
    n_to_be 1ul (u.v x0) == B32.reveal accu'
  ))
= let accu = B32.create 1ul 42uy in
  Seq.append_empty_r (n_to_be 1ul (u.v x0));
  let res = n_to_be_body' t n u x0 1ul x0 accu in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_2
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 2 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 2)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 2 /\
    n_to_be 2ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.create 2ul 42uy in
  Seq.append_empty_r (n_to_be 2ul (u.v x0));
  let accu1 = n_to_be_body' t n u x0 2ul x0 accu in
  let x1 = u_div256 x0 in
  let res = n_to_be_body' t n u x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_3
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 3 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 3)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 3 /\
    n_to_be 3ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.create 3ul 42uy in
  Seq.append_empty_r (n_to_be 3ul (u.v x0));
  let accu2 = n_to_be_body' t n u x0 3ul x0 accu in
  let x2 = u_div256 x0 in
  let accu1 = n_to_be_body' t n u x0 2ul x2 accu2 in
  let x1 = u_div256 x2 in
  let res = n_to_be_body' t n u x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res

inline_for_extraction
let n_to_be_4
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (x0: t)
: Pure B32.bytes
  (requires (
    8 `Prims.op_Multiply` 4 <= n /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` 4)
  ))
  (ensures (fun accu' ->
    B32.length accu' == 4 /\
    n_to_be 4ul (u.v x0) == B32.reveal accu'
  ))
= match u with
  | UIntType u_v u_to_byte _ _ _ _ _ u_div256 ->
  let accu = B32.create 4ul 42uy in
  Seq.append_empty_r (n_to_be 4ul (u.v x0));
  let accu3 = n_to_be_body' t n u x0 4ul x0 accu in
  let x3 = u_div256 x0 in
  let accu2 = n_to_be_body' t n u x0 3ul x3 accu3 in
  let x2 = u_div256 x3 in
  let accu1 = n_to_be_body' t n u x0 2ul x2 accu2 in
  let x1 = u_div256 x2 in
  let res = n_to_be_body' t n u x0 1ul x1 accu1 in
  Seq.append_empty_l (B32.reveal res);
  res


module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

inline_for_extraction
let u8 () : uinttype U8.t 8 =
  UIntType
    (fun x -> U8.v x)
    (fun x -> x)
    (fun x -> x)
    0uy
    (fun x y -> ())
    (fun x y -> U8.add x y)
    (fun x -> 0uy)
    (fun x -> 0uy)

inline_for_extraction
let u16 () : uinttype U16.t 16 =
  UIntType
    (fun x -> U16.v x)
    (fun x -> Cast.uint16_to_uint8 x)
    (fun x -> Cast.uint8_to_uint16 x)
    0us
    (fun x y -> ())
    (fun x y -> U16.add x y)
    (fun x -> U16.mul x 256us)
    (fun x -> U16.div x 256us)

inline_for_extraction
let u32 () : uinttype U32.t 32 =
  UIntType
    (fun x -> U32.v x)
    (fun x -> Cast.uint32_to_uint8 x)
    (fun x -> Cast.uint8_to_uint32 x)
    0ul
    (fun x y -> ())
    (fun x y -> U32.add x y)
    (fun x -> U32.mul x 256ul)
    (fun x -> U32.div x 256ul)

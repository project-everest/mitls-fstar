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
= let sq = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i)) in
  let sq' = G.hide (Seq.slice (B32.reveal s) 0 (B32.length s - (U32.v i - 1))) in
  let b = B32.get s (U32.sub (B32.len s) i) in
  assert (b == Seq.last (G.reveal sq'));
  assert (Seq.slice (G.reveal sq') 0 (Seq.length (G.reveal sq') - 1) == G.reveal sq);
  lemma_be_to_n_is_bounded (G.reveal sq);
  M.pow2_plus (8 `Prims.op_Multiply` Seq.length (G.reveal sq)) 8;
  assert (u.v accu `Prims.op_Multiply` 256 < pow2 (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8));
  M.pow2_le_compat n (8 `Prims.op_Multiply` Seq.length (G.reveal sq) + 8);
  assert (u.v accu `Prims.op_Multiply` 256 < pow2 n);
  let accu256 = u.mul256 accu in
  let accu' = u.add (u.from_byte b) accu256 in
  accu'

let be_to_n_inv
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.bytes)
  (continue: bool)
  (x: U32.t * t)
: GTot Type0
= let (i, accu) = x in
  U32.v i <= B32.length s /\
  8 `Prims.op_Multiply` B32.length s <= n /\
  u.v accu == be_to_n (Seq.slice (B32.reveal s) 0 (B32.length s - U32.v i)) /\
  (continue == false ==> U32.v i == 0)

let be_to_n_measure
  (t: Type0)
  (x: U32.t * t)
: GTot nat
= let (i, _) = x in
  U32.v i

inline_for_extraction
let be_to_n_body
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.bytes)
  (x: U32.t * t)
: Pure (bool * (U32.t * t))
  (requires (be_to_n_inv t n u s true x))
  (ensures (fun (continue, x') ->
    be_to_n_inv t n u s continue x' /\
    (continue == true ==>  be_to_n_measure t x' < be_to_n_measure t x)
  ))
= let (i, accu) = x in
  if i = 0ul
  then (false, x)
  else
    let accu' = be_to_n_body' t n u s i accu in
    let i' = U32.sub i 1ul in
    (true, (i', accu'))

module CL = C.Loops

inline_for_extraction
let be_to_n_impl 
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (s: B32.bytes)
: Pure t
  (requires (8 `Prims.op_Multiply` B32.length s <= n))
  (ensures (fun y -> u.v y == be_to_n (B32.reveal s)))
= let (_, res) =
    CL.total_while
      (be_to_n_measure t)
      (be_to_n_inv t n u s)
      (be_to_n_body t n u s)
      (B32.len s, u.zero)
  in
  res

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
= let b = u.to_byte x in
  let i' = U32.sub i 1ul in
  let accu' = B32.set_byte accu i' b in
  M.pow2_plus 8 (8 `Prims.op_Multiply` U32.v i');
  let x' = G.hide (u.div256 x) in
  assert (u.v (G.reveal x') < pow2 (8 `Prims.op_Multiply` U32.v i'));
  assert (n_to_be i (u.v x) == Seq.append (n_to_be i' (u.v (G.reveal x'))) (Seq.create 1 b));
  assert (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu') == Seq.slice (B32.reveal accu) (U32.v i) (B32.length accu));
  assert (Seq.slice (B32.reveal accu') (U32.v i') (B32.length accu') `Seq.equal` Seq.append (Seq.create 1 b) (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu')));
  Seq.append_assoc (n_to_be i' (u.v (G.reveal x'))) (Seq.create 1 b) (Seq.slice (B32.reveal accu') (U32.v i) (B32.length accu'));
  accu'

let n_to_be_inv
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (len: U32.t)
  (x0: t)
  (continue: bool)
  (y: U32.t * t * B32.bytes)
: GTot Type0
= let (i, x, accu) = y in
    U32.v len == B32.length accu /\
    8 `Prims.op_Multiply` B32.length accu <= n /\
    U32.v i <= B32.length accu /\
    u.v x0 < pow2 (8 `Prims.op_Multiply` B32.length accu) /\
    u.v x < pow2 (8 `Prims.op_Multiply` U32.v i) /\
    n_to_be (B32.len accu) (u.v x0) == Seq.append (n_to_be i (u.v x)) (Seq.slice (B32.reveal accu) (U32.v i) (B32.length accu)) /\
    (continue == false ==> U32.v i == 0)

let n_to_be_measure
  (t: Type0)
  (y: U32.t * t * B32.bytes)
: GTot nat
= let (i, _, _) = y in
  U32.v i

inline_for_extraction
let n_to_be_body
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (len: U32.t)
  (x0: t)
  (y: U32.t * t * B32.bytes)
: Pure (bool * (U32.t * t * B32.bytes))
  (requires (n_to_be_inv t n u len x0 true y))
  (ensures (fun (continue, y') ->
    n_to_be_inv t n u len x0 continue y' /\
    (continue == true ==> n_to_be_measure t y' < n_to_be_measure t y)
  ))
= let (i, x, accu) = y in
  if i = 0ul
  then (false, y)
  else
    let accu' = n_to_be_body' t n u x0 i x accu in
    let x' = u.div256 x in
    let i' = U32.sub i 1ul in
    (true, (i', x', accu'))

inline_for_extraction
let n_to_be_impl
  (t: Type0)
  (n: nat)
  (u: uinttype t n)
  (len: U32.t)
  (x0: t)
  (z: unit {
    u.v x0 < pow2 (8 `Prims.op_Multiply` U32.v len) /\
    8 `Prims.op_Multiply` U32.v len <= n
  } )
: Tot (y: B32.bytes { B32.reveal y == n_to_be len (u.v x0) } )
= let buf = B32.create len 42uy in
  Seq.append_empty_r (n_to_be len (u.v x0));
  let (_, _, res) =
    CL.total_while
      (n_to_be_measure t)
      (n_to_be_inv t n u len x0)
      (n_to_be_body t n u len x0)
      (len, x0, buf)
  in
  Seq.append_empty_l (B32.reveal res);
  res


module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

inline_for_extraction
let u8 : uinttype U8.t 8 =
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
let u16 : uinttype U16.t 16 =
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
let u32 : uinttype U32.t 32 =
  UIntType
    (fun x -> U32.v x)
    (fun x -> Cast.uint32_to_uint8 x)
    (fun x -> Cast.uint8_to_uint32 x)
    0ul
    (fun x y -> ())
    (fun x y -> U32.add x y)
    (fun x -> U32.mul x 256ul)
    (fun x -> U32.div x 256ul)

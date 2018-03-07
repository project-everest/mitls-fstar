module Parse

open FStar.Bytes
open FStar.Error

open TLSError

include Mem // temporary, for code opening only TLSConstants

(** Begin Module Format *)

// basic parsing and formatting---an attempt at splitting TLSConstant.

type pinverse_t (#a:Type) (#b:Type) ($f:(a -> Tot b)) = b -> Tot (result a)

unfold type lemma_inverse_g_f (#a:Type) (#b:Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (x:a) =
  g (f x) == Correct x

unfold type lemma_pinverse_f_g (#a:Type) (#b:Type) (r:b -> b -> Type) ($f:a -> Tot b) ($g:b -> Tot (result a)) (y:b) =
  Correct? (g y) ==> r (f (Correct?._0 (g y))) y


(** Transforms a sequence of natural numbers into bytes *)
val bytes_of_seq: n:nat{ repr_bytes n <= 8 } -> Tot (b:bytes{length b <= 8})
let bytes_of_seq sn = bytes_of_int 8 sn

(** Transforms bytes into a sequence of natural numbers *)
val seq_of_bytes: b:bytes{ length b <= 8 } -> Tot nat
let seq_of_bytes b = int_of_bytes b

(** Transform and concatenate a natural number to bytes *)
val vlbytes: 
  lSize:nat {lSize <= 3} -> 
  b:bytes{repr_bytes (length b) <= lSize} -> Tot (lbytes (lSize + length b))
let vlbytes lSize b = bytes_of_int lSize (Bytes.length b) @| b

// avoiding explicit applications of the representation lemmas
let vlbytes1 (b:bytes {length b < pow2 8}) = lemma_repr_bytes_values (length b); vlbytes 1 b
let vlbytes2 (b:bytes {length b < pow2 16}) = lemma_repr_bytes_values (length b); vlbytes 2 b

val vlbytes_trunc: 
  lSize:nat {lSize <= 3} -> b:bytes -> 
  extra:nat {repr_bytes (length b + extra) <= lSize} ->
  r: lbytes (lSize + length b)
let vlbytes_trunc lSize b extra =
  bytes_of_int lSize (length b + extra) @| b

let vlbytes_trunc_injective
  (lSize: nat {lSize <= 3})
  (b1: bytes)
  (extra1: nat {repr_bytes (length b1 + extra1) <= lSize} )
  (s1: bytes {UInt.size (lSize + length b1 + length s1) UInt32.n})
  (b2: bytes)
  (extra2: nat {repr_bytes (length b2 + extra2) <= lSize} )
  (s2: bytes {UInt.size (lSize + length b2 + length s2) UInt32.n})
: Lemma
  (requires (vlbytes_trunc lSize b1 extra1 @| s1 = vlbytes_trunc lSize b2 extra2 @| s2))
  (ensures (length b1 + extra1 == length b2 + extra2 /\ b1 @| s1 == b2 @| s2))
= admit()
  // let l1 = bytes_of_int lSize (length b1 + extra1) in
  // let l2 = bytes_of_int lSize (length b2 + extra2) in
  // append_assoc l1 b1 s1;
  // append_assoc l2 b2 s2;
  // lemma_append_inj l1 (b1 @| s1) l2 (b2 @| s2);
  // int_of_bytes_of_int lSize (length b1 + extra1);
  // int_of_bytes_of_int lSize (length b2 + extra2)

(** Lemmas associated to bytes manipulations *)
val lemma_vlbytes_len : lSize:nat {lSize <= 3} -> b:bytes{repr_bytes (length b) <= lSize}
  -> Lemma (ensures (length (vlbytes lSize b) = lSize + length b))
let lemma_vlbytes_len i b = ()

val lemma_vlbytes_inj_strong : i:nat {i <= 3}
  -> b:bytes {repr_bytes (length b) <= i}
  -> s:bytes {UInt.size (i + length b + length s) UInt32.n} 
  -> b':bytes {repr_bytes (length b') <= i}
  -> s':bytes {UInt.size (i + length b' + length s') UInt32.n} 
  -> Lemma (requires (vlbytes i b @| s = vlbytes i b' @| s'))
          (ensures (b == b' /\ s == s'))
let lemma_vlbytes_inj_strong i b s b' s' = admit()
  // let l = bytes_of_int i (length b) in
  // let l' = bytes_of_int i (length b') in
  // Seq.append_assoc l b s;
  // Seq.append_assoc l' b' s';
  // Seq.lemma_append_inj l (b @| s) l' (b' @| s');
  // int_of_bytes_of_int i (length b);
  // int_of_bytes_of_int i (length b');
  // Seq.lemma_append_inj b s b' s'

val lemma_vlbytes_inj : i:nat {i <= 3}
  -> b:bytes{repr_bytes (length b) <= i}
  -> b':bytes{repr_bytes (length b') <= i}
  -> Lemma (requires (vlbytes i b = vlbytes i b'))
          (ensures (b == b'))
let lemma_vlbytes_inj i b b' =
  lemma_vlbytes_inj_strong i b empty_bytes b' empty_bytes

val vlbytes_length_lemma: 
  n: nat {n <= 3} -> 
  a: bytes{repr_bytes (length a) <= n} -> 
  b: bytes{repr_bytes (length b) <= n} -> Lemma 
  (requires 
    slice (vlbytes n a) 0ul (UInt32.uint_to_t n) =  
    slice (vlbytes n b) 0ul (UInt32.uint_to_t n))
  (ensures length a = length b)
let vlbytes_length_lemma n a b = admit()
  // let lena = Seq.slice (vlbytes n a) 0 n in
  // let lenb = Seq.slice (vlbytes n b) 0 n in
  // assert(Seq.equal lena (bytes_of_int n (length a)));
  // assert(Seq.equal lenb (bytes_of_int n (length b)));
  // int_of_bytes_of_int n (length a); int_of_bytes_of_int n (length b)


#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length

val vlsplit: 
  lSize: nat {lSize <= 3} -> 
  vlb: bytes {lSize <= length vlb} -> 
  result (b:(bytes * bytes){
    let b0, b1 = b in 
    repr_bytes (length b0) <= lSize /\ 
    length vlb = lSize + length b0 + length b1 /\ 
    vlb = vlbytes lSize b0 @| b1
    })

//18-02-23 the three assumptions on Bytes should be (triggered) lemmas
let vlsplit lSize vlb =
  let vl,b = split vlb (UInt32.uint_to_t lSize) in
  assume(vlb = vl @| b); 
  let l = int_of_bytes vl in
  if l <= length b
  then 
    let b0, b1 = split b (UInt32.uint_to_t l) in 
    assume(b = b0 @| b1);
    assume(vl @| b0 @| b1 = (vl @| b0) @| b1);
    //assert(repr_bytes (length b0) <= lSize);
    //assert(length vlb = lSize + length b0 + length b1);
    //assert(vl @| b0 = vlbytes lSize b0);
    //assert(vlb = vl @| b0 @| b1);
    Correct(b0,b1)
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse: 
  lSize: nat {lSize <= 3} -> 
  vlb: bytes{lSize <= length vlb} -> 
  result (b:bytes{repr_bytes (length b) <= lSize /\ vlb = vlbytes lSize b})
let vlparse lSize vlb =
  assume false;//18-02-23 
  let vl,b = split_ vlb lSize in
  if int_of_bytes vl = length b
  then Correct b
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse_vlbytes: 
  lSize:nat{lSize <= 3} -> 
  vlb:bytes{repr_bytes (length vlb) <= lSize} -> Lemma
  (ensures vlparse lSize (vlbytes lSize vlb) == Correct vlb)
  [SMTPat (vlparse lSize (vlbytes lSize vlb))]
#reset-options "--initial_ifuel 2 --initial_fuel 2"
let vlparse_vlbytes lSize vlb =
  assume false; //18-02-23 
  let vl,b = split_ (vlbytes lSize vlb) lSize in
  assert (vl = bytes_of_int lSize (length vlb));
  int_of_bytes_of_int #lSize (length vlb);
  match vlparse lSize (vlbytes lSize vlb) with
  | Error z   -> ()
  | Correct b -> lemma_vlbytes_inj lSize vlb b

val uint16_of_bytes:
  b:bytes{length b == 2} ->
  n:UInt16.t{repr_bytes (UInt16.v n) <= 2 /\ bytes_of_int 2 (UInt16.v n) == b}

let uint16_of_bytes b =
  let n = int_of_bytes b in
  assert_norm (pow2 16 == 65536);
  lemma_repr_bytes_values n;
  int_of_bytes_of_int n;
  UInt16.uint_to_t n

val uint32_of_bytes:
  b:bytes{length b == 4} ->
  n:UInt32.t{repr_bytes (UInt32.v n) <= 4 /\ bytes_of_int 4 (UInt32.v n) == b}

let uint32_of_bytes b =
  let n = int_of_bytes b in
  assert_norm (pow2 32 == 4294967296);
  lemma_repr_bytes_values n;
  UInt32.uint_to_t n

let bytes_of_uint32 (n:UInt32.t) : Tot (lbytes 4) =
  let n = UInt32.v n in
  lemma_repr_bytes_values n;
  bytes_of_int 4 n

let bytes_of_uint16 (n:UInt16.t) : Tot (lbytes 2) =
  let n = UInt16.v n in
  lemma_repr_bytes_values n;
  bytes_of_int 2 n

// 18-02-26 to be inlined in the source
let cbyte (b:bytes{length b >= 1}) = b.[0ul]
let cbyte2 (b:bytes{length b >= 2}) = b.[0ul], b.[1ul]

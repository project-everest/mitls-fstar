module Parse

open FStar.Error
open TLSError
open Platform.Bytes

(** This file should be split in 3 different modules:
  - Regions: for global table regions (now in Mem)
  - Format: for generic formatting functions
  - DHFormat: for (EC)DHE-specific formatting (should go elsewhere)
*)

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
val vlbytes: lSize:nat -> b:bytes{repr_bytes (length b) <= lSize} -> Tot (r:bytes{length r = lSize + length b})
let vlbytes lSize b = bytes_of_int lSize (length b) @| b

// avoiding explicit applications of the representation lemmas
let vlbytes1 (b:bytes {length b < pow2 8}) = lemma_repr_bytes_values (length b); vlbytes 1 b
let vlbytes2 (b:bytes {length b < pow2 16}) = lemma_repr_bytes_values (length b); vlbytes 2 b

val vlbytes_trunc: lSize:nat -> b:bytes ->
  extra:nat{repr_bytes (length b + extra) <= lSize} ->
  r:bytes{length r == lSize + length b}
let vlbytes_trunc lSize b extra =
  bytes_of_int lSize (length b + extra) @| b

let vlbytes_trunc_injective
  (lSize: nat)
  (b1: bytes)
  (extra1: nat { repr_bytes (length b1 + extra1) <= lSize } )
  (s1: bytes)
  (b2: bytes)
  (extra2: nat { repr_bytes (length b2 + extra2) <= lSize } )
  (s2: bytes)
: Lemma
  (requires (Seq.equal (vlbytes_trunc lSize b1 extra1 @| s1) (vlbytes_trunc lSize b2 extra2 @| s2)))
  (ensures (length b1 + extra1 == length b2 + extra2 /\ b1 @| s1 == b2 @| s2))
= let l1 = bytes_of_int lSize (length b1 + extra1) in
  let l2 = bytes_of_int lSize (length b2 + extra2) in
  Seq.append_assoc l1 b1 s1;
  Seq.append_assoc l2 b2 s2;
  Seq.lemma_append_inj l1 (b1 @| s1) l2 (b2 @| s2);
  int_of_bytes_of_int lSize (length b1 + extra1);
  int_of_bytes_of_int lSize (length b2 + extra2)

(** Lemmas associated to bytes manipulations *)
val lemma_vlbytes_len : i:nat -> b:bytes{repr_bytes (length b) <= i}
  -> Lemma (ensures (length (vlbytes i b) = i + length b))
let lemma_vlbytes_len i b = ()

val lemma_vlbytes_inj_strong : i:nat
  -> b:bytes{repr_bytes (length b) <= i}
  -> s:bytes
  -> b':bytes{repr_bytes (length b') <= i}
  -> s':bytes
  -> Lemma (requires (Seq.equal (vlbytes i b @| s) (vlbytes i b' @| s')))
          (ensures (b == b' /\ s == s'))
let lemma_vlbytes_inj_strong i b s b' s' =
  let l = bytes_of_int i (length b) in
  let l' = bytes_of_int i (length b') in
  Seq.append_assoc l b s;
  Seq.append_assoc l' b' s';
  Seq.lemma_append_inj l (b @| s) l' (b' @| s');
  int_of_bytes_of_int i (length b);
  int_of_bytes_of_int i (length b');
  Seq.lemma_append_inj b s b' s'

val lemma_vlbytes_inj : i:nat
  -> b:bytes{repr_bytes (length b) <= i}
  -> b':bytes{repr_bytes (length b') <= i}
  -> Lemma (requires (Seq.equal (vlbytes i b) (vlbytes i b')))
          (ensures (b == b'))
let lemma_vlbytes_inj i b b' =
  lemma_vlbytes_inj_strong i b Seq.createEmpty b' Seq.createEmpty

val vlbytes_length_lemma: n:nat -> a:bytes{repr_bytes (length a) <= n} -> b:bytes{repr_bytes (length b) <= n} ->
  Lemma (requires (Seq.equal (Seq.slice (vlbytes n a) 0 n) (Seq.slice (vlbytes n b) 0 n)))
        (ensures (length a = length b))
let vlbytes_length_lemma n a b =
  let lena = Seq.slice (vlbytes n a) 0 n in
  let lenb = Seq.slice (vlbytes n b) 0 n in
  assert(Seq.equal lena (bytes_of_int n (length a)));
  assert(Seq.equal lenb (bytes_of_int n (length b)));
  int_of_bytes_of_int n (length a); int_of_bytes_of_int n (length b)


#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length

val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:(bytes * bytes){
                    repr_bytes (length (fst b)) <= lSize
                  /\ Seq.equal vlb (vlbytes lSize (fst b) @| (snd b))}))
let vlsplit lSize vlb =
  let (vl,b) = Platform.Bytes.split vlb lSize in
  let l = int_of_bytes vl in
  if l <= length b
  then Correct(Platform.Bytes.split b l)
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse: lSize:nat{lSize <= 4} -> vlb:bytes{lSize <= length vlb}
  -> Tot (result (b:bytes{repr_bytes (length b) <= lSize /\ Seq.equal vlb (vlbytes lSize b)}))
let vlparse lSize vlb =
  let vl,b = split vlb lSize in
  if int_of_bytes vl = length b
  then Correct b
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


val vlparse_vlbytes: lSize:nat{lSize <= 4} -> vlb:bytes{repr_bytes (length vlb) <= lSize} -> Lemma
  (requires (True))
  (ensures (vlparse lSize (vlbytes lSize vlb) == Correct vlb))
  [SMTPat (vlparse lSize (vlbytes lSize vlb))]
let vlparse_vlbytes lSize vlb =
  let vl,b = split (vlbytes lSize vlb) lSize in
  assert (Seq.equal vl (bytes_of_int lSize (length vlb)));
  int_of_bytes_of_int lSize (length vlb);
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
  int_of_bytes_of_int 2 n;
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

(** End Module Format *)

(*
(** to be replaced by flat enum from QD's NamedGroup and NameGroupList 
    (can we get a better name?)
*)

// floating crypto definitions; 
// these should come from the RFC, be hidden behind CommonDH.fsti

(** Finite Field Diffie-Hellman group definitions *)
type ffdhe =
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192
type unknownNG =
  u:(byte*byte){(let (b1,b2) = u in
    (b1 = 0x00z ==> b2 <> 0x17z /\ b2 <> 0x18z /\ b2 <> 0x19z
                 /\ b2 <> 0x1dz /\ b2 <> 0x1ez) /\
    (b1 = 0x01z ==> b2 <> 0x00z /\ b2 <> 0x01z /\ b2 <> 0x02z
                 /\ b2 <> 0x03z /\ b2 <> 0x04z))}
type namedGroup =
  | SEC of CoreCrypto.ec_curve
  | FFDHE of ffdhe
  | NG_UNKNOWN of unknownNG

type namedGroups = list namedGroup{List.Tot.length groups < 65536/2}
(** Formatting and parsing (EC)DHE named groups *)

val namedGroupBytes: namedGroup -> Tot (lbytes 2)
val parseNamedGroup: pinverse_t namedGroupBytes

(** Formatting and parsing lists of named groups *)
val namedGroupsBytes: groups:list namedGroup{List.Tot.length groups < 65536/2}
  -> Tot (b:bytes { length b = 2 + op_Multiply 2 (List.Tot.length groups)})
val parseNamedGroups: b:bytes { 2 <= length b /\ length b < 65538 }
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = (length b - 2) / 2}))

(*
 * We only seem to be using these two named groups
 * irrespective of whether it's TLS 12 or 13
 *)
type valid_namedGroup = x:namedGroup{SEC? x \/ FFDHE? x}
*)

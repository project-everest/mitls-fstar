module Parse

open FStar.Error
open TLSError
open FStar.Bytes


module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = FStar.Bytes

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
val bytes_of_seq: n:nat{B.repr_bytes n <= 8 } -> Tot (b:B.bytes{B.length b <= 8})
let bytes_of_seq sn = B.bytes_of_int 8 sn

(** Transforms bytes into a sequence of natural numbers *)
val seq_of_bytes: b:B.bytes{ B.length b <= 8 } -> Tot nat
let seq_of_bytes b = B.int_of_bytes b

(** Transform and concatenate a natural number to bytes *)
val vlbytes: lSize:nat -> b:B.bytes{B.repr_bytes (B.length b) <= lSize} -> Tot (r:B.bytes{B.length r = lSize + B.length b})
let vlbytes lSize b = B.bytes_of_int lSize (B.length b) @| b

// avoiding explicit applications of the representation lemmas
let vlbytes1 (b:B.bytes {B.length b < pow2 8}) = B.lemma_repr_bytes_values (B.length b); vlbytes 1 b
let vlbytes2 (b:B.bytes {B.length b < pow2 16}) = B.lemma_repr_bytes_values (B.length b); vlbytes 2 b

val vlbytes_trunc: lSize:nat -> b:B.bytes ->
  extra:nat{B.repr_bytes (B.length b + extra) <= lSize} ->
  r:B.bytes{B.length r == lSize + B.length b}
let vlbytes_trunc lSize b extra =
  B.bytes_of_int lSize (B.length b + extra) @| b

let vlbytes_trunc_injective
  (lSize: nat)
  (b1: B.bytes)
  (extra1: nat { B.repr_bytes (B.length b1 + extra1) <= lSize } )
  (s1: B.bytes)
  (b2: B.bytes)
  (extra2: nat { B.repr_bytes (B.length b2 + extra2) <= lSize } )
  (s2: B.bytes)
: Lemma
  (requires ((vlbytes_trunc lSize b1 extra1 @| s1) = (vlbytes_trunc lSize b2 extra2 @| s2)))
  (ensures (B.length b1 + extra1 == B.length b2 + extra2 /\ b1 @| s1 == b2 @| s2))
= admit()
  // let l1 = B.bytes_of_int lSize (B.length b1 + extra1) in
  // let l2 = B.bytes_of_int lSize (B.length b2 + extra2) in
  // B.append_assoc l1 b1 s1;
  // B.append_assoc l2 b2 s2;
  // B.lemma_append_inj l1 (b1 @| s1) l2 (b2 @| s2);
  // B.int_of_bytes_of_int lSize (B.length b1 + extra1);
  // B.int_of_bytes_of_int lSize (B.length b2 + extra2)

(** Lemmas associated to bytes manipulations *)
val lemma_vlbytes_len : i:nat -> b:B.bytes{B.repr_bytes (B.length b) <= i}
  -> Lemma (ensures (B.length (vlbytes i b) = i + B.length b))
let lemma_vlbytes_len i b = ()


val lemma_vlbytes_inj_strong : i:nat
  -> b:B.bytes{B.repr_bytes (B.length b) <= i}
  -> s:B.bytes
  -> b':B.bytes{B.repr_bytes (B.length b') <= i}
  -> s':B.bytes
  -> Lemma (requires ((vlbytes i b @| s) = (vlbytes i b' @| s')))
          (ensures (b == b' /\ s == s'))

let lemma_vlbytes_inj_strong i b s b' s' = admit()
  // let l = B.bytes_of_int i (B.length b) in
  // let l' = B.bytes_of_int i (B.length b') in
  // B.append_assoc l b s;
  // B.append_assoc l' b' s';
  // B.lemma_append_inj l (b @| s) l' (b' @| s');
  // B.int_of_bytes_of_int i (B.length b);
  // B.int_of_bytes_of_int i (B.length b');
  // B.lemma_append_inj b s b' s'

val lemma_vlbytes_inj : i:nat
  -> b:B.bytes{B.repr_bytes (B.length b) <= i}
  -> b':B.bytes{B.repr_bytes (B.length b') <= i}
  -> Lemma (requires ((vlbytes i b) = (vlbytes i b')))
          (ensures (b == b'))

let lemma_vlbytes_inj i b b' =
  lemma_vlbytes_inj_strong i b B.empty_bytes b' B.empty_bytes

val vlbytes_length_lemma: n:nat -> a:B.bytes{B.repr_bytes (B.length a) <= n} -> b:B.bytes{B.repr_bytes (B.length b) <= n} ->
  Lemma (requires ((B.slice (vlbytes n a) 0ul (FStar.UInt32.uint_to_t n)) = (B.slice (vlbytes n b) 0ul (FStar.UInt32.uint_to_t n))))
        (ensures (B.length a = B.length b))

let vlbytes_length_lemma n a b = admit()

#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 0 --initial_fuel 0"   //need to reason about length

val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:B.bytes{lSize <= B.length vlb}
  -> Tot (result (b:(B.bytes * B.bytes){
        B.repr_bytes (B.length (fst b)) <= lSize /\
        vlb == (vlbytes lSize (fst b) @| (snd b))}))

#set-options "--max_ifuel 2 --initial_ifuel 2"
let vlsplit lSize vlb =
  let (vl,b) = B.split vlb (FStar.UInt32.uint_to_t lSize) in
  let l = B.int_of_bytes vl in
  if l <= B.length b
  then begin
    let u, v = B.split b (FStar.UInt32.uint_to_t l) in
//    B.append_assoc vl u v; //TODO
    Correct (u,v)
   end
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse: lSize:nat{lSize <= 4} -> vlb:B.bytes{lSize <= B.length vlb}
  -> Pure (r:result B.bytes)
  (requires (True))
  (ensures fun r -> Correct? r ==>
    (let b = Correct?._0 r in B.repr_bytes (B.length b) <= lSize /\ vlb = (vlbytes lSize b)))

let vlparse lSize vlb =
  let vl,b = B.split vlb (FStar.UInt32.uint_to_t lSize) in
  if B.int_of_bytes vl = B.length b then Correct b
  else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val vlparse_vlbytes: lSize:nat{lSize <= 4} -> vlb:B.bytes{B.repr_bytes (B.length vlb) <= lSize} -> Lemma
  (requires (True))
  (ensures (vlparse lSize (vlbytes lSize vlb) == Correct vlb))
  [SMTPat (vlparse lSize (vlbytes lSize vlb))]

#reset-options "--initial_ifuel 2 --initial_fuel 2"
let vlparse_vlbytes lSize vlb =
  let b' = vlbytes lSize vlb in
  assert(b' = B.bytes_of_int lSize (B.length vlb) @| vlb);
  let vl, b = B.split b' (FStar.UInt32.uint_to_t lSize) in
//  B.lemma_append_inj vl b (B.bytes_of_int lSize (B.length vlb)) vlb; //TODO
  assert (vl = (B.bytes_of_int lSize (B.length vlb)));
//  B.int_of_bytes_of_int lSize (B.length vlb); //TODO
  let x = vlparse lSize b' in
  let b'' = Correct?._0 x in
  assert(x == vlparse lSize (vlbytes lSize vlb))

val uint16_of_bytes:
  b:B.bytes{B.length b == 2} ->
  n:UInt16.t{B.repr_bytes (UInt16.v n) <= 2 /\ B.bytes_of_int 2 (UInt16.v n) == b}

let uint16_of_bytes b =
  let n = B.int_of_bytes b in
  assert_norm (pow2 16 == 65536);
  B.lemma_repr_bytes_values n;
  // B.int_of_bytes_of_int 2 n; //TODO
  let r = UInt16.uint_to_t n in
  assert(UInt16.v r = n);
  assert(B.repr_bytes (UInt16.v r) <= 2);
  r

val uint32_of_bytes:
  b:B.bytes{B.length b == 4} ->
  n:UInt32.t{B.repr_bytes (UInt32.v n) <= 4 /\ B.bytes_of_int 4 (UInt32.v n) == b}

let uint32_of_bytes b =
  let n = B.int_of_bytes b in
  assert_norm (pow2 32 == 4294967296);
  B.lemma_repr_bytes_values n;
  UInt32.uint_to_t n

let bytes_of_uint32 (n:UInt32.t) : Tot (B.lbytes 4) =
  FStar.Bytes.bytes_of_int32 n

let bytes_of_uint16 (n:UInt16.t) : Tot (B.lbytes 2) =
  let n = UInt16.v n in
  B.lemma_repr_bytes_values n;
  B.bytes_of_int 2 n

(** End Module Format *)


(** Begin Module DHFormat *)

// floating crypto definitions

(** Finite Field Diffie-Hellman group definitions *)
type ffdhe =
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192

type unknownNG = u:(byte * byte){
    let b1, b2 = u in
    (b1 = 0z ==> b2 <> 0x17z /\ b2 <> 0x18z /\ b2 <> 0x19z
                 /\ b2 <> 0x1dz /\ b2 <> 0x1ez) /\
    (b1 = 1z ==> b2 <> 0x00z /\ b2 <> 0x01z /\ b2 <> 0x02z
                 /\ b2 <> 0x03z /\ b2 <> 0x04z)}

(** TLS 1.3 named groups for (EC)DHE key exchanges *)
type namedGroup =
  | SEC of CoreCrypto.ec_curve
  | FFDHE of ffdhe
  | NG_UNKNOWN of unknownNG

(*
 * We only seem to be using these two named groups
 * irrespective of whether it's TLS 12 or 13
 *)
type valid_namedGroup = x:namedGroup{SEC? x \/ FFDHE? x}

(** Serializing function for (EC)DHE named groups *)
val namedGroupBytes: namedGroup -> Tot (B.lbytes 2)
let namedGroupBytes ng =
  let open CoreCrypto in
  match ng with
  | SEC ec ->
    begin
    match ec with
    | ECC_P256		-> B.twobytes (0x00z, 0x17z)
    | ECC_P384		-> B.twobytes (0x00z, 0x18z)
    | ECC_P521		-> B.twobytes (0x00z, 0x19z)
    | ECC_X25519  -> B.twobytes (0x00z, 0x1dz)
    | ECC_X448    -> B.twobytes (0x00z, 0x1ez)
    end
  | FFDHE dhe ->
    begin
    match dhe with
    | FFDHE2048		-> B.twobytes (0x01z, 0x00z)
    | FFDHE3072		-> B.twobytes (0x01z, 0x01z)
    | FFDHE4096		-> B.twobytes (0x01z, 0x02z)
    | FFDHE6144		-> B.twobytes (0x01z, 0x03z)
    | FFDHE8192		-> B.twobytes (0x01z, 0x04z)
    end
  | NG_UNKNOWN u	-> B.twobytes u

(* TODO: move to FStar.Bytes *)
let twobytes_inj x1 x2 : Lemma
  (B.twobytes x1 == B.twobytes x2 ==> x1 == x2)
  [SMTPat (B.twobytes x1); SMTPat (B.twobytes x2)]
= let s1 = B.twobytes x1 in
  let s2 = B.twobytes x2 in
  assert (x1 == (s1.[0ul], s1.[1ul]));
  assert (x2 == (s2.[0ul], s2.[1ul]))

val namedGroupBytes_is_injective: ng1:namedGroup -> ng2:namedGroup ->
  Lemma (requires ((namedGroupBytes ng1) = (namedGroupBytes ng2)))
        (ensures (ng1 == ng2))
let namedGroupBytes_is_injective ng1 ng2 =
  admit()

let cbyte2 (b:bytes{length b = 2}) : byte * byte =
  b.[0ul], b.[1ul]

(** Parsing function for (EC)DHE named groups *)
val parseNamedGroup: pinverse_t namedGroupBytes
let parseNamedGroup b =
  let open CoreCrypto in
  let bb = cbyte2 b in
  match bb with
  | (0x00z, 0x17z) -> Correct (SEC ECC_P256)
  | (0x00z, 0x18z) -> Correct (SEC ECC_P384)
  | (0x00z, 0x19z) -> Correct (SEC ECC_P521)
  | (0x00z, 0x1dz) -> Correct (SEC ECC_X25519)
  | (0x00z, 0x1ez) -> Correct (SEC ECC_X448)
  | (0x01z, 0x00z) -> Correct (FFDHE FFDHE2048)
  | (0x01z, 0x01z) -> Correct (FFDHE FFDHE3072)
  | (0x01z, 0x02z) -> Correct (FFDHE FFDHE4096)
  | (0x01z, 0x03z) -> Correct (FFDHE FFDHE6144)
  | (0x01z, 0x04z) -> Correct (FFDHE FFDHE8192)
  | _ -> Correct (NG_UNKNOWN bb)


(** Lemmas for named groups parsing/serializing inversions *)
#set-options "--max_ifuel 10 --max_fuel 10"
val inverse_namedGroup: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f namedGroupBytes parseNamedGroup x)
  [SMTPat (parseNamedGroup (namedGroupBytes x))]
let inverse_namedGroup x = ()

val pinverse_namedGroup: x:_ -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g Prims.eq2 namedGroupBytes parseNamedGroup x))
  [SMTPat (namedGroupBytes (Correct?._0 (parseNamedGroup x)))]
let pinverse_namedGroup x = ()

#set-options "--initial_fuel 2 --initial_ifuel 2"
private let lemma_namedGroupBytes_injective (ng1:namedGroup) (ng2:namedGroup)
  : Lemma (requires (namedGroupBytes ng1 = namedGroupBytes ng2))
          (ensures (ng1 = ng2))
  =
  let open CoreCrypto in
  let nb1 = namedGroupBytes ng1 in
  let nb2 = namedGroupBytes ng2 in
  match ng1, ng2 with
  | SEC ec1, SEC ec2 ->
    if ec1 = ec2 then ()
    else assert(nb1.[0ul] = 0x00z /\ nb2.[0ul] = 0x00z)
  | FFDHE dhe1, FFDHE dhe2 ->
    if dhe1 = dhe2 then ()
    else assert(nb1.[0ul] = 0x01z /\ nb2.[0ul] = 0x01z)
  | NG_UNKNOWN u1, NG_UNKNOWN u2 ->
    twobytes_inj u1 u2
  | _ -> assert(nb1.[0ul] = nb2.[0ul] /\ nb1.[1ul] = nb2.[1ul])
#reset-options

#set-options "--max_ifuel 2 --max_fuel 2"
private val namedGroupsBytes0: groups:list namedGroup
  -> Tot (b:B.bytes { B.length b == op_Multiply 2 (List.Tot.length groups)})
let rec namedGroupsBytes0 groups =
  match groups with
  | [] -> B.empty_bytes
  | g::gs ->
    // B.lemma_len_append (namedGroupBytes g) (namedGroupsBytes0 gs); // TODO should be unnecessary
    namedGroupBytes g @| namedGroupsBytes0 gs
#reset-options

#set-options "--initial_fuel 2 --initial_ifuel 2"
private
let rec namedGroupsBytes0_is_injective
  (groups1 groups2: list namedGroup)
: Lemma
  (requires ((namedGroupsBytes0 groups1) = (namedGroupsBytes0 groups2)))
  (ensures (groups1 == groups2))
= match groups1, groups2 with
  | [], [] -> ()
  | g1::groups1', g2::groups2' ->
    assert((namedGroupBytes g1) @| (namedGroupsBytes0 groups1') = (namedGroupBytes g2) @| (namedGroupsBytes0 groups2'));
    //B.lemma_append_inj (namedGroupBytes g1) (namedGroupsBytes0 groups1') (namedGroupBytes g2) (namedGroupsBytes0 groups2'); //TODO
    lemma_namedGroupBytes_injective g1 g2;
    namedGroupsBytes0_is_injective groups1' groups2'

(** Serialization function for a list of named groups *)
val namedGroupsBytes: groups:list namedGroup{List.Tot.length groups < 65536/2}
  -> Tot (b:B.bytes { B.length b = 2 + op_Multiply 2 (List.Tot.length groups)})

let namedGroupsBytes groups =
  let gs = namedGroupsBytes0 groups in
  B.lemma_repr_bytes_values (B.length gs);
  vlbytes 2 gs

let namedGroupsBytes_is_injective
  (groups1: list namedGroup { List.Tot.length groups1 < 65536/2 } )
  (s1: B.bytes)
  (groups2: list namedGroup { List.Tot.length groups2 < 65536/2 } )
  (s2: B.bytes)
: Lemma
  (requires ((namedGroupsBytes groups1 @| s1) == (namedGroupsBytes groups2 @| s2)))
  (ensures (groups1 == groups2 /\ s1 == s2))
= let gs1 = namedGroupsBytes0 groups1 in
  B.lemma_repr_bytes_values (B.length gs1);
  let gs2 = namedGroupsBytes0 groups2 in
  B.lemma_repr_bytes_values (B.length gs2);
  lemma_vlbytes_inj_strong 2 gs1 s1 gs2 s2;
  namedGroupsBytes0_is_injective groups1 groups2

private val parseNamedGroups0: b:B.bytes -> l:list namedGroup
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = List.Tot.length l + B.length b / 2}))
  (decreases (B.length b))
let rec parseNamedGroups0 b groups =
  if B.length b > 0 then
    if B.length b >= 2 then
      let (ng, bytes) = B.split b 2ul in
      //B.lemma_split b 2; //TODO
      match parseNamedGroup ng with
      |Correct ng ->
        let groups' = ng :: groups in
        parseNamedGroups0 bytes groups'
      | Error z    -> Error z
    else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  else
   let grev = List.Tot.rev groups in
   assume (List.Tot.length grev == List.Tot.length groups);
   Correct grev

(** Parsing function for a list of named groups *)
val parseNamedGroups: b:B.bytes { 2 <= B.length b /\ B.length b < 65538 }
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = (B.length b - 2) / 2}))

let parseNamedGroups b =
  match vlparse 2 b with
  | Correct b' -> parseNamedGroups0 b' []
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse named groups")

(* End Module DHFormat *)

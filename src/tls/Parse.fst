module Parse

open FStar.All

open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError

module HH = FStar.HyperHeap
module HS = FStar.HyperStack


(** This file should be split in 3 different modules:
  - Regions: for global table regions
  - Format: for generic formatting functions
  - DHFormat: for (EC)DHE-specific formatting
*)


(** Begin Module Regions *)

//type fresh_subregion r0 r h0 h1 = ST.stronger_fresh_region r h0 h1 /\ ST.extends r r0

(** Regions and colors for objects in memory *)
let tls_color = -1
let epoch_color = 1
let hs_color = 2

let is_tls_rgn r   = HH.color r = tls_color
let is_epoch_rgn r = HH.color r = epoch_color
let is_hs_rgn r    = HH.color r = hs_color

(*
 * AR: Adding the eternal region predicate.
 * Strengthening the predicate because at some places, the code uses HH.parent.
 *)
let rgn       = r:HH.rid{r<>HH.root
                         /\ (forall (s:HH.rid).{:pattern HS.is_eternal_region s} HS.is_above s r ==> HS.is_eternal_region s)}
let tls_rgn   = r:rgn{is_tls_rgn r}
let epoch_rgn = r:rgn{is_epoch_rgn r}
let hs_rgn    = r:rgn{is_hs_rgn r}

let tls_region : tls_rgn = new_colored_region HH.root tls_color

let tls_tables_region : (r:tls_rgn{HH.parent r = tls_region}) =
    new_region tls_region


(** End Module Regions *)


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

(** Lemmas associated to bytes manipulations *)
val lemma_vlbytes_len : i:nat -> b:bytes{repr_bytes (length b) <= i}
  -> Lemma (ensures (length (vlbytes i b) = i + length b))
let lemma_vlbytes_len i b = ()

val lemma_vlbytes_inj : i:nat
  -> b:bytes{repr_bytes (length b) <= i}
  -> b':bytes{repr_bytes (length b') <= i}
  -> Lemma (requires (Seq.equal (vlbytes i b) (vlbytes i b')))
          (ensures (b == b'))
let lemma_vlbytes_inj i b b' =
  let l = bytes_of_int i (length b) in
  Seq.lemma_append_inj l b l b'

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

let z3kill = 0xFFz
(** TLS 1.3 named groups for (EC)DHE key exchanges *)
type namedGroup =
  | SEC of CoreCrypto.ec_curve
  | EC_UNSUPPORTED of (b:byte{b <> 0x17z /\ b <> 0x18z /\ b <> 0x19z})
  | FFDHE of ffdhe
  | FFDHE_PRIVATE_USE of (b:byte{b = 0xFCz \/ b = 0xFDz \/ b = 0xFEz \/ b = z3kill})
  | ECDHE_PRIVATE_USE of byte

(*
 * We only seem to be using these two named groups
 * irrespective of whether it's TLS 12 or 13
 *)
type valid_namedGroup = x:namedGroup{SEC? x \/ FFDHE? x}

(** Serializing function for (EC)DHE named groups *)
val namedGroupBytes: namedGroup -> Tot (lbytes 2)
let namedGroupBytes ng =
  let open CoreCrypto in
  match ng with
  | SEC ec ->
    begin
    match ec with
    | ECC_P256		-> abyte2 (0x00z, 0x17z)
    | ECC_P384		-> abyte2 (0x00z, 0x18z)
    | ECC_P521		-> abyte2 (0x00z, 0x19z)
    end
  | EC_UNSUPPORTED b	-> abyte2 (0x00z, b)
  | FFDHE dhe ->
    begin
    match dhe with
    | FFDHE2048		-> abyte2 (0x01z, 0x00z)
    | FFDHE3072		-> abyte2 (0x01z, 0x01z)
    | FFDHE4096		-> abyte2 (0x01z, 0x02z)
    | FFDHE6144		-> abyte2 (0x01z, 0x03z)
    | FFDHE8192		-> abyte2 (0x01z, 0x04z)
    end
  | FFDHE_PRIVATE_USE b -> abyte2 (0x01z, b)
  | ECDHE_PRIVATE_USE b -> abyte2 (0xFEz, b)

(** Parsing function for (EC)DHE named groups *)
val parseNamedGroup: pinverse_t namedGroupBytes
let parseNamedGroup b =
  let open CoreCrypto in
  match cbyte2 b with
  | (0x00z, 0x17z) -> Correct (SEC ECC_P256)
  | (0x00z, 0x18z) -> Correct (SEC ECC_P384)
  | (0x00z, 0x19z) -> Correct (SEC ECC_P521)
  | (0x00z, b)     -> Correct (EC_UNSUPPORTED b) // REMARK: only values 0x01z-0x16z and 0x1Az-0x1Ez are assigned
  | (0x01z, 0x00z) -> Correct (FFDHE FFDHE2048)
  | (0x01z, 0x01z) -> Correct (FFDHE FFDHE3072)
  | (0x01z, 0x02z) -> Correct (FFDHE FFDHE4096)
  | (0x01z, 0x03z) -> Correct (FFDHE FFDHE6144)
  | (0x01z, 0x04z) -> Correct (FFDHE FFDHE8192)
  | (0x01z, b)     ->
    if b = 0xFCz || b = 0xFDz || b = 0xFEz || b = 0xFFz
    then Correct (FFDHE_PRIVATE_USE b)
    else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong ffdhe private use group")
  | (0xFEz, b)     -> Correct (ECDHE_PRIVATE_USE b)
  | _ -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong named group")

(** Lemmas for named groups parsing/serializing inversions *)
val inverse_namedGroup: x:_ -> Lemma
  (requires (True))
  (ensures lemma_inverse_g_f namedGroupBytes parseNamedGroup x)
  [SMTPat (parseNamedGroup (namedGroupBytes x))]
let inverse_namedGroup x = ()

val pinverse_namedGroup: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal namedGroupBytes parseNamedGroup x))
  [SMTPat (namedGroupBytes (Correct?._0 (parseNamedGroup x)))]
let pinverse_namedGroup x = ()

#set-options "--max_ifuel 2 --max_fuel 2"
private val namedGroupsBytes0: groups:list namedGroup
  -> Tot (b:bytes { length b == op_Multiply 2 (List.Tot.length groups)})
let rec namedGroupsBytes0 groups =
  match groups with
  | [] -> empty_bytes
  | g::gs ->
    lemma_len_append (namedGroupBytes g) (namedGroupsBytes0 gs);
    namedGroupBytes g @| namedGroupsBytes0 gs
#reset-options

(** Serialization function for a list of named groups *)
val namedGroupsBytes: groups:list namedGroup{List.Tot.length groups < 65536/2}
  -> Tot (b:bytes { length b = 2 + op_Multiply 2 (List.Tot.length groups)})
let namedGroupsBytes groups =
  let gs = namedGroupsBytes0 groups in
  lemma_repr_bytes_values (length gs);
  vlbytes 2 gs

private val parseNamedGroups0: b:bytes -> l:list namedGroup
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = List.Tot.length l + length b / 2}))
  (decreases (length b))
let rec parseNamedGroups0 b groups =
  if length b > 0 then
    if length b >= 2 then
      let (ng, bytes) = split b 2 in
      lemma_split b 2;
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
val parseNamedGroups: b:bytes { 2 <= length b /\ length b < 65538 }
  -> Tot (result (groups:list namedGroup{List.Tot.length groups = (length b - 2) / 2}))
let parseNamedGroups b =
  match vlparse 2 b with
  | Correct b -> parseNamedGroups0 b []
  | Error z   ->
    Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse named groups")

(* End Module DHFormat *)

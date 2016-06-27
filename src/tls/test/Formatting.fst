module Formatting

open FStar.String
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes

type message = bytes

(*-------------------------------------------------------------------*)
(* From string to bytestring and back *)

(*
(* this spec is accurate for ASCII strings *)
val utf8: s:string -> Tot (b:bytes{length b <= strlen s})
let utf8 s = magic()
*)

// utf8 function is assumed in Platform.Bytes
assume val utf8_inj: s0:string -> s1:string -> Lemma
  (requires equal (utf8 s0) (utf8 s1))
  (ensures  s0 = s1)
  [SMTPat (utf8 s0); SMTPat (utf8 s1)]

type uint16 = i:int{0 <= i /\ i < 65536}

val uint16_to_bytes: u:uint16 -> Tot (lbytes 2)
let uint16_to_bytes u =
  lemma_repr_bytes_values u;
  bytes_of_int 2 u

val uint16_inj: s0:uint16 -> s1:uint16 -> Lemma
  (requires equal (uint16_to_bytes s0) (uint16_to_bytes s1))
  (ensures  s0 = s1)
  [SMTPat (uint16_to_bytes s0); SMTPat (uint16_to_bytes s1)]
let uint16_inj s0 s1 =
  lemma_repr_bytes_values s0;
  lemma_repr_bytes_values s1;
  int_of_bytes_of_int 2 s0;
  int_of_bytes_of_int 2 s1

type string16 = s:string{length (utf8 s) < 65536}


(*-------------------------------------------------------------------*)
(* Format for RPC requests and responses *)

val request : string -> Tot message
val response: string16 -> string -> Tot message

let tag0 = createBytes 1 0x00z
let tag1 = createBytes 1 0x01z

let request s = tag0 @| utf8 s

let response s t =
  lemma_repr_bytes_values (length (utf8 s));
  let lb = uint16_to_bytes (length (utf8 s)) in
  tag1 @| (lb @| ( (utf8 s) @| (utf8 t)))


(*-------------------------------------------------------------------*)
(* Lemmas on message formats:
   - requests are injective on their argument
   - responses are injective on both their arguments
   - requests and responses are distinct

   Note that we do not export a "spec" of the request and response
   functions---they just return messages---so these three lemmas are
   sufficient
*)

val append_inj_lemma: s1:bytes -> s2:bytes -> t1:bytes -> t2:bytes -> Lemma
  (requires length s1 = length t1 /\ equal (s1 @| s2) (t1 @| t2))
  (ensures  equal s1 t1 /\ equal s2 t2)
  [SMTPat (s1 @| s2); SMTPat (t1 @| t2)]
let rec append_inj_lemma s1 s2 t1 t2 =
  lemma_append_inj s1 s2 t1 t2

val req_resp_distinct: s1:string -> s2:string16 -> t:string -> Lemma
  (requires True)
  (ensures  request s1 <> response s2 t)
  [SMTPat (request s1); SMTPat (response s2 t)]
let req_resp_distinct s1 s2 t =
  assert (index (request s1) 0 = 0x00z);
  assert (index (response s2 t) 0 = 0x01z)

val req_components_corr: s1:string -> s2:string -> Lemma
  (requires equal (request s1) (request s2))
  (ensures  s1 = s2)
  [SMTPat (request s1); SMTPat (request s2)]
let req_components_corr s1 s2 =
  lemma_append_inj tag0 (utf8 s1) tag0 (utf8 s2);
  utf8_inj s1 s2

val resp_components_corr: s1:string16 -> t1:string -> s2:string16 -> t2:string -> Lemma
  (requires equal (response s1 t1) (response s2 t2))
  (ensures  s1 = s2 /\ t1 = t2)
  [SMTPat (response s1 t1); SMTPat (response s2 t2)]
let resp_components_corr s1 t1 s2 t2 = ()

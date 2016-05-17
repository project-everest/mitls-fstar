module StreamPlain

open FStar.Seq
open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range
open Content

// Defines an abstract "plain i len" plaintext interface from the more
// concrete & TLS-specific type "Content.fragment i"; 
// "len" is the (public) length after CTing and padding.

// This module is used only for TLS 1.3.

type id = i:id { pv_of_id i = TLS_1p3 }  


(*** plain := fragment | CT | 0*  ***)

// naming: we switch from fragment to plain as we are no longer TLS-specific
// similarly, the length accounts for the TLS-specific CT byte.
// internally, we know len > 0

let plainLength (l:int) = 1 <= l /\ l <= max_TLSCiphertext_fragment_length_13
type plainLen = l:nat { plainLength l }
type plainRepr = b:bytes { plainLength (length b) }

type plain (i:id) (len:plainLen) = f:fragment i { len >= snd (Content.rg i f) + 1 }

let pad payload ct (len:plainLen { length payload < len }): plainRepr = 
  payload @| ctBytes ct @| createBytes (len - length payload - 1) 0z

val ghost_repr: #i:id -> #len: plainLen -> f:plain i len -> GTot (bs:lbytes len)
let ghost_repr #i #len f = 
  let ct,_ = ct_rg i f in 
  let payload = Content.ghost_repr #i f in 
  pad payload ct len

// slight code duplication between monads; avoidable? 
val repr: i:id{ ~(safeId i)} -> len: plainLen -> p:plain i len -> Tot (b:lbytes len {b = ghost_repr #i #len p})
let repr i len f = 
  let ct,_ = ct_rg i f in 
  let payload = Content.repr i f in 
  pad payload ct len


// Implementations MUST NOT send zero-length fragments of Handshake,
// Alert, or ChangeCipherSpec content types. Zero-length fragments of
// Application data MAY be sent as they are potentially useful as a
// traffic analysis countermeasure.

val scan: i:id { ~ (authId i) } -> bs:plainRepr -> 
  j:nat { j < length bs /\ 
         (forall (k:nat {j < k /\ k < length bs}).{:pattern (Seq.index bs k)} Seq.index bs k = 0z) } -> 
  Tot (result (p:plain i (length bs) { bs = ghost_repr #i #(length bs) p }))
let rec scan i bs j =
  let len = length bs in 
  match index bs j with
  | 0z ->
    if j > 0 then scan i bs (j-1)
    else Error (AD_decode_error, "No ContentType byte")
  | 21z ->
    if j = 0 then Error (AD_decode_error, "Empty Alert fragment")
    else
      if j > max_TLSPlaintext_fragment_length then
	Error (AD_record_overflow, "TLSPlaintext fragment exceeds maximum length")
      else
	let rg:frange i = (0, j) in
	let payload, _ = Platform.Bytes.split bs j in
	let f = CT_Alert rg payload in
        lemma_eq_intro bs (pad payload Alert len);
        Correct f
  | 22z ->
    if j = 0 then Error (AD_decode_error, "Empty Handshake fragment")
    else
      if j > max_TLSPlaintext_fragment_length then
	Error (AD_record_overflow, "TLSPlaintext fragment exceeds maximum length")
      else
	let rg:frange i = (0, j) in
	let payload, _ = Platform.Bytes.split bs j in
	let f = CT_Handshake rg payload in
        lemma_eq_intro bs (pad payload Handshake len);
        Correct f
  | 23z -> 
    if j > max_TLSPlaintext_fragment_length then
      Error (AD_record_overflow, "TLSPlaintext fragment exceeds maximum length")
    else
      let rg:frange i = (0, j) in
      let payload, _ = Platform.Bytes.split bs j in
      let d = DataStream.mk_fragment #i rg payload in // REMARK: No-op
      let f = CT_Data rg d in
      lemma_eq_intro bs (pad payload Application_data len);
      Correct f
  | _    -> Error (AD_decode_error, "") 

type goodrepr i = bs: plainRepr {is_Correct (scan i bs (length bs - 1)) }

val mk_plain: i:id{ ~(authId i)} -> l:plainLen -> pr:lbytes l -> Tot (option (p:plain i l {pr = ghost_repr #i #l p}))
let mk_plain i l pr = 
  match scan i pr (length pr - 1) with 
  | Correct p -> Some p
  | Error _ -> None

(* OLD VERSION, breaking abstraction:
let mk_plain i l pr =
  let len = (length pr) - 1 in
  let (p,ctb) = Platform.Bytes.split pr len in
  match Content.parseCT ctb with
  | Correct ct -> Some (Content.mk_fragment i ct (0,len) p)
  | Error z -> None
*)

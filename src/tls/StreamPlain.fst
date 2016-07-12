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

type id = i:id { is_ID13 i }  


(*** plain := fragment | CT | 0*  ***)

// naming: we switch from fragment to plain as we are no longer TLS-specific
// similarly, the length accounts for the TLS-specific CT byte.
// internally, we know len > 0

let plainLength (l:int) = 1 <= l /\ l <= max_TLSCiphertext_fragment_length_13
type plainLen = l:int { plainLength l }
type plainRepr = b:bytes { plainLength (length b) }

type plain (i:id) (len:plainLen) = f:fragment i { len = snd (Content.rg i f) + 1 }

let pad payload ct (len:plainLen { length payload < len /\ length payload <= max_TLSPlaintext_fragment_length }): plainRepr = 
  payload @| ctBytes ct @| createBytes (len - length payload - 1) 0z

(*
val pad_zeros: payload:bytes 
  -> ct:contentType
  -> len:plainLen { length payload < len /\ len < max_TLSPlaintext_fragment_length }
  -> j:plainLen {length payload < j /\ j < len}
  -> Lemma (j < length (pad payload ct len) /\ 
           (forall (k:nat {j < k /\ k < len}).{:pattern (Seq.index (pad payload ct len) k)} Seq.index (pad payload ct len) k = 0z))
let pad_zeros payload ct len len' = ()
*)

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

private inline let min (a:nat) (b:nat): nat = if a < b then a else b

// Implementations MUST NOT send zero-length fragments of Handshake,
// Alert, or ChangeCipherSpec content types. Zero-length fragments of
// Application data MAY be sent as they are potentially useful as a
// traffic analysis countermeasure.

// Note that zero-padding can go past max_TLSPlaintext_fragment_length.
// This function scans from right to left the AE-decrypted plaintext to strip 
// the padding and compute a value of type `plain` with a public range.
// The representation of the result is the original
// AE-decrypted plaintext truncated to max_TLSPlaintext_fragment_length + 1.
val scan: i:id { ~ (authId i) } -> bs:plainRepr -> 
  j:nat { j < length bs 
	/\ (forall (k:nat {j < k /\ k < length bs}).{:pattern (Seq.index bs k)} Seq.index bs k = 0z) } ->
  Tot (let len = min (length bs) (max_TLSPlaintext_fragment_length + 1) in
       let bs' = fst (split bs len) in
       result (p:plain i len{ bs' = ghost_repr #i #len p }))
let rec scan i bs j =
  let len = min (length bs) (max_TLSPlaintext_fragment_length + 1) in
  let bs' = fst (split bs len) in
  match index bs j with
  | 0z ->
    if j > 0 then scan i bs (j - 1)
    else Error (AD_decode_error, "No ContentType byte")
  | 20z ->
    begin
    match j with
    | 0 -> Error (AD_decode_error, "Empty ChangeCipherSpec fragment")
    | 1 ->
      let payload, _ = split bs j in
      let rg = (1, len - 1) in
      if payload = ccsBytes then
	begin
	let f = CT_CCS #i rg in
	lemma_eq_intro bs' (pad ccsBytes Change_cipher_spec len);
        Correct f
	end
      else
	Error (AD_decode_error, "Malformed ChangeCipherSpec fragment")
    | _ -> Error (AD_decode_error, "Malformed ChangeCipherSpec fragment")
    end
  | 21z ->
    begin
    match j with
    | 0 -> Error (AD_decode_error, "Empty Alert fragment")
    | 1 -> Error (AD_decode_error, "Fragmented Alert")
    | 2 ->
      let payload, _ = split bs j in
      let rg = (2, len - 1) in
      begin
      match Alert.parse payload with
      | Correct ad ->
	let f = CT_Alert #i rg ad in
        lemma_eq_intro bs' (pad (Alert.alertBytes ad) Alert len);
        Correct f
      | Error e -> Error e
      end
    | _ -> Error (AD_decode_error, "Malformed Alert fragment")
    end
  | 22z ->
    if j = 0 then Error (AD_decode_error, "Empty Handshake fragment")
    else
      if j > max_TLSPlaintext_fragment_length then
	Error (AD_record_overflow, "TLSPlaintext fragment exceeds maximum length")
      else
	let payload, _ = split bs j in
	let rg = (1, len - 1) in
	let f = CT_Handshake rg payload in
	lemma_eq_intro bs' (pad payload Handshake len);
        Correct f
  | 23z -> 
    if j > max_TLSPlaintext_fragment_length then
      Error (AD_record_overflow, "TLSPlaintext fragment exceeds maximum length")
    else
      let payload, _ = split bs j in
      let rg = (0, len - 1) in
      let d = DataStream.mk_fragment #i rg payload in // REMARK: No-op
      let f = CT_Data rg d in
      lemma_eq_intro bs' (pad payload Application_data len);
      Correct f
  | _   -> Error (AD_decode_error, "Unknown ContentType")


val scan_pad_correct: i:id {~ (authId i)} -> payload:bytes -> ct:contentType
  -> len:plainLen { length payload < len /\ length payload <= max_TLSPlaintext_fragment_length }
  -> j:nat {length payload <= j /\ j < len}
  -> Lemma (requires (  (ct = Handshake ==> 0 < length payload)
		     /\ (ct = Change_cipher_spec ==> payload = ccsBytes)
		     /\ (ct = Alert ==>
		        length payload = 2 /\ is_Correct (Alert.parse payload))))
	  (ensures is_Correct (scan i (pad payload ct len) j) )

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

let rec scan_pad_correct i payload ct len j =
  let bs = pad payload ct len in
  if j = length payload then
    begin
    cut (abyte (index bs j) = ctBytes ct);
    lemma_split bs j;
    lemma_eq_intro payload (fst (split bs j));
    match index bs j with
    | 20z -> cut (j = 1)
    | 21z -> cut (j = 2)
    | 22z -> ()
    | 23z -> ()
    | _ -> ()
    end
  else
    scan_pad_correct i payload ct len (j - 1)

#reset-options

val inverse_scan: i:id{~(authId i)} -> len:plainLen -> f:plain i len ->
  Lemma (requires (let ct,_ = ct_rg i f in
		   let payload = Content.ghost_repr #i f in
		     (ct = Handshake ==> 0 < length payload)
		   /\ (ct = Change_cipher_spec ==> payload = ccsBytes)
		   /\ (ct = Alert ==>
		      length payload = 2 /\ is_Correct (Alert.parse payload))) )
	(ensures is_Correct (scan i (ghost_repr #i #len f) (len - 1)) )
let inverse_scan i len f =
  let ct,_ = ct_rg i f in 
  let payload = Content.ghost_repr #i f in
  scan_pad_correct i payload ct len (len - 1)

type goodrepr i = bs:plainRepr { is_Correct (scan i bs (length bs - 1)) }

val mk_plain: i:id{ ~(authId i) } -> l:plainLen -> pr:lbytes l
  -> Tot (let len = min l (max_TLSPlaintext_fragment_length + 1) in
         let pr' = fst (split pr len) in
         option (p:plain i len {pr' = ghost_repr #i #len p}))
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

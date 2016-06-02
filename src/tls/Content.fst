module Content // was TLSFragment

// Multiplexing protocol payloads into record-layer plaintext
// fragments, and defining their projection to application-level
// streams.

open FStar
open FStar.Seq
open FStar.SeqProperties

open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range
open DataStream


type fragment (i:id) =
    | CT_Alert     : alertDescription                           -> fragment i // could insist we get exactly 2 bytes
    | CT_Handshake : rg: frange i -> f: rbytes rg                -> fragment i // concrete
    | CT_CCS       :                                              fragment i // one-byte; never encrypted or decrypted
    | CT_Data      : rg: frange i -> f: DataStream.fragment i rg -> fragment i // abstract
// for TLS 1.3
//  | CT_EncryptedHandshake : rg: frange i -> f: Handshake.fragment i rg -> fragment i // abstract
//  | CT_EarlyData : rg: frange i -> f: DataStream.fragment i rg -> fragment i // abstract

// move to Seq?
val split: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a * a)
let split #a s =
  let last = Seq.length s - 1 in
  Seq.slice s 0 last, Seq.index s last

// Alert fragmentation is forbidden in TLS 1.3; as a slight deviation
// from the standard, we also forbid it in earlier version. 
// Anyway, this is internal to the Alert protocol.

// Ghost projection from low-level multiplexed fragments to application-level deltas
// Some fragments won't parse; they are ignored in the projection. 
// We may prove that they are never written on authentic streams.
val project: i:id -> fs:seq (fragment i) -> Tot(seq (DataStream.delta i))
  (decreases %[Seq.length fs]) // not-quite-stuctural termination
#reset-options
let rec project i fs =
  if Seq.length fs = 0 then Seq.createEmpty
  else
      let fs, f = split #(fragment i) fs in
      let ds = project i fs in
      match f with
      | CT_Data rg d -> 
	let d : pre_fragment i = d in //A widening coercion as a proof hint, unpacking (d:fragment i (frange i)) to a pre_fragment i
	snoc ds (DataStream.Data d)   //so that it can be repackaged as a fragment i fragment_range
      | CT_Alert ad  -> snoc ds (DataStream.Alert ad)
      | _            -> ds  // other fragments are internal to TLS

// try out a few lemmas
// we may also need a projection that takes a low-level pos and yields a high-level pos

val project_ignores_Handshake: i:id -> s: seq (fragment i) {Seq.length s > 0 /\ is_CT_Handshake (Seq.index s (Seq.length s - 1))} -> 
  Lemma(project i s = project i (Seq.slice s 0 (Seq.length s - 1)))

let project_ignores_Handshake i s = ()


// --------------- parsing and formatting content types ---------------------

type contentType =
    | Change_cipher_spec
    | Alert
    | Handshake
    | Application_data

type contentType13 = ct: contentType { ct <> Change_cipher_spec }

val ctBytes: contentType -> Tot (lbytes 1)
let ctBytes ct =
    match ct with
    | Change_cipher_spec -> abyte 20z
    | Alert              -> abyte 21z
    | Handshake          -> abyte 22z
    | Application_data   -> abyte 23z

val parseCT: pinverse_t ctBytes
let parseCT b =
    match cbyte b with
    | 20z -> Correct Change_cipher_spec
    | 21z -> Correct Alert
    | 22z -> Correct Handshake
    | 23z -> Correct Application_data
    | _    -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_ct: x:_ -> Lemma
  (requires (True)) 
  (ensures lemma_inverse_g_f ctBytes parseCT x)
  [SMTPat (parseCT (ctBytes x))]
let inverse_ct x = ()

val pinverse_ct: x:_ -> Lemma
  (requires (True))
  (ensures (lemma_pinverse_f_g Seq.equal ctBytes parseCT x))
  [SMTPat (ctBytes (Correct._0 (parseCT x)))]
let pinverse_ct x = ()

let ctToString = function
    | Change_cipher_spec -> "CCS"
    | Alert              -> "Alert"
    | Handshake          -> "Handshake"
    | Application_data   -> "Data"


// --------------- conditional access to fragment representation ---------------------

let ccsBytes = abyte 1z

val ghost_repr: #i:id -> fragment i -> GTot bytes
let ghost_repr #i f =
  match f with
  // FIXME: without the #i, extraction crashes
  | CT_Data rg d      -> DataStream.ghost_repr #i d
  | CT_Handshake rg f -> f
  | CT_CCS            -> ccsBytes
  | CT_Alert ad       -> Alert.alertBytes ad

val repr: i:id{ ~(safeId i)} -> p:fragment i -> Tot (b:bytes {b = ghost_repr #i p})
let repr i f =
  match f with
  // FIXME: same thing
  | CT_Data rg d      -> DataStream.repr #i rg d
  | CT_Handshake rg f -> f
  | CT_CCS            -> ccsBytes
  | CT_Alert ad       -> Alert.alertBytes ad

let ct (i:id) (f:fragment i): contentType =
  match f with
  | CT_Data rg d      -> Application_data
  | CT_Handshake rg f -> Handshake
  | CT_CCS            -> Change_cipher_spec
  | CT_Alert ad       -> Alert

let rg (i:id) (f:fragment i): frange i =
  match f with
  | CT_Data rg _      -> rg
  | CT_Handshake rg _ -> rg
  | CT_CCS            -> point 1 
  | CT_Alert _        -> point 2

let ct_rg i f = ct i f, rg i f

// "plain interface" for conditional security (TODO restore details)

let fragmentRepr (#i:id) (ct:contentType) (rg:frange i) (b:rbytes rg) = 
  match ct with 
    | Change_cipher_spec -> b2t(op_Equality #bytes b ccsBytes)
    | Alert              -> rg = point 2 /\ is_Correct (Alert.parse b)
    | _                  -> True

val mk_fragment: i:id{ ~(authId i)} -> ct:contentType -> rg:frange i -> b:rbytes rg { fragmentRepr ct rg b } ->
  Tot (p:fragment i {b = ghost_repr p})
let mk_fragment i ct rg b =
    match ct with
    | Application_data   -> CT_Data      rg (DataStream.mk_fragment #i rg b)
    | Handshake          -> CT_Handshake rg b
    | Change_cipher_spec -> CT_CCS 
    | Alert              -> CT_Alert     (match Alert.parse b with | Correct ad -> ad)

(*
val mk_ct_rg: 
  i:id{ ~(authId i)} -> 
  ct:contentType -> 
  rg:frange i ->
  b:rbytes rg { fragmentRepr ct rg b } ->
  Lemma ((ct,rg) = ct_rg i (mk_fragment i ct rg b))
let mk_ct_rg i ct rg b = ()
*)

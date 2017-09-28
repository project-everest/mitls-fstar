module Content // was TLSFragment

// Multiplexing protocol payloads into record-layer plaintext
// fragments, and defining their projection to application-level
// streams.

open FStar
open FStar.Seq

open FStar.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range
open DataStream


// this description is detailed enough to compute the size of the plaintext and ciphertext
type fragment (i:id) =
  | CT_Alert    : rg:frange i {wider rg (point 2)} -> alertDescription -> fragment i
  | CT_Handshake: rg:frange i -> f:rbytes rg                           -> fragment i  // concrete for now
  | CT_CCS      : rg:frange i {wider rg (point 1)}                    -> fragment i
  | CT_Data     : rg:frange i -> f:DataStream.fragment i rg            -> fragment i // abstract
// for TLS 1.3
//  | CT_EncryptedHandshake: rg:frange i -> f:Handshake.fragment i rg  -> fragment i // abstract
//  | CT_EarlyData         : rg:frange i -> f:DataStream.fragment i rg -> fragment i // abstract

// move to Seq?
private val split: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a * a)
let split #a s =
  let last = Seq.length s - 1 in
  Seq.slice s 0 last, Seq.index s last

// Alert fragmentation is forbidden in TLS 1.3; as a slight deviation
// from the standard, we also forbid it in earlier version. 
// Anyway, this is internal to the Alert protocol.

// Ghost projection from low-level multiplexed fragments to application-level deltas
// Some fragments won't parse; they are ignored in the projection. 
// We may prove that they are never written on authentic streams.
val project: i:id -> fs:seq (fragment i) -> Tot (seq (DataStream.delta i))
  (decreases %[Seq.length fs]) // not-quite-stuctural termination
#reset-options
let rec project i fs =
  if Seq.length fs = 0 then Seq.createEmpty
  else
    let fs, f = split #(fragment i) fs in
    let ds = project i fs in
    match f with
    | CT_Data rg d ->
      let d:pre_fragment i = d in //A widening coercion as a proof hint, unpacking (d:fragment i (frange i)) to a pre_fragment i
      snoc ds (DataStream.Data d)   //so that it can be repackaged as a fragment i fragment_range
    | CT_Alert rg ad -> snoc ds (DataStream.Alert ad)
    | _ -> ds	 // other fragments are internal to TLS

// try out a few lemmas
// we may also need a projection that takes a low-level pos and yields a high-level pos

val project_ignores_Handshake: i:id -> s:seq (fragment i) {Seq.length s > 0 /\ CT_Handshake? (Seq.index s (Seq.length s - 1))} ->
  Lemma(project i s == project i (Seq.slice s 0 (Seq.length s - 1)))
let project_ignores_Handshake i s = ()


// --------------- parsing and formatting content types ---------------------

type contentType =
  | Change_cipher_spec
  | Alert
  | Handshake
  | Application_data

type contentType13 = ct: contentType { ct <> Change_cipher_spec }

val ctBytes: contentType -> Tot (lbytes 1)
let ctBytes = function
  | Change_cipher_spec -> abyte 20z
  | Alert	       -> abyte 21z
  | Handshake	       -> abyte 22z
  | Application_data   -> abyte 23z

val parseCT: pinverse_t ctBytes
let parseCT b =
  match b.[0ul] with
  | 20z -> Correct Change_cipher_spec
  | 21z -> Correct Alert
  | 22z -> Correct Handshake
  | 23z -> Correct Application_data
  | _	-> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val inverse_ct: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f ctBytes parseCT x)
  [SMTPat (parseCT (ctBytes x))]
let inverse_ct x = ()

val pinverse_ct: x:_ -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g Bytes.equal ctBytes parseCT x))
  [SMTPat (ctBytes (Correct?._0 (parseCT x)))]
let pinverse_ct x = ()

let ctToString = function
  | Change_cipher_spec -> "CCS"
  | Alert	       -> "Alert"
  | Handshake	       -> "Handshake"
  | Application_data   -> "Data"


// --------------- conditional access to fragment representation ---------------------

val rg: i:id -> fragment i -> Tot (frange i)
let rg i = function
  | CT_Data rg _      -> rg
  | CT_Handshake rg _ -> rg
  | CT_CCS rg         -> rg
  | CT_Alert rg _     -> rg

val ct: i:id -> fragment i -> Tot contentType
let ct i = function
  | CT_Data _ _      -> Application_data
  | CT_Handshake _ _ -> Handshake
  | CT_CCS _         -> Change_cipher_spec
  | CT_Alert _ _     -> Alert

let ct_rg i f = ct i f, rg i f

let is_stream i = ID13? i

let is_stlhae i = ID12? i && AEAD? (aeAlg_of_id i)

val cipherLen: i:id -> fragment i -> Tot (l:nat{Range.valid_clen i l})
let cipherLen i f =
  let r = rg i f in
  if PlaintextID? i then
    fst r
  else if is_stream i then
    // sufficient to ensure the cipher can be processed without length errors
    let alg  = AEAD?._0 (aeAlg_of_id i) in
    let ltag = CoreCrypto.aeadTagSize alg in
    snd r + 1 + ltag
  else if is_stlhae i then
    Range.targetLength i r
  else
    admit () // FIXME: after generalizing StLHAE beyond AEAD ciphers

type encrypted (#i:id) (f:fragment i) = lbytes (cipherLen i f)
type decrypted (i:id) = contentType * (b:bytes{ Range.valid_clen i (length b) })

let ccsBytes = abyte 1z

val ghost_repr: #i:id -> f:fragment i -> GTot (rbytes (rg i f))
let ghost_repr #i = function
  // FIXME: without the #i, extraction crashes
  | CT_Data _ d      -> DataStream.ghost_repr #i d
  | CT_Handshake _ f -> f
  | CT_CCS rg        -> ccsBytes
  | CT_Alert _ ad    -> Alert.alertBytes ad

val repr: i:id{ ~(safeId i) } -> p:fragment i -> Tot (b:bytes {b = ghost_repr #i p})
let repr i = function
  // FIXME: same thing
  | CT_Data rg d     -> DataStream.repr #i rg d
  | CT_Handshake _ f -> f
  | CT_CCS _         -> ccsBytes
  | CT_Alert _ ad    -> Alert.alertBytes ad

// "plain interface" for conditional security (TODO restore details)

let fragmentRepr (#i:id) (ct:contentType) (rg:frange i) (b:rbytes rg) = 
  match ct with 
  | Change_cipher_spec -> wider rg (point 1) /\ b = ccsBytes
  | Alert              -> wider rg (point 2) /\ length b = 2 /\ Correct? (Alert.parse b)
  | _                  -> True

val mk_fragment: i:id{ ~(authId i) } -> ct:contentType -> rg:frange i -> b:rbytes rg { fragmentRepr ct rg b } ->
  Tot (p:fragment i {b = ghost_repr p})
let mk_fragment i ct rg b =
  match ct with
  | Application_data   -> CT_Data      rg (DataStream.mk_fragment #i rg b)
  | Handshake          -> CT_Handshake rg b
  | Change_cipher_spec -> CT_CCS       rg
  | Alert              -> CT_Alert     rg (match Alert.parse b with | Correct ad -> ad)

val mk_ct_rg: i:id{ ~(authId i) } -> ct:contentType -> rg:frange i -> b:rbytes rg { fragmentRepr ct rg b } ->
  Lemma (requires True) (ensures (ct,rg) = ct_rg i (mk_fragment i ct rg b))
	[SMTPat (ct_rg i (mk_fragment i ct rg b))]
let mk_ct_rg i ct rg b = ()

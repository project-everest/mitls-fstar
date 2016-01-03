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
    | CT_Alert     : rg: frange i -> f: rbytes rg -> fragment i // could insist we get exactly 2n bytes
    | CT_Handshake : rg: frange i -> f: rbytes rg -> fragment i // concrete
    | CT_CCS       : fragment i // empty; never encrypted or decrypted
    | CT_Data      : rg: frange i -> f: DataStream.fragment i rg -> fragment i // abstract
// for TLS 1.3
//  | CT_EncryptedHandshake : rg: frange i -> f: Handshake.fragment i rg -> fragment i // abstract
//  | CT_EarlyData : rg: frange i -> f: DataStream.fragment i rg -> fragment i // abstract

let ct_alert (i:id) (ad:alertDescription) : fragment i = CT_Alert (2,2) (Alert.alertBytes ad)

// consider replacing (rg,f) with just bytes for HS and Alert
// consider being more concrete, e.g. CT_Alert: alertDescription -> fragment i


// move to Seq?
val split: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a * a)
let split s =
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
let rec project i fs =
  if Seq.length fs = 0 then Seq.createEmpty
  else
      let fs, f = split #(fragment i) fs in
      let ds = project i fs in
      (match f with
      | CT_Data (rg: frange i) d -> cut(Wider fragment_range rg); snoc ds (DataStream.Data d)
      | CT_Alert rg alf -> // alert parsing may fail, or return several deltas
          if length alf = 2 then 
          (match Alert.parse alf with
          | Correct ad -> snoc ds (DataStream.Alert ad)
          | Error _    -> ds) // ill-formed alert contents are ignored
          else ds            // ill-formed alert packets are ignored
      | _              -> ds) // other fragments are internal to TLS

// try out a few lemmas
// we may also need a projection that takes a low-level pos and yields a high-level pos

val project_ignores_Handshake: i:id -> s: seq (fragment i) {Seq.length s > 0 /\ is_CT_Handshake (Seq.index s (Seq.length s - 1))} -> 
  Lemma(project i s = project i (Seq.slice s 0 (Seq.length s - 1)))

let project_ignores_Handshake i s = ()


// --------------- conditional access to fragment representation ---------------------

val ghost_repr: #i:id -> fragment i -> GTot bytes
let ghost_repr i f =
  match f with
  | CT_Data rg d      -> DataStream.ghost_repr d
  | CT_Handshake rg f -> f
  | CT_CCS            -> empty_bytes
  | CT_Alert rg f     -> f

val repr: i:id{ ~(safeId i)} -> p:fragment i -> Tot (b:bytes {b = ghost_repr #i p})
let repr i f =
  match f with
  | CT_Data rg d      -> DataStream.repr rg d
  | CT_Handshake rg f -> f
  | CT_CCS            -> empty_bytes
  | CT_Alert rg f     -> f

let ct_rg (i:id) (f:fragment i) : _ * frange i =
  match f with
  | CT_Data rg d      -> Application_data, rg
  | CT_Handshake rg f -> TLSConstants.Handshake, rg
  | CT_CCS            -> Change_cipher_spec, zero
  | CT_Alert rg f     -> TLSConstants.Alert, rg

let rg (i:id) (f:fragment i) : frange i =
  match f with
  | CT_Data rg d      -> rg
  | CT_Handshake rg f -> rg
  | CT_CCS            -> zero
  | CT_Alert rg f     -> rg


// "plain interface" for conditional security (TODO restore details)

val mk_fragment: i:id{ ~(authId i)} -> ct:ContentType -> rg:frange i ->
  b:rbytes rg { ct = Change_cipher_spec ==> rg == zero }->
  Tot (p:fragment i {b = ghost_repr p})
let mk_fragment i ct rg b =
    match ct with
    | Application_data   -> CT_Data      rg (DataStream.mk_fragment i rg b)
    | Handshake          -> CT_Handshake rg b
    | Change_cipher_spec -> cut(Eq b empty_bytes);CT_CCS  //* rediscuss
    | TLSConstants.Alert -> CT_Alert     rg b

val mk_ct_rg: 
  i:id{ ~(authId i)} -> 
  ct:ContentType -> 
  rg:frange i ->
  b:rbytes rg { ct = Change_cipher_spec ==> rg = zero } ->
  Lemma ((ct,rg) = ct_rg i (mk_fragment i ct rg b))
let mk_ct_rg i ct rg b = ()


(*
val reprFragment: i:id { not (SafeId i) } -> ct:contentType -> rg:range -> fragment i ct rg
let reprFragment i:id (ct:ContentType) (rg:range) frag =
    match frag with
    | FHandshake(f) -> HSFragment.fragmentRepr i rg f
    | FCCS(f)       -> HSFragment.fragmentRepr i rg f
    | FAlert(f)     -> HSFragment.fragmentRepr i rg f
    | FAppData(f)   -> AppFragment.repr i rg f
*)





(* later, we may be more precise and also account for hanshake traffic protection

type history = {
  handshake: HSFragment.stream; //CF Handshake.stream;
  ccs:       HSFragment.stream; //CF Handshake.stream;
  alert:     HSFragment.stream; //CF Alert.stream;
  appdata:   DataStream.stream //CF AppData.stream;
}

let emptyHistory e =
    let i = mk_id e in
    let es = HSFragment.init i in
    let ehApp = DataStream.init e in
    { handshake = es;
      ccs = es;
      alert = es;
      appdata = ehApp}

let handshakeHistory (e:epoch) h = h.handshake
let ccsHistory (e:epoch) h = h.ccs
let alertHistory (e:epoch) h = h.alert

let hsPlainToRecordPlain    (e:epoch) (h:history) (r:range) (f:HSFragment.plain) = FHandshake(f)
let ccsPlainToRecordPlain   (e:epoch) (h:history) (r:range) (f:HSFragment.plain) = FCCS(f)
let alertPlainToRecordPlain (e:epoch) (h:history) (r:range) (f:HSFragment.plain) = FAlert(f)
let appPlainToRecordPlain   (e:epoch) (h:history) (r:range) (f:AppFragment.plain)= FAppData(f)

let recordPlainToHSPlain    (e:epoch) (h:history) (r:range) ff =
    match ff with
    | FHandshake(f) -> f
    | FCCS(_)
    | FAlert(_)
    | FAppData(_)   -> unreachable "[RecordPlainToHSPlain] invoked on an invalid fragment"
let recordPlainToCCSPlain    (e:epoch) (h:history) (r:range) ff =
    match ff with
    | FCCS(f)       -> f
    | FHandshake(_)
    | FAlert(_)
    | FAppData(_)   -> unreachable "[RecordPlainToCCSPlain] invoked on an invalid fragment"
let recordPlainToAlertPlain    (e:epoch) (h:history) (r:range) ff =
    match ff with
    | FAlert(f)     -> f
    | FHandshake(_)
    | FCCS(_)
    | FAppData(_)   -> unreachable "[RecordPlainToAlertPlain] invoked on an invalid fragment"
let recordPlainToAppPlain    (e:epoch) (h:history) (r:range) ff =
    match ff with
    | FAppData(f)   -> f
    | FHandshake(_)
    | FCCS(_)
    | FAlert(_)     -> unreachable "[RecordPlainToAppPlain] invoked on an invalid fragment"

let extendHistory (e:epoch) ct ss r frag =
  let i = mk_id e in
  match ct,frag with
    | Handshake,FHandshake(f)      -> let s' = HSFragment.extend i ss.handshake r f in
                                      {ss with handshake = s'}
    | Alert,FAlert(f)              -> let s' = HSFragment.extend i ss.alert r f in
                                      {ss with alert = s'}
    | Change_cipher_spec,FCCS(f)   -> let s' = HSFragment.extend i ss.ccs r f in
                                      {ss  with ccs = s'}
    | Application_data,FAppData(f) -> let d,s' = AppFragment.delta e ss.appdata r f in
                                      {ss with appdata = s'}
    | _,_                          -> unexpected "[extendHistory] invoked on an invalid contenttype/fragment"
    //CF unreachable too, but we'd need to list the other 12 cases to prove it.

let makeExtPad i ct r frag =
    match ct,frag with
    | Handshake,FHandshake(f)      -> let f = HSFragment.makeExtPad  i r f in FHandshake(f)
    | Alert,FAlert(f)              -> let f = HSFragment.makeExtPad  i r f in FAlert(f)
    | Change_cipher_spec,FCCS(f)   -> let f = HSFragment.makeExtPad  i r f in FCCS(f)
    | Application_data,FAppData(f) -> let f = AppFragment.makeExtPad i r f in FAppData(f)
    | _,_                          -> unexpected "[makeExtPad] invoked on an invalid contenttype/fragment"

let parseExtPad i ct r frag : Result (fragment) =
    match ct,frag with
    | Handshake,FHandshake(f) ->
        (match HSFragment.parseExtPad i r f with
        | Error(x) -> Error(x)
        | Correct(f) -> Correct (FHandshake(f)))
    | Alert,FAlert(f) ->
        (match HSFragment.parseExtPad i r f with
        | Error(x) -> Error(x)
        | Correct(f) -> Correct (FAlert(f)))
    | Change_cipher_spec,FCCS(f) ->
        (match HSFragment.parseExtPad i r f with
        | Error(x) -> Error(x)
        | Correct(f) -> Correct (FCCS(f)))
    | Application_data,FAppData(f) ->
        (match AppFragment.parseExtPad i r f with
        | Error(x) -> Error(x)
        | Correct(f) -> Correct (FAppData(f)))
    | _,_ -> unexpected "[parseExtPad] invoked on an invalid contenttype/fragment"

#if ideal
let widen i ct r0 f0 =
    let r1 = rangeClass i r0 in
    match ct,f0 with
    | Handshake,FHandshake(f)      -> let f1 = HSFragment.widen i r0 r1 f in
                                      FHandshake(f1)
    | Alert,FAlert(f)              -> let f1 = HSFragment.widen i r0 r1 f in
                                      FAlert(f1)
    | Change_cipher_spec,FCCS(f)   -> let f1 = HSFragment.widen i r0 r1 f in
                                      FCCS(f1)
    | Application_data,FAppData(f) -> let f1 = AppFragment.widen i r0 f in
                                      FAppData(f1)
    | _,_                          -> unexpected "[widen] invoked on an invalid contenttype/fragment"
    //CF unreachable too
#endif
*)

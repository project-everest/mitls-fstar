module Model.AE
include Model.AEAD

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module CL = C.Loops
module MU = Model.Utils
module SC = Spec.AEAD
module F = Flags
module E = EverCrypt
module ES = EverCrypt.Specs
module U32 = FStar.UInt32

inline_for_extraction
let iv_len = 12ul

inline_for_extraction
noextract
let random_sample
  (len: U32.t)
  (out: B.buffer SC.uint8 { B.len out == len })
: HST.Stack unit
  (requires (fun h -> B.live h out))
  (ensures (fun h _ h' -> B.modifies (B.loc_buffer out) h h'))
= let h = HST.get () in
  assume (ES.random_sample_pre h);
  E.random_sample len out

inline_for_extraction
noextract
let iv_length = 12

let rec regenerate_iv
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (out: B.buffer SC.uint8)
: HST.Stack (s: SC.iv a { Seq.length s == iv_length })
  (requires (fun h ->
    B.loc_disjoint (B.loc_buffer out) (footprint s) /\
    B.live h out /\
    B.len out == iv_len /\
    invariant h s /\
    F.model == true
  ))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer out) h h' /\
    res == B.as_seq h' out /\
    (F.ideal_iv == true ==> fresh_iv h' s res)
  ))
= let h0 = HST.get () in
  random_sample iv_len out;
  let iv = MU.get_buffer out iv_len in
  let h1 = HST.get () in
  frame_invariant h0 s (B.loc_buffer out) h1;
  if F.ideal_iv
  then begin
    let cond = is_fresh_iv s iv in
    let h' = HST.get () in
    frame_fresh_iv h1 s iv B.loc_none h' ;
    if cond
    then iv
    else begin
      frame_invariant h1 s B.loc_none h' ;
      regenerate_iv s out
    end
  end else iv

let generate_iv
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
: HST.Stack (s: SC.iv a { Seq.length s == iv_length })
  (requires (fun h ->
    F.model == true /\
    invariant h s
  ))
  (ensures (fun h iv h' ->
    B.modifies B.loc_none h h' /\
    (F.ideal_iv == true ==> fresh_iv h s iv)
  ))
= let h = HST.get () in
  invariant_loc_in_footprint h s;
  HST.push_frame ();
  let b = B.alloca (Lib.IntTypes.mk_int 0 <: SC.uint8) iv_len in
  let h1 = HST.get () in
  frame_invariant h s B.loc_none h1 ;
  let res = regenerate_iv s b in
  let h2 = HST.get () in
  frame_fresh_iv h s res B.loc_none h2;
  HST.pop_frame ();
  res

val encrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (plain: SC.plain a)
: HST.Stack (s: Seq.seq SC.uint8 { Seq.length s == iv_length + Seq.length plain + SC.tag_length a }) 
  (requires (fun h ->
    Flags.model == true /\
    invariant h s /\
    phi plain
  ))
  (ensures (fun h cipher h' -> 
    B.modifies (footprint s) h h' /\
    Seq.length cipher <= iv_length + SC.max_length a + SC.tag_length a /\ (
    let iv = Seq.slice cipher 0 iv_length in
    invariant h' s /\
    (Flags.ideal_AEAD == false ==>
      SC.encrypt (state_kv s) iv Seq.empty plain == Seq.slice cipher iv_length (Seq.length cipher)
  ))))

let encrypt
  #a #phi s plain
= let h = HST.get () in
  let iv = generate_iv s in
  let h1 = HST.get () in
  frame_invariant h s B.loc_none h1;
  frame_fresh_iv h s iv B.loc_none h1;
  let cipher = encrypt s iv plain in
  let res = Seq.append iv cipher in
  assert (Seq.slice res 0 iv_length `Seq.equal` iv);
  assert (Seq.slice res iv_length (Seq.length res) `Seq.equal` cipher);
  res

val decrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (cipher: SC.cipher a { Seq.length cipher >= iv_length + SC.tag_length a /\ Seq.length cipher <= iv_length + SC.max_length a + SC.tag_length a })
: HST.Stack (option (plain: Seq.seq SC.uint8 { Seq.length cipher == iv_length + Seq.length plain + SC.tag_length a }))
  (requires (fun h ->
    Flags.model == true /\
    invariant h s
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint s) h h' /\ (
    let cipher' = Seq.slice cipher iv_length (Seq.length cipher) in
    let iv = Seq.slice cipher 0 iv_length in
    (Flags.ideal_AEAD == false ==> (
      SC.decrypt (state_kv s) iv Seq.empty cipher' == res
    )) /\
    invariant h' s /\
    begin match res with
    | None -> True
    | Some plain ->
      (Flags.ideal_AEAD == true ==> phi plain)
    end
  )))

let decrypt
  #a #phi s cipher
= let iv' = Seq.slice cipher 0 iv_length in
  let cipher' = Seq.slice cipher iv_length (Seq.length cipher) in
  decrypt s iv' cipher'

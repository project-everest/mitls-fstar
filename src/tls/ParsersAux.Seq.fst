module ParsersAux.Seq

module LP = LowParse.Low.Base
module Seq = FStar.Seq
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer

let seq_starts_with (#t: Type) (slong sshort: Seq.seq t) : GTot Type0 =
  Seq.length sshort <= Seq.length slong /\
  Seq.slice slong 0 (Seq.length sshort) `Seq.equal` sshort

let seq_starts_with_trans (#t: Type) (s1 s2 s3: Seq.seq t) : Lemma
  (requires (s1 `seq_starts_with` s2 /\ s2 `seq_starts_with` s3))
  (ensures (s1 `seq_starts_with` s3))
= ()

let seq_starts_with_append_l_intro (#t: Type) (s1 s2: Seq.seq t) : Lemma
  ((s1 `Seq.append` s2) `seq_starts_with` s1)
= ()

let seq_starts_with_append_r_elim (#t: Type) (s s1 s2: Seq.seq t) : Lemma
  (requires (s `seq_starts_with` (s1 `Seq.append` s2)))
  (ensures (
    s `seq_starts_with` s1 /\
    Seq.slice s (Seq.length s1) (Seq.length s) `seq_starts_with` s2
  ))
  [SMTPat (s `seq_starts_with` (s1 `Seq.append` s2))]
= let s3 = Seq.slice s (Seq.length s1 + Seq.length s2) (Seq.length s) in
  assert (s `Seq.equal` (s1 `Seq.append` s2 `Seq.append` s3))

inline_for_extraction
noextract
let jump_serializer
  (#k: _)
  (#t: _)
  (#p: LP.parser k t)
  (s: LP.serializer p { k.LP.parser_kind_subkind == Some LP.ParserStrong })
  (j: LP.jumper p)
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased t)
: HST.Stack U32.t
  (requires (fun h ->
    let sq = LP.serialize s (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    LP.bytes_of_slice_from h sl pos `seq_starts_with` sq
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + Seq.length (LP.serialize s (Ghost.reveal x)) == U32.v res
  ))
= let h = HST.get () in
  let gsq = Ghost.hide (LP.serialize s (Ghost.reveal x)) in
  let glen = Ghost.hide (Seq.length (Ghost.reveal gsq)) in
  let gpos' = Ghost.hide (pos `U32.add` U32.uint_to_t (Ghost.reveal glen)) in
  assert (LP.bytes_of_slice_from_to h sl pos (Ghost.reveal gpos') == Seq.slice (LP.bytes_of_slice_from h sl pos) 0 (Seq.length (LP.serialize s (Ghost.reveal x))));
  LP.serialize_valid_exact s h sl (Ghost.reveal x) pos (Ghost.reveal gpos');
  LP.valid_exact_valid p h sl pos (Ghost.reveal gpos');
  j sl pos
